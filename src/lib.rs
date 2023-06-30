use halo2_base::gates::flex_gate::FlexGateConfig;
use halo2_base::gates::GateInstructions;
use halo2_base::halo2_proofs::halo2curves::bn256::{Bn256, Fr, G1Affine};
use halo2_base::halo2_proofs::plonk::{Circuit, ConstraintSystem};
use halo2_base::halo2_proofs::poly::{commitment::Params, kzg::commitment::ParamsKZG};
use halo2_base::halo2_proofs::{circuit::Layouter, plonk::Error};
use halo2_base::halo2_proofs::{
    circuit::{floor_planner::V1, Cell, Value},
    dev::{CircuitCost, FailureLocation, MockProver, VerifyFailure},
    plonk::{Any, Column, Instance, ProvingKey, VerifyingKey},
};
use halo2_base::utils::fe_to_bigint;
use halo2_base::{gates::range::RangeConfig, utils::PrimeField, Context};
use halo2_base::{gates::range::RangeStrategy::Vertical, SKIP_FIRST_PASS};
use halo2_base::{AssignedValue, QuantumCell};
use halo2_ecc::ecc::{EcPoint, EccChip};
use halo2_ecc::fields::fp::FpConfig;
use halo2_ecc::fields::FieldChip;
use num_bigint::BigInt;
use rand::rngs::OsRng;
use rand::Rng;

#[derive(Debug, Clone)]
pub struct Point<F: PrimeField> {
    x: F,
    y: F,
}

#[derive(Debug, Clone)]
pub struct AssignedPoint<'a, F: PrimeField> {
    x: AssignedValue<'a, F>,
    y: AssignedValue<'a, F>,
}

#[derive(Debug, Clone)]
pub struct NativeECConfig<F: PrimeField> {
    gate: FlexGateConfig<F>,
    param_a: u64,
    param_d: u64,
    generator: Point<F>,
}

impl<F: PrimeField> NativeECConfig<F> {
    // const PARAM_A: u64 = 168700;
    // const PARAM_D: u64 = 168696;
    pub fn new(gate: FlexGateConfig<F>, param_a: u64, param_d: u64, generator: Point<F>) -> Self {
        Self {
            gate,
            param_a,
            param_d,
            generator,
        }
    }

    pub fn load_generator<'a>(&self, ctx: &mut Context<F>) -> AssignedPoint<'a, F> {
        let x = self.gate.load_constant(ctx, self.generator.x);
        let y = self.gate.load_constant(ctx, self.generator.y);
        AssignedPoint { x, y }
    }

    pub fn load_point_unchecked<'a>(
        &self,
        ctx: &mut Context<F>,
        point: &Point<F>,
    ) -> AssignedPoint<'a, F> {
        let x = self.gate.load_witness(ctx, Value::known(point.x));
        let y = self.gate.load_witness(ctx, Value::known(point.y));
        AssignedPoint { x, y }
    }

    pub fn load_point_checked<'a>(
        &self,
        ctx: &mut Context<F>,
        point: &Point<F>,
    ) -> AssignedPoint<'a, F> {
        let point = self.load_point_unchecked(ctx, point);
        let x2 = self.gate.mul(
            ctx,
            QuantumCell::Existing(&point.x),
            QuantumCell::Existing(&point.x),
        );
        let y2 = self.gate.mul(
            ctx,
            QuantumCell::Existing(&point.y),
            QuantumCell::Existing(&point.y),
        );
        // a*x2 + y2 === 1 + d*x2*y2;
        let left_term = self.gate.mul_add(
            ctx,
            QuantumCell::Constant(F::from(self.param_a)),
            QuantumCell::Existing(&x2),
            QuantumCell::Existing(&y2),
        );
        let right_term = {
            let muled = self
                .gate
                .mul(ctx, QuantumCell::Existing(&x2), QuantumCell::Existing(&y2));
            self.gate.mul_add(
                ctx,
                QuantumCell::Existing(&muled),
                QuantumCell::Constant(F::from(self.param_d)),
                QuantumCell::Constant(F::one()),
            )
        };
        self.gate.assert_equal(
            ctx,
            QuantumCell::Existing(&left_term),
            QuantumCell::Existing(&right_term),
        );
        point
    }

    pub fn add(
        &self,
        ctx: &mut Context<F>,
        point1: &AssignedPoint<F>,
        point2: &AssignedPoint<F>,
    ) -> AssignedPoint<F> {
        let beta = self.gate.mul(
            ctx,
            QuantumCell::Existing(&point1.x),
            QuantumCell::Existing(&point2.y),
        );
        let gamma = self.gate.mul(
            ctx,
            QuantumCell::Existing(&point1.y),
            QuantumCell::Existing(&point2.x),
        );
        let delta = {
            let factor1 = self.gate.mul_add(
                ctx,
                QuantumCell::Constant(-F::from(self.param_a)),
                QuantumCell::Existing(&point1.x),
                QuantumCell::Existing(&point1.y),
            );
            let factor2 = self.gate.add(
                ctx,
                QuantumCell::Existing(&point2.x),
                QuantumCell::Existing(&point2.y),
            );
            self.gate.mul(
                ctx,
                QuantumCell::Existing(&factor1),
                QuantumCell::Existing(&factor2),
            )
        };
        let tau = self.gate.mul(
            ctx,
            QuantumCell::Existing(&beta),
            QuantumCell::Existing(&gamma),
        );
        let beta_gamma_sum = self.gate.add(
            ctx,
            QuantumCell::Existing(&beta),
            QuantumCell::Existing(&gamma),
        );
        let one_d_tau1 = self.gate.mul_add(
            ctx,
            QuantumCell::Constant(F::from(self.param_d)),
            QuantumCell::Existing(&tau),
            QuantumCell::Constant(F::one()),
        );
        let new_x = {
            let inv = one_d_tau1.value().map(|v| v.invert().unwrap());
            let val = beta_gamma_sum.value().zip(inv).map(|(a, b)| *a * b);
            self.gate.load_witness(ctx, val)
        };
        {
            let mul = self.gate.mul(
                ctx,
                QuantumCell::Existing(&one_d_tau1),
                QuantumCell::Existing(&new_x),
            );
            self.gate.assert_equal(
                ctx,
                QuantumCell::Existing(&mul),
                QuantumCell::Existing(&beta_gamma_sum),
            );
        }
        let delta_beta_gamma = {
            let term1 = self.gate.mul_add(
                ctx,
                QuantumCell::Existing(&beta),
                QuantumCell::Constant(F::from(self.param_a)),
                QuantumCell::Existing(&delta),
            );
            self.gate.sub(
                ctx,
                QuantumCell::Existing(&term1),
                QuantumCell::Existing(&gamma),
            )
        };
        let one_d_tau2 = {
            let muled = self.gate.mul(
                ctx,
                QuantumCell::Constant(F::from(self.param_d)),
                QuantumCell::Existing(&tau),
            );
            self.gate.sub(
                ctx,
                QuantumCell::Constant(F::one()),
                QuantumCell::Existing(&muled),
            )
        };
        let new_y = {
            let inv = one_d_tau2.value().map(|v| v.invert().unwrap());
            let val = delta_beta_gamma.value().zip(inv).map(|(a, b)| *a * b);
            self.gate.load_witness(ctx, val)
        };
        {
            let mul = self.gate.mul(
                ctx,
                QuantumCell::Existing(&one_d_tau2),
                QuantumCell::Existing(&new_y),
            );
            self.gate.assert_equal(
                ctx,
                QuantumCell::Existing(&mul),
                QuantumCell::Existing(&delta_beta_gamma),
            );
        }
        AssignedPoint { x: new_x, y: new_y }
    }

    pub fn double(&self, ctx: &mut Context<F>, point: &AssignedPoint<F>) -> AssignedPoint<F> {
        self.add(ctx, point, point)
    }

    pub fn select_point<'a>(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedPoint<'a, F>,
        b: &AssignedPoint<'a, F>,
        sel: &AssignedValue<'a, F>,
    ) -> AssignedPoint<'a, F> {
        let x = self.gate.select(
            ctx,
            QuantumCell::Existing(&a.x),
            QuantumCell::Existing(&b.x),
            QuantumCell::Existing(&sel),
        );
        let y = self.gate.select(
            ctx,
            QuantumCell::Existing(&a.y),
            QuantumCell::Existing(&b.y),
            QuantumCell::Existing(&sel),
        );
        AssignedPoint { x, y }
    }

    pub fn scalar_mul<'a>(
        &'a self,
        ctx: &mut Context<F>,
        point: &AssignedPoint<'a, F>,
        scalar: &AssignedValue<'a, F>,
    ) -> AssignedPoint<'a, F> {
        let gate = &self.gate;
        let scalar_bits = gate.num_to_bits(ctx, scalar, F::NUM_BITS as usize);
        let mut out = self.load_generator(ctx);
        let mut doubled: AssignedPoint<F> = point.clone();
        for bit in scalar_bits.into_iter() {
            let added = self.add(ctx, &out, &doubled);
            out = self.select_point(ctx, &added, &out, &bit);
            doubled = self.double(ctx, &doubled);
        }
        out
    }
}