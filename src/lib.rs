use std::ops::Add;

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
use halo2_base::utils::{fe_to_bigint, fe_to_biguint};
use halo2_base::{gates::range::RangeConfig, utils::PrimeField, Context};
use halo2_base::{gates::range::RangeStrategy::Vertical, SKIP_FIRST_PASS};
use halo2_base::{AssignedValue, QuantumCell};
use halo2_ecc::ecc::{EcPoint, EccChip};
use halo2_ecc::fields::fp::FpConfig;
use halo2_ecc::fields::FieldChip;
use num_bigint::BigInt;
use rand::rngs::OsRng;
use rand::Rng;
use std::ops::Mul;

pub(crate) const PARAM_A: u64 = 168700;
pub(crate) const PARAM_D: u64 = 168696;
pub(crate) const BASE_POINT_X: &'static str =
    "5299619240641551281634865583518297030282874472190772894086521144482721001553";
pub(crate) const BASE_POINT_Y: &'static str =
    "16950150798460657717958625567821834550301663161624707787222815936182638968203";

#[derive(Debug, Clone)]
pub struct Point<F: PrimeField> {
    x: F,
    y: F,
}

impl<F: PrimeField> Add<Self> for Point<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let beta = self.x * rhs.y;
        let gamma = self.y * rhs.x;
        let delta = (-F::from(PARAM_A) * self.x + self.y) * (rhs.x + rhs.y);
        let tau = beta * gamma;
        let new_x_denom = (F::from(1) + F::from(PARAM_D) * tau).invert().unwrap();
        let new_x = (beta + gamma) * new_x_denom;
        let new_y_denom = (F::from(1) - F::from(PARAM_D) * tau).invert().unwrap();
        let new_y = (delta + F::from(PARAM_A) * beta - gamma) * new_y_denom;
        Point::new(new_x, new_y)
    }
}

impl<F: PrimeField> Mul<F> for Point<F> {
    type Output = Self;

    fn mul(self, rhs: F) -> Self::Output {
        let mut out = Point::new(F::zero(), F::zero());
        let mut doubled = self.clone();
        let scalar_big = fe_to_biguint(&rhs);
        let scalar_bytes = scalar_big.to_bytes_le();
        let num_bits = scalar_big.bits();
        for i in 0..num_bits {
            if scalar_bytes[i as usize / 8] & (1 << (i % 8)) != 0 {
                out = out + doubled.clone();
            }
            doubled = doubled.clone() + doubled;
        }
        // for bit in rhs.to_().as_ref().iter().rev() {
        //     if bit {
        //         out = out + doubled.clone();
        //     }
        //     doubled = doubled + doubled;
        // }
        out
    }
}

impl<F: PrimeField> Point<F> {
    pub fn new(x: F, y: F) -> Self {
        Self { x, y }
    }

    pub fn base_point() -> Self {
        Self::new(
            F::from_str_vartime(BASE_POINT_X).unwrap(),
            F::from_str_vartime(BASE_POINT_Y).unwrap(),
        )
    }
}

#[derive(Debug, Clone)]
pub struct AssignedPoint<'a, F: PrimeField> {
    x: AssignedValue<'a, F>,
    y: AssignedValue<'a, F>,
}

#[derive(Debug, Clone)]
pub struct NativeECConfig<F: PrimeField> {
    pub gate: FlexGateConfig<F>,
}

impl<F: PrimeField> NativeECConfig<F> {
    // const PARAM_A: u64 = 168700;
    // const PARAM_D: u64 = 168696;
    pub fn configure(gate: FlexGateConfig<F>) -> Self {
        Self { gate }
    }

    pub fn load_base_point<'a>(&self, ctx: &mut Context<F>) -> AssignedPoint<'a, F> {
        let base_point = Point::base_point();
        let x = self.gate.load_constant(ctx, base_point.x);
        let y = self.gate.load_constant(ctx, base_point.y);
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
            QuantumCell::Constant(F::from(PARAM_A)),
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
                QuantumCell::Constant(F::from(PARAM_D)),
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
                QuantumCell::Constant(-F::from(PARAM_A)),
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
            QuantumCell::Constant(F::from(PARAM_D)),
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
                QuantumCell::Constant(F::from(PARAM_A)),
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
                QuantumCell::Constant(F::from(PARAM_D)),
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
        let mut out = self.load_base_point(ctx);
        let mut doubled: AssignedPoint<F> = point.clone();
        println!("scalar {:?}", scalar);
        for bit in scalar_bits.into_iter() {
            let added = self.add(ctx, &out, &doubled);
            out = self.select_point(ctx, &added, &out, &bit);
            // println!("bit {:?}", bit);
            // println!("out {:?}", out);
            // println!("added {:?}", added);
            doubled = self.double(ctx, &doubled);
        }
        out
    }

    pub fn is_equal<'a>(
        &self,
        ctx: &mut Context<F>,
        point_a: &AssignedPoint<'a, F>,
        point_b: &AssignedPoint<'a, F>,
    ) -> AssignedValue<'a, F> {
        let is_x_eq = self.gate.is_equal(
            ctx,
            QuantumCell::Existing(&point_a.x),
            QuantumCell::Existing(&point_b.x),
        );
        let is_y_eq = self.gate.is_equal(
            ctx,
            QuantumCell::Existing(&point_a.y),
            QuantumCell::Existing(&point_b.y),
        );
        let is_eq = self.gate.and(
            ctx,
            QuantumCell::Existing(&is_x_eq),
            QuantumCell::Existing(&is_y_eq),
        );
        is_eq
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use halo2_base::halo2_proofs::plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, ConstraintSystem,
    };
    use halo2_base::halo2_proofs::poly::commitment::{Params, ParamsProver, ParamsVerifier};
    use halo2_base::halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
    use halo2_base::halo2_proofs::poly::kzg::multiopen::{ProverGWC, VerifierGWC};
    use halo2_base::halo2_proofs::poly::kzg::strategy::SingleStrategy;
    use halo2_base::halo2_proofs::transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    };
    use halo2_base::halo2_proofs::{
        dev::{CircuitCost, FailureLocation, MockProver, VerifyFailure},
        halo2curves::bn256::{Bn256, Fr, G1Affine, G1},
        plonk::{Any, Circuit},
    };
    use halo2_base::{gates::range::RangeStrategy::Vertical, ContextParams, SKIP_FIRST_PASS};
    use halo2_proofs::circuit::SimpleFloorPlanner;
    use rand::rngs::OsRng;
    use std::marker::PhantomData;
    use std::{collections::HashSet, path::Path};

    #[derive(Debug, Clone)]
    pub struct TestCircuit1<F: PrimeField> {
        rand_a: F,
        rand_b: F,
        rand_c: F,
    }

    impl<F: PrimeField> Circuit<F> for TestCircuit1<F> {
        type Config = NativeECConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;
        fn without_witnesses(&self) -> Self {
            Self {
                rand_a: F::one(),
                rand_b: F::one(),
                rand_c: F::one(),
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let gate = FlexGateConfig::<F>::configure(
                meta,
                halo2_base::gates::flex_gate::GateStrategy::Vertical,
                &[Self::NUM_ADVICE],
                Self::NUM_FIXED,
                0,
                Self::K,
            );
            // let base_point = Point::base_point();
            // println!("base_point {:?}", base_point);
            NativeECConfig::configure(gate)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let mut first_pass = SKIP_FIRST_PASS;
            layouter.assign_region(
                || "regex",
                |region| {
                    if first_pass {
                        first_pass = false;
                        return Ok(());
                    }
                    let gate = config.gate.clone();
                    let mut aux = Context::new(
                        region,
                        ContextParams {
                            max_rows: gate.max_rows,
                            num_context_ids: 1,
                            fixed_columns: gate.constants.clone(),
                        },
                    );
                    let ctx = &mut aux;
                    let base_point = config.load_base_point(ctx);
                    let assigned_rand_a = config.gate.load_witness(ctx, Value::known(self.rand_a));
                    let assigned_point_a = config.scalar_mul(ctx, &base_point, &assigned_rand_a);
                    let assigned_rand_b = config.gate.load_witness(ctx, Value::known(self.rand_b));
                    let assigned_point_b = config.scalar_mul(ctx, &base_point, &assigned_rand_b);
                    let assigned_rand_c = config.gate.load_witness(ctx, Value::known(self.rand_c));
                    let assigned_point_c = config.scalar_mul(ctx, &base_point, &assigned_rand_c);
                    {
                        let added_ab = config.add(ctx, &assigned_point_a, &assigned_point_b);
                        let added_abc = config.add(ctx, &added_ab, &assigned_point_c);
                        let added_bc = config.add(ctx, &assigned_point_b, &assigned_point_c);
                        let added_bca = config.add(ctx, &assigned_point_a, &added_bc);
                        let is_eq = config.is_equal(ctx, &added_abc, &added_bca);
                        config.gate.assert_equal(
                            ctx,
                            QuantumCell::Constant(F::one()),
                            QuantumCell::Existing(&is_eq),
                        );
                    }
                    {
                        let added = config.add(ctx, &assigned_point_a, &assigned_point_a);
                        let doubled = config.double(ctx, &assigned_point_a);
                        // let added = config.add(ctx, &doubled, &assigned_point_a);
                        let is_eq = config.is_equal(ctx, &added, &doubled);
                        config.gate.assert_equal(
                            ctx,
                            QuantumCell::Constant(F::one()),
                            QuantumCell::Existing(&is_eq),
                        );
                    }
                    {
                        let added = config.add(ctx, &base_point, &base_point);
                        let is_eq = config.is_equal(ctx, &added, &base_point);
                        config.gate.assert_equal(
                            ctx,
                            QuantumCell::Constant(F::one()),
                            QuantumCell::Existing(&is_eq),
                        );
                    }
                    {
                        let three = config.gate.load_constant(ctx, F::from(3u64));
                        let three_muled = config.scalar_mul(ctx, &assigned_point_a, &three);
                        let doubled = config.double(ctx, &assigned_point_a);
                        let added = config.add(ctx, &doubled, &assigned_point_a);
                        let is_eq = config.is_equal(ctx, &three_muled, &added);
                        println!("three_muled {:?}", three_muled);
                        println!("added {:?}", doubled);
                        // config.gate.assert_equal(
                        //     ctx,
                        //     QuantumCell::Constant(F::one()),
                        //     QuantumCell::Existing(&is_eq),
                        // );
                    }
                    Ok(())
                },
            )?;
            Ok(())
        }
    }

    impl<F: PrimeField> TestCircuit1<F> {
        // const PARAM_A: u64 = 168700;
        // const PARAM_D: u64 = 168696;
        const NUM_ADVICE: usize = 10;
        const NUM_FIXED: usize = 1;
        const K: usize = 15;
        // const BASE_POINT_X: &'static str =
        //     "5299619240641551281634865583518297030282874472190772894086521144482721001553";
        // const BASE_POINT_Y: &'static str =
        //     "16950150798460657717958625567821834550301663161624707787222815936182638968203";
    }

    #[test]
    fn test_add_and_mul() {
        let rand_a = Fr::random(&mut OsRng);
        let rand_b = Fr::random(&mut OsRng);
        let rand_c = Fr::random(&mut OsRng);
        let circuit = TestCircuit1 {
            rand_a,
            rand_b,
            rand_c,
        };
        let prover = MockProver::<Fr>::run(TestCircuit1::<Fr>::K as u32, &circuit, vec![]).unwrap();
        prover.verify().unwrap();
    }
}
