// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Useful function for inflation for nominated proof of stake.

use sp_arithmetic::{Perbill, biguint::BigUint, traits::Zero};
use core::convert::TryFrom;

/// Parameter for NPoS curve
///
/// (as detailed
/// [here](https://research.web3.foundation/en/latest/polkadot/economics/1-token-economics.html#inflation-model-with-parachains))
#[derive(Clone)]
pub struct Parameter {
	/// The minimal amount to be rewarded between validators, expressed as a fraction
	/// of total issuance. Known as `I_0` in the literature.
	pub min_inflation: Perbill,
	/// The maximum amount to be rewarded between validators, expressed as a fraction
	/// of total issuance. This is attained only when `ideal_stake` is achieved.
	/// Must be between min_inflation and 1.
	pub max_inflation: Perbill,
	/// The fraction of total issued tokens that should be actively staked behind
	/// validators. Known as `x_ideal` in the literature.
	/// Must be more than 0.
	pub ideal_stake: Perbill,
	/// Known as `decay_rate` in the literature. A co-efficient dictating the strength of
	/// the global incentivization to get the `ideal_stake`. A higher number results in less typical
	/// inflation at the cost of greater volatility for validators.
	/// Must be more than 0.
	pub falloff: Perbill,
	/// The fraction of total issued tokens that actively staked behind
	/// validators. Known as `x` in the literature.
	pub stake: Perbill,
}

/// Compute yearly inflation using function:
///
/// ```ignore
/// I(x) = for x between 0 and x_ideal: I0 + x * (i_ideal - I0 / x_ideal),
/// for x between x_ideal and 1: I0 + (i_ideal * x_ideal - I0) * 2^((x_ideal - x) / d)
/// ```
///
/// where:
/// * x is the stake rate, i.e. fraction of total issued tokens that actively staked behind
///   validators.
/// * d is the falloff or `decay_rate` see [`Parameter`].
/// * I0 is the minimum inflation.
/// * x_ideal: the ideal stake rate.
/// * i_ideal: ideal intereset rate, i.e. x_ideal * i_ideal is maximum inflation.
///
/// (as detailed
/// [here](https://research.web3.foundation/en/latest/polkadot/economics/1-token-economics.html#inflation-model-with-parachains))
///
/// For documentation on parameters see [`Parameter`].
///
/// It is recommanded to test that the computation is precise enough using
/// [`test_inflation_computation`].
pub fn compute_inflation(param: Parameter) -> Perbill {
	let p = match INPoSParam::check_and_convert(&param) {
		Ok(p) => p,
		Err(()) => {
			debug_assert!(true, "Invalid parameters");
			return param.min_inflation;
		},
	};

	let res = if p.x <= p.x_ideal {
		compute_left_part(&p)
	} else {
		compute_right_part(&p)
	};

	let min_inflation = param.min_inflation.deconstruct() as u128;
	let max_inflation = param.max_inflation.deconstruct() as u128;

	match u128::try_from(res) {
		Ok(res) if res <= max_inflation && res >= min_inflation => Perbill::from_parts(res as u32),
		// If result is beyond bounds there is nothing we can do
		_ => {
			debug_assert!(true, "Invalid inflation computation");
			return param.min_inflation;
		},
	}
}


/// Internal struct holding parameter info alongside other cached value.
///
/// All expressed in billionth
struct INPoSParam {
	i_0: BigUint,
	i_ideal_times_x_ideal: BigUint,
	ln_2_div_d: BigUint,
	i_ideal: BigUint,
	x_ideal: BigUint,
	i_0_div_x_ideal: BigUint,
	_d: BigUint,
	x: BigUint,
}

/// `ln(2)` expressed in billionth.
const LN2: u32 = 0_693_147_181;
/// 1 billion.
const BILLION: u32 = 1_000_000_000;

impl INPoSParam {
	/// Check parameter validity and convert
	///
	/// I.e. checks for:
	/// * max_inflation >= min_inflation.
	/// * falloff > 0
	/// * ideal_stake > 0
	fn check_and_convert(p: &Parameter) -> Result<Self, ()> {
		if p.min_inflation > p.max_inflation {
			return Err(())
		}

		if p.falloff.is_zero() {
			return Err(())
		}

		if p.ideal_stake.is_zero() {
			return Err(())
		}

		Ok(INPoSParam {
			i_0: BigUint::from(p.min_inflation.deconstruct()),
			i_ideal_times_x_ideal: BigUint::from(p.max_inflation.deconstruct()),
			ln_2_div_d: BigUint::from(
				LN2 as u64 * BILLION as u64
					/ p.falloff.deconstruct() as u64
			),
			i_ideal: BigUint::from(
				p.max_inflation.deconstruct() as u64 * BILLION as u64
					/ p.ideal_stake.deconstruct() as u64
			),
			x_ideal: BigUint::from(p.ideal_stake.deconstruct()),
			i_0_div_x_ideal: BigUint::from(
				p.min_inflation.deconstruct() as u64 * BILLION as u64
					/ p.ideal_stake.deconstruct() as u64
			),
			_d: BigUint::from(p.falloff.deconstruct()),
			x: BigUint::from(p.stake.deconstruct()),
		})
	}
}

/// Compute `i_0 + x * (i_ideal - i_0 / x_ideal)`
///
/// Result is expressed in billionth.
fn compute_left_part(p: &INPoSParam) -> BigUint {
	p.i_0.clone().add(
		&p.x.clone()
			.mul(
				&p.i_ideal.clone().sub(&p.i_0_div_x_ideal.clone())
					// NOTE: should never happen because i_ideal >= i_0 / x_ideal.
					// because i_ideal * x_ideal >= i_0
					// because max_inflation >= i_0
					.unwrap_or_else(|_| BigUint::zero())
			)
			.div_unit(BILLION)
	)
}

/// Compute `i_0 + (i_ideal_times_x_ideal - i_0) * 2^((x_ideal - x) / d)`
///
/// x must be striclty more than x_ideal.
///
/// result is expressed in billionth.
fn compute_right_part(p: &INPoSParam) -> BigUint {
	let i_ideal_time_x_ideal_sub_i_0 = p.i_ideal_times_x_ideal.clone().sub(&p.i_0.clone())
		// NOTE: should never happen because max_inflation >= i_0
		.unwrap_or_else(|_| BigUint::zero());

	p.i_0.clone()
		+ (i_ideal_time_x_ideal_sub_i_0.clone() * compute_taylor_serie_part(&p)).div_unit(BILLION)
}

/// Compute `2^((x_ideal - x) / d)` using taylor serie.
///
/// x must be striclty more than x_ideal.
///
/// result is expressed in billionth.
fn compute_taylor_serie_part(p: &INPoSParam) -> BigUint {
	// The last computed taylor term.
	let mut last_taylor_term = BigUint::from(BILLION);

	// Whereas taylor sum is positive.
	let mut taylor_sum_positive = true;

	// The sum of all taylor term.
	let mut taylor_sum = last_taylor_term.clone();

	for k in 1..300 {
		last_taylor_term = compute_taylor_term(k, &last_taylor_term, p);

		if last_taylor_term.is_zero() {
			break
		}

		let last_taylor_term_positive = k % 2 == 0;

		if taylor_sum_positive == last_taylor_term_positive {
			taylor_sum = taylor_sum.add(&last_taylor_term);
		} else {
			if taylor_sum >= last_taylor_term {
				taylor_sum = taylor_sum.sub(&last_taylor_term)
					// NOTE: Should never happen as checked above
					.unwrap_or_else(|e| e);
			} else {
				taylor_sum_positive = !taylor_sum_positive;
				taylor_sum = last_taylor_term.clone().sub(&taylor_sum)
					// NOTE: Should never happen as checked above
					.unwrap_or_else(|e| e);
			}
		}
	}

	taylor_sum.lstrip();
	taylor_sum
}

/// Return the absolute value of k-th taylor term of `2^((x_ideal - x))/d` i.e.
/// `((x - x_ideal) * ln(2) / d)^k / k!`
///
/// x must be strictly more x_ideal.
///
/// We compute the term from the last term using this formula:
///
/// `((x - x_ideal) * ln(2) / d)^k / k! == previous_term * (x - x_ideal) * ln(2) / d / k`
///
/// `previous_taylor_term` and result are expressed in billionth.
fn compute_taylor_term(k: u32, previous_taylor_term: &BigUint, p: &INPoSParam) -> BigUint {
	let x_minus_x_ideal = p.x.clone().sub(&p.x_ideal)
		// NOTE: Should never happen, as x must be more than x_ideal
		.unwrap_or_else(|_| BigUint::zero());

	let mut res = previous_taylor_term.clone()
		.mul(&x_minus_x_ideal)
		.mul(&p.ln_2_div_d)
		.div_unit(BILLION)
		.div_unit(BILLION)
		.div_unit(k);

	res.lstrip();
	res
}

/// This test for different value of stake and ideal_stake, compare with float computation,
/// and panics if error too big error.
///
/// `ideal_stake` goes from 0.000_000_001 to 1 with increment 0.001.
/// `stake` goes from 0 to 1 with increment 0.001.
/// error is asserted to be less than 0.000_000_002.
#[cfg(feature = "std")]
pub fn test_inflation_computation(
	min_inflation: Perbill,
	max_inflation: Perbill,
	falloff: Perbill
) {
	for ideal_stake in 0..1000 {
		for stake in 0..1000 {
			let ideal_stake = if ideal_stake == 0 {
				1
			} else {
				ideal_stake * 1_000_000
			};

			let stake = stake * 1_000_000;

			let param = Parameter {
				max_inflation,
				min_inflation,
				falloff,
				ideal_stake: Perbill::from_parts(ideal_stake),
				stake: Perbill::from_parts(stake),
			};

			let res = compute_inflation(param.clone());
			let res = res.deconstruct() as f64 / BILLION as f64;

			let expect = float_i_npos(param);

			if (res - expect).abs() > 0.000_000_002 {
				panic!(
					"ideal_stake: {}, stake: {}, res: {}, expect: {}",
					ideal_stake, stake, res , expect
				);
			}
		}
	}
}

#[cfg(feature = "std")]
fn float_i_npos(param: Parameter) -> f64 {
	let max_inflation = param.max_inflation.deconstruct() as f64 / BILLION as f64;
	let min_inflation = param.min_inflation.deconstruct() as f64 / BILLION as f64;
	let ideal_stake = param.ideal_stake.deconstruct() as f64 / BILLION as f64;
	let stake = param.stake.deconstruct() as f64 / BILLION as f64;
	let falloff = param.falloff.deconstruct() as f64 / BILLION as f64;

	let i_0 = min_inflation;
	let i_ideal = max_inflation / ideal_stake;
	let x_ideal = ideal_stake;
	let x = stake;
	let d = falloff;

	if x <= x_ideal {
		i_0 + x * (i_ideal - i_0 / x_ideal)
	} else {
		i_0 + (i_ideal * x_ideal - i_0) * 2_f64.powf((x_ideal - x) / d)
	}
}
