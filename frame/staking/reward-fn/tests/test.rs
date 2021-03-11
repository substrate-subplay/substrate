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

use pallet_staking_reward_fn;
use sp_arithmetic::Perbill;

#[test]
fn test_precision_for_x_and_x_ideal_varying() {
	pallet_staking_reward_fn::test_inflation_computation(
		Perbill::from_fraction(0.025),
		Perbill::from_fraction(0.1),
		Perbill::from_fraction(0.05),
	);
}

#[test]
fn test_precision_for_x_and_x_ideal_varying_2() {
	pallet_staking_reward_fn::test_inflation_computation(
		Perbill::from_fraction(0.025),
		Perbill::from_fraction(0.1),
		Perbill::from_fraction(0.01),
	);
}
