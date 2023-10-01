// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Default weights for the AURA Pallet.
//! This file was not auto-generated.

use frame_support::weights::{
	constants::{RocksDbWeight as DbWeight, WEIGHT_REF_TIME_PER_MICROS, WEIGHT_REF_TIME_PER_NANOS},
	Weight,
};

/// Default `WeightInfo` generic over the max number of validator's nominators (`N`).
pub struct WeightInfo<const N: u32>;

impl<const N: u32> crate::WeightInfo for WeightInfo<N> {
	fn report_equivocation(validator_count: u32) -> Weight {
		// We take the validator set count from the membership proof to
		// calculate the weight but we set a floor of 100 validators.
		let validator_count = validator_count.max(100) as u64;
		let max_nominators_per_validator = N;

		// Checking membership proof
		Weight::from_parts(35u64 * WEIGHT_REF_TIME_PER_MICROS, 0)
			.saturating_add(
				Weight::from_parts(175u64 * WEIGHT_REF_TIME_PER_NANOS, 0)
					.saturating_mul(validator_count),
			)
			.saturating_add(DbWeight::get().reads(5))
			// Check equivocation proof
			.saturating_add(Weight::from_parts(110u64 * WEIGHT_REF_TIME_PER_MICROS, 0))
			// Report offence
			.saturating_add(Weight::from_parts(110u64 * WEIGHT_REF_TIME_PER_MICROS, 0))
			.saturating_add(Weight::from_parts(
				25u64 * WEIGHT_REF_TIME_PER_MICROS * max_nominators_per_validator as u64,
				0,
			))
			.saturating_add(DbWeight::get().reads(14 + 3 * max_nominators_per_validator as u64))
			.saturating_add(DbWeight::get().writes(10 + 3 * max_nominators_per_validator as u64))
	}
}
