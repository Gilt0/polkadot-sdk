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

#![cfg(test)]
mod mock;

pub(crate) const LOG_TARGET: &str = "integration-tests::epm-staking";

use mock::*;

use frame_election_provider_support::{bounds::ElectionBoundsBuilder, ElectionDataProvider};
use pallet_election_provider_multi_block::Phase;

use frame_support::assert_ok;

// syntactic sugar for logging.
#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		log::$level!(
			target: crate::LOG_TARGET,
			concat!("🛠️  ", $patter)  $(, $values)*
		)
	};
}

fn log_current_time() {
	log!(
		info,
		"block: {:?}, session: {:?}, era: {:?}, EPM phase: {:?} ts: {:?}",
		System::block_number(),
		Session::current_index(),
		Staking::current_era(),
		ElectionProvider::current_phase(),
		Timestamp::now()
	);
}

#[test]
fn block_progression_works() {
	let (mut ext, _pool_state, _) = ExtBuilder::default().build_offchainify();
	ext.execute_with(|| {})
}

#[test]
fn verify_snapshot() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(Pages::get(), 3);

		// manually get targets and voters from staking to see the inspect the issue with the
		// DataProvider.
		let bounds = ElectionBoundsBuilder::default()
			.targets_count((TargetSnapshotPerBlock::get() as u32).into())
			.voters_count((VoterSnapshotPerBlock::get() as u32).into())
			.build();

		assert_ok!(<Staking as ElectionDataProvider>::electable_targets(bounds.targets, 2));
		assert_ok!(<Staking as ElectionDataProvider>::electing_voters(bounds.voters, 2));
	})
}

mod staking_integration {
	use super::*;

	#[test]
	fn call_elect_single_block() {
		ExtBuilder::default().build_and_execute(|| {
			assert_eq!(Pages::get(), 3);
			assert_eq!(ElectionProvider::current_round(), 0);
			assert_eq!(Staking::current_era(), Some(0));

			roll_to(election_prediction(), false);

			// election successfully, round & era progressed.
			assert_eq!(ElectionProvider::current_phase(), Phase::Off);
			assert_eq!(ElectionProvider::current_round(), 1);
			assert_eq!(Staking::current_era(), Some(1));
		})
	}

	#[test]
	fn call_elect_multi_block() {}
}
