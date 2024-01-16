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

//! # Types for the multi-block election provider pallet.

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{BoundedVec, DebugNoBound};
use scale_info::TypeInfo;
use sp_npos_elections::ElectionScore;
use sp_runtime::SaturatedConversion;

use crate::Verifier;

use frame_election_provider_support::{ElectionProvider, NposSolution, PageIndex};

/// The main account ID type.
pub type AccountIdOf<T> = <T as frame_system::Config>::AccountId;

/// Supports that are returned from a given [`Verifier`].
pub type SupportsOf<V> = frame_election_provider_support::BoundedSupports<
	<V as Verifier>::AccountId,
	<V as Verifier>::MaxWinnersPerPage,
	<V as Verifier>::MaxBackersPerWinner,
>;

/// The voter index. Derived from [`SolutionOf`].
pub type SolutionVoterIndexOf<T> = <SolutionOf<T> as NposSolution>::VoterIndex;
/// The target index. Derived from [`SolutionOf`].
pub type SolutionTargetIndexOf<T> = <SolutionOf<T> as NposSolution>::TargetIndex;

/// The solution type used by this crate.
pub type SolutionOf<T> = <T as crate::Config>::Solution;

#[derive(DebugNoBound, PartialEq)]
pub enum ElectionError<T: crate::Config> {
	/// Error returned by the election data provider.
	DataProvider,
	/// The data provider returned data that exceeded the boundaries defined in the contract with
	/// the election provider.
	DataProviderBoundariesExceeded,
	/// The support `page_index` was not available at request.
	SupportPageNotAvailable(PageIndex),
	/// The requested page exceeds the number of election pages defined of the current election
	/// config.
	RequestedPageExceeded,
	/// The fallback election error'ed.
	Fallback(FallbackErrorOf<T>),
}

/// Alias for an error of a fallback election provider.
type FallbackErrorOf<T> = <<T as crate::Config>::Fallback as ElectionProvider>::Error;

/// Alias for a voter, parameterized by this crate's config.
pub(crate) type VoterOf<T> =
	frame_election_provider_support::VoterOf<<T as crate::Config>::DataProvider>;

/// Alias for a page of voters, parameterized by this crate's config.
pub(crate) type VoterPageOf<T> =
	BoundedVec<VoterOf<T>, <T as crate::Config>::VoterSnapshotPerBlock>;

pub(crate) type MaxWinnersPerPageOf<T> = <<T as crate::Config>::Verifier as Verifier>::MaxWinnersPerPage;

/// Current phase of an election.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, MaxEncodedLen, Debug, TypeInfo)]
pub enum Phase<Bn> {
	/// Election has halted -- nothing will happen.
	Halted,
	/// The election is off.
	Off,
	/// Signed phase is open.
	Signed,
	/// The signed validations phase
	SignedValidation(Bn),
	Unsigned(Bn),
	/// Preparing the paged target and voter snapshots.
	Snapshot(PageIndex),
	/// Exporting a paged election result.
	Export,
	/// Emergency phase, something went wrong and the election is halted.
	Emergency,
}

impl<Bn> Default for Phase<Bn> {
	fn default() -> Self {
		Phase::Off
	}
}

impl<Bn: PartialEq + Eq> Phase<Bn> {
	pub(crate) fn is_signed(&self) -> bool {
		matches!(self, Phase::Signed)
	}

	/// Returns whether the validation phase is ongoing.
	pub(crate) fn is_signed_validation_open_at(&self, at: Option<Bn>) -> bool {
		match at {
			Some(at) => matches!(self, Phase::SignedValidation(real) if *real == at),
			None => matches!(self, Phase::SignedValidation(_)),
		}
	}

	pub(crate) fn is_unsigned_open_at(&self, at: Bn) -> bool {
		matches!(self, Phase::Unsigned(real) if *real == at)
	}
}

use frame_support::{
	CloneNoBound, DefaultNoBound, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};

/// Encodes the length of a page of either a solution or a snapshot.
///
/// This is stored automatically on-chain, and it contains the **size of the entire snapshot page**.
/// This is also used in dispatchables as weight witness data and should **only contain the size of
/// the presented solution page**, not the entire snapshot or page snaphsot.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, Debug, Default, TypeInfo)]
pub struct PageSize {
	/// The length of voters.
	#[codec(compact)]
	pub voters: u32,
	/// The length of targets.
	#[codec(compact)]
	pub targets: u32,
}

/// Alias for all pages of voters, parameterized by this crate's config.
pub(crate) type AllVoterPagesOf<T> = BoundedVec<VoterPageOf<T>, <T as crate::Config>::Pages>;
// Accuracy of the election.
pub type SolutionAccuracyOf<T> = <SolutionOf<T> as NposSolution>::Accuracy;

/// Edges from voters to nominated targets that are part of the winner set.
pub type AssignmentOf<T> = sp_npos_elections::Assignment<AccountIdOf<T>, SolutionAccuracyOf<T>>;

/// A paged raw solution which contains a set of paginated solutions to be submitted.
///
/// A raw solution has not been checked for correctness.
#[derive(
	TypeInfo,
	Encode,
	Decode,
	RuntimeDebugNoBound,
	CloneNoBound,
	EqNoBound,
	PartialEqNoBound,
	MaxEncodedLen,
	DefaultNoBound,
)]
#[codec(mel_bound(T: crate::Config))]
#[scale_info(skip_type_params(T))]
pub struct PagedRawSolution<T: crate::Config> {
	pub solution_pages: BoundedVec<SolutionOf<T>, T::Pages>,
	pub score: ElectionScore,
	pub round: u32,
}

/// A helper trait to deal with the page index of partial solutions.
///
/// This should only be called on the `Vec<Solution>` or similar types. If the solution is *full*,
/// then it returns a normal iterator that is just mapping the index (usize) to `PageIndex`.
///
/// if the solution is partial, it shifts the indices sufficiently so that the most significant page
/// of the solution matches with the most significant page of the snapshot onchain.
pub trait Pagify<T> {
	fn pagify(&self, bound: PageIndex) -> Box<dyn Iterator<Item = (PageIndex, &T)> + '_>;
	fn into_pagify(self, bound: PageIndex) -> Box<dyn Iterator<Item = (PageIndex, T)>>;
}

impl<T> Pagify<T> for Vec<T> {
	fn pagify(&self, desired_pages: PageIndex) -> Box<dyn Iterator<Item = (PageIndex, &T)> + '_> {
		Box::new(
			self.into_iter()
				.enumerate()
				.map(|(p, s)| (p.saturated_into::<PageIndex>(), s))
				.map(move |(p, s)| {
					let desired_pages_usize = desired_pages as usize;
					// TODO: this could be an error.
					debug_assert!(self.len() <= desired_pages_usize);
					let padding = desired_pages_usize.saturating_sub(self.len());
					let new_page = p.saturating_add(padding.saturated_into::<PageIndex>());
					(new_page, s)
				}),
		)
	}

	fn into_pagify(self, _: PageIndex) -> Box<dyn Iterator<Item = (PageIndex, T)>> {
		todo!()
	}
}
