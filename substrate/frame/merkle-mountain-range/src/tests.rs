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

use crate::{mock::*, *};

use frame_support::traits::{Get, OnInitialize};
use sp_core::{
	offchain::{testing::TestOffchainExt, OffchainDbExt, OffchainWorkerExt},
	H256,
};
use sp_mmr_primitives::{mmr_lib::helper, utils, Compact, Proof};
use sp_runtime::BuildStorage;

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	frame_system::GenesisConfig::<Test>::default().build_storage().unwrap().into()
}

fn register_offchain_ext(ext: &mut sp_io::TestExternalities) {
	let (offchain, _offchain_state) = TestOffchainExt::with_offchain_db(ext.offchain_db());
	ext.register_extension(OffchainDbExt::new(offchain.clone()));
	ext.register_extension(OffchainWorkerExt::new(offchain));
}

fn new_block() -> Weight {
	let number = frame_system::Pallet::<Test>::block_number() + 1;
	let hash = H256::repeat_byte(number as u8);
	LeafDataTestValue::mutate(|r| r.a = number);

	frame_system::Pallet::<Test>::reset_events();
	frame_system::Pallet::<Test>::initialize(&number, &hash, &Default::default());
	MMR::on_initialize(number)
}

fn peaks_from_leaves_count(leaves_count: NodeIndex) -> Vec<NodeIndex> {
	let size = utils::NodesUtils::new(leaves_count).size();
	helper::get_peaks(size)
}

pub(crate) fn hex(s: &str) -> H256 {
	s.parse().unwrap()
}

type BlockNumber = frame_system::pallet_prelude::BlockNumberFor<Test>;

fn decode_node(
	v: Vec<u8>,
) -> mmr::Node<<Test as Config>::Hashing, ((BlockNumber, H256), LeafData)> {
	use crate::primitives::DataOrHash;
	type A = DataOrHash<<Test as Config>::Hashing, (BlockNumber, H256)>;
	type B = DataOrHash<<Test as Config>::Hashing, LeafData>;
	type Node = mmr::Node<<Test as Config>::Hashing, (A, B)>;
	let tuple: Node = codec::Decode::decode(&mut &v[..]).unwrap();

	match tuple {
		mmr::Node::Data((DataOrHash::Data(a), DataOrHash::Data(b))) => mmr::Node::Data((a, b)),
		mmr::Node::Hash(hash) => mmr::Node::Hash(hash),
		_ => unreachable!(),
	}
}

fn add_blocks(blocks: usize) {
	// given
	for _ in 0..blocks {
		new_block();
	}
}

#[test]
fn should_start_empty() {
	let _ = env_logger::try_init();
	new_test_ext().execute_with(|| {
		// given
		assert_eq!(
			crate::RootHash::<Test>::get(),
			"0000000000000000000000000000000000000000000000000000000000000000"
				.parse()
				.unwrap()
		);
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 0);
		assert_eq!(crate::Nodes::<Test>::get(0), None);

		// when
		let weight = new_block();

		// then
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 1);
		assert_eq!(
			crate::Nodes::<Test>::get(0),
			Some(hex("f467378cd91be46c35c020eb389c851f5ff89656f27f6cb4bc6bf31a97bc15c5"))
		);
		assert_eq!(
			crate::RootHash::<Test>::get(),
			hex("f467378cd91be46c35c020eb389c851f5ff89656f27f6cb4bc6bf31a97bc15c5")
		);
		assert!(weight != Weight::zero());
	});
}

#[test]
fn should_append_to_mmr_when_on_initialize_is_called() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	let (parent_b1, parent_b2) = ext.execute_with(|| {
		// when
		new_block();
		let parent_b1 = <frame_system::Pallet<Test>>::parent_hash();

		// then
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 1);
		assert_eq!(
			(
				crate::Nodes::<Test>::get(0),
				crate::Nodes::<Test>::get(1),
				crate::RootHash::<Test>::get(),
			),
			(
				Some(hex("f467378cd91be46c35c020eb389c851f5ff89656f27f6cb4bc6bf31a97bc15c5")),
				None,
				hex("0xf467378cd91be46c35c020eb389c851f5ff89656f27f6cb4bc6bf31a97bc15c5"),
			)
		);

		// when
		new_block();
		let parent_b2 = <frame_system::Pallet<Test>>::parent_hash();

		// then
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 2);
		let peaks = peaks_from_leaves_count(2);
		assert_eq!(peaks, vec![2]);
		assert_eq!(
			(
				crate::Nodes::<Test>::get(0),
				crate::Nodes::<Test>::get(1),
				crate::Nodes::<Test>::get(2),
				crate::Nodes::<Test>::get(3),
				crate::RootHash::<Test>::get(),
			),
			(
				None,
				None,
				Some(hex("58811a9effcb08da58c86b1d23e1e595863fcf2d2f3273d1afad6ed0a73f3913")),
				None,
				hex("58811a9effcb08da58c86b1d23e1e595863fcf2d2f3273d1afad6ed0a73f3913"),
			)
		);

		(parent_b1, parent_b2)
	});
	// make sure the leaves end up in the offchain DB
	ext.persist_offchain_overlay();

	let offchain_db = ext.offchain_db();

	let expected = Some(mmr::Node::Data(((0, H256::repeat_byte(1)), LeafData::new(1))));
	assert_eq!(
		offchain_db.get(&MMR::node_temp_offchain_key(0, parent_b1)).map(decode_node),
		expected
	);

	let expected = Some(mmr::Node::Data(((1, H256::repeat_byte(2)), LeafData::new(2))));
	assert_eq!(
		offchain_db.get(&MMR::node_temp_offchain_key(1, parent_b2)).map(decode_node),
		expected
	);

	let expected = Some(mmr::Node::Hash(hex(
		"58811a9effcb08da58c86b1d23e1e595863fcf2d2f3273d1afad6ed0a73f3913",
	)));
	assert_eq!(
		offchain_db.get(&MMR::node_temp_offchain_key(2, parent_b2)).map(decode_node),
		expected
	);

	assert_eq!(offchain_db.get(&MMR::node_temp_offchain_key(3, parent_b2)), None);
}

#[test]
fn should_construct_larger_mmr_correctly() {
	let _ = env_logger::try_init();
	new_test_ext().execute_with(|| {
		// when
		add_blocks(7);

		// then
		assert_eq!(crate::NumberOfLeaves::<Test>::get(), 7);
		let peaks = peaks_from_leaves_count(7);
		assert_eq!(peaks, vec![6, 9, 10]);
		for i in (0..=10).filter(|p| !peaks.contains(p)) {
			assert!(crate::Nodes::<Test>::get(i).is_none());
		}
		assert_eq!(
			(
				crate::Nodes::<Test>::get(6),
				crate::Nodes::<Test>::get(9),
				crate::Nodes::<Test>::get(10),
				crate::RootHash::<Test>::get(),
			),
			(
				Some(hex("4e3fb711b8d82d2cc0a062f64c8b008781d514b2db5c4287ef4a5f30001798ad")),
				Some(hex("8f6511e74ed817a685ddc0906a92e66696ac61ea601e121641cab4f751d9cf0b")),
				Some(hex("01e19b7a77b40a1055b4f255ce2dc25eaeec01744379e2c750b67509a12b1995")),
				hex("25a6a0750a3a20036edc2764253d742743499f61092cac84a07bf429c3bf114d"),
			)
		);
	});
}

#[test]
fn should_calculate_the_size_correctly() {
	let _ = env_logger::try_init();

	let leaves = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 21];
	let sizes = vec![0, 1, 3, 4, 7, 8, 10, 11, 15, 16, 18, 19, 22, 23, 25, 26, 39];

	// size cross-check
	let mut actual_sizes = vec![];
	for s in &leaves[1..] {
		new_test_ext().execute_with(|| {
			let mut mmr = mmr::Mmr::<mmr::storage::RuntimeStorage, crate::mock::Test, _, _>::new(0);
			for i in 0..*s {
				mmr.push(i);
			}
			actual_sizes.push(mmr.size());
		})
	}
	assert_eq!(sizes[1..], actual_sizes[..]);
}

#[test]
fn should_generate_proofs_correctly() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	// given
	let num_blocks: u64 = 7;
	ext.execute_with(|| add_blocks(num_blocks as usize));
	ext.persist_offchain_overlay();

	// Try to generate proofs now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	ext.execute_with(|| {
		let best_block_number = frame_system::Pallet::<Test>::block_number();
		// when generate proofs for all leaves.
		let proofs = (1_u64..=best_block_number)
			.into_iter()
			.map(|block_num| crate::Pallet::<Test>::generate_proof(vec![block_num], None).unwrap())
			.collect::<Vec<_>>();
		// when generate historical proofs for all leaves
		let historical_proofs = (1_u64..best_block_number)
			.into_iter()
			.map(|block_num| {
				let mut proofs = vec![];
				for historical_best_block in block_num..=num_blocks {
					proofs.push(
						crate::Pallet::<Test>::generate_proof(
							vec![block_num],
							Some(historical_best_block),
						)
						.unwrap(),
					)
				}
				proofs
			})
			.collect::<Vec<_>>();

		// then
		assert_eq!(
			proofs[0],
			(
				vec![Compact::new(((0, H256::repeat_byte(1)).into(), LeafData::new(1).into(),))],
				Proof {
					leaf_indices: vec![0],
					leaf_count: 7,
					items: vec![
						hex("643edf8ea59ed2232c1696f2a02194944b4736e7ac42f53074543fde2e8587e0"),
						hex("9ea4336f0498374120735bc6d18c9e1f3a6d6dd47c07b32420010b80e320664c"),
						hex("03312a705c249aab61efce14a1782087030a168ba2a4cd848cb6c1c22369c6d9"),
					],
				}
			)
		);
		assert_eq!(
			historical_proofs[0][0],
			(
				vec![Compact::new(((0, H256::repeat_byte(1)).into(), LeafData::new(1).into(),))],
				Proof { leaf_indices: vec![0], leaf_count: 1, items: vec![] }
			)
		);

		//       D
		//     /   \
		//    /     \
		//   A       B       C
		//  / \     / \     / \
		// 1   2   3   4   5   6  7
		//
		// we're proving 3 => we need { 4, A, C++7 }
		assert_eq!(
			proofs[2],
			(
				vec![Compact::new(((2, H256::repeat_byte(3)).into(), LeafData::new(3).into(),))],
				Proof {
					leaf_indices: vec![2],
					leaf_count: 7,
					items: vec![
						hex("3da35e025298c9416ee3ba66418c6fec29ac974ada8be89550b71fbabcc2b3ce"),
						hex("58811a9effcb08da58c86b1d23e1e595863fcf2d2f3273d1afad6ed0a73f3913"),
						hex("03312a705c249aab61efce14a1782087030a168ba2a4cd848cb6c1c22369c6d9"),
					],
				}
			)
		);
		//   A
		//  / \
		// 1   2   3
		//
		// we're proving 3 => we need { A }
		assert_eq!(
			historical_proofs[2][0],
			(
				vec![Compact::new(((2, H256::repeat_byte(3)).into(), LeafData::new(3).into(),))],
				Proof {
					leaf_indices: vec![2],
					leaf_count: 3,
					items: vec![hex(
						"58811a9effcb08da58c86b1d23e1e595863fcf2d2f3273d1afad6ed0a73f3913"
					)],
				}
			)
		);
		//       D
		//     /   \
		//    /     \
		//   A       B
		//  / \     / \
		// 1   2   3   4   5
		// we're proving 3 => we need { 4, A, 5 }
		assert_eq!(
			historical_proofs[2][2],
			(
				vec![Compact::new(((2, H256::repeat_byte(3)).into(), LeafData::new(3).into(),))],
				Proof {
					leaf_indices: vec![2],
					leaf_count: 5,
					items: vec![
						hex("3da35e025298c9416ee3ba66418c6fec29ac974ada8be89550b71fbabcc2b3ce"),
						hex("58811a9effcb08da58c86b1d23e1e595863fcf2d2f3273d1afad6ed0a73f3913"),
						hex("f24de46b2ce3d772a16096d4914650f7e8f6f3a2bac7f02e20444a061ff9e13e")
					],
				}
			)
		);
		assert_eq!(historical_proofs[2][4], proofs[2]);

		assert_eq!(
			proofs[4],
			(
				// NOTE: the leaf index is equivalent to the block number(in this case 5) - 1
				vec![Compact::new(((4, H256::repeat_byte(5)).into(), LeafData::new(5).into(),))],
				Proof {
					leaf_indices: vec![4],
					leaf_count: 7,
					items: vec![
						hex("4e3fb711b8d82d2cc0a062f64c8b008781d514b2db5c4287ef4a5f30001798ad"),
						hex("b34a69ddd99ca7ea708f65ee791a0cfb8f6c86402159471f873dcb2e905cba8c"),
						hex("01e19b7a77b40a1055b4f255ce2dc25eaeec01744379e2c750b67509a12b1995"),
					],
				}
			)
		);
		assert_eq!(
			historical_proofs[4][0],
			(
				vec![Compact::new(((4, H256::repeat_byte(5)).into(), LeafData::new(5).into(),))],
				Proof {
					leaf_indices: vec![4],
					leaf_count: 5,
					items: vec![hex(
						"4e3fb711b8d82d2cc0a062f64c8b008781d514b2db5c4287ef4a5f30001798ad"
					),],
				}
			)
		);
		assert_eq!(historical_proofs[4][2], proofs[4]);

		assert_eq!(
			proofs[6],
			(
				vec![Compact::new(((6, H256::repeat_byte(7)).into(), LeafData::new(7).into(),))],
				Proof {
					leaf_indices: vec![6],
					leaf_count: 7,
					items: vec![
						hex("4e3fb711b8d82d2cc0a062f64c8b008781d514b2db5c4287ef4a5f30001798ad"),
						hex("8f6511e74ed817a685ddc0906a92e66696ac61ea601e121641cab4f751d9cf0b"),
					],
				}
			)
		);
		assert_eq!(historical_proofs[5][1], proofs[5]);
	});
}

#[test]
fn should_generate_batch_proof_correctly() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	// given
	ext.execute_with(|| add_blocks(7));
	ext.persist_offchain_overlay();

	// Try to generate proofs now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	ext.execute_with(|| {
		// when generate proofs for a batch of leaves
		let (.., proof) = crate::Pallet::<Test>::generate_proof(vec![1, 5, 6], None).unwrap();
		// then
		assert_eq!(
			proof,
			Proof {
				// the leaf indices are equivalent to the above specified block numbers - 1.
				leaf_indices: vec![0, 4, 5],
				leaf_count: 7,
				items: vec![
					hex("643edf8ea59ed2232c1696f2a02194944b4736e7ac42f53074543fde2e8587e0"),
					hex("9ea4336f0498374120735bc6d18c9e1f3a6d6dd47c07b32420010b80e320664c"),
					hex("01e19b7a77b40a1055b4f255ce2dc25eaeec01744379e2c750b67509a12b1995"),
				],
			}
		);

		// when generate historical proofs for a batch of leaves
		let (.., historical_proof) =
			crate::Pallet::<Test>::generate_proof(vec![1, 5, 6], Some(6)).unwrap();
		// then
		assert_eq!(
			historical_proof,
			Proof {
				leaf_indices: vec![0, 4, 5],
				leaf_count: 6,
				items: vec![
					hex("643edf8ea59ed2232c1696f2a02194944b4736e7ac42f53074543fde2e8587e0"),
					hex("9ea4336f0498374120735bc6d18c9e1f3a6d6dd47c07b32420010b80e320664c"),
				],
			}
		);

		// when generate historical proofs for a batch of leaves
		let (.., historical_proof) =
			crate::Pallet::<Test>::generate_proof(vec![1, 5, 6], None).unwrap();
		// then
		assert_eq!(historical_proof, proof);
	});
}

#[test]
fn should_verify() {
	let _ = env_logger::try_init();

	// Start off with chain initialisation and storing indexing data off-chain
	// (MMR Leafs)
	let mut ext = new_test_ext();
	ext.execute_with(|| add_blocks(7));
	ext.persist_offchain_overlay();

	// Try to generate proof now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	let (leaves, proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_proof(vec![5], None).unwrap()
	});
	let (simple_historical_leaves, simple_historical_proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_proof(vec![5], Some(6)).unwrap()
	});
	let (advanced_historical_leaves, advanced_historical_proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_proof(vec![5], Some(7)).unwrap()
	});

	ext.execute_with(|| {
		add_blocks(7);
		// then
		assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proof5), Ok(()));
		assert_eq!(
			crate::Pallet::<Test>::verify_leaves(
				simple_historical_leaves,
				simple_historical_proof5
			),
			Ok(())
		);
		assert_eq!(
			crate::Pallet::<Test>::verify_leaves(
				advanced_historical_leaves,
				advanced_historical_proof5
			),
			Ok(())
		);
	});
}

#[test]
fn should_verify_batch_proofs() {
	fn generate_and_verify_batch_proof(
		ext: &mut sp_io::TestExternalities,
		block_numbers: &Vec<u64>,
		blocks_to_add: usize,
	) {
		let (leaves, proof) = ext.execute_with(|| {
			crate::Pallet::<Test>::generate_proof(block_numbers.to_vec(), None).unwrap()
		});

		let max_block_number = ext.execute_with(|| frame_system::Pallet::<Test>::block_number());
		let min_block_number = block_numbers.iter().max().unwrap();

		// generate all possible historical proofs for the given blocks
		let historical_proofs = (*min_block_number..=max_block_number)
			.map(|best_block| {
				ext.execute_with(|| {
					crate::Pallet::<Test>::generate_proof(block_numbers.to_vec(), Some(best_block))
						.unwrap()
				})
			})
			.collect::<Vec<_>>();

		ext.execute_with(|| {
			add_blocks(blocks_to_add);
			// then
			assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proof), Ok(()));
			historical_proofs.iter().for_each(|(leaves, proof)| {
				assert_eq!(
					crate::Pallet::<Test>::verify_leaves(leaves.clone(), proof.clone()),
					Ok(())
				);
			});
		})
	}

	let _ = env_logger::try_init();

	use itertools::Itertools;

	let mut ext = new_test_ext();
	// require the offchain extensions to be present
	// to retrieve full leaf data when generating proofs
	register_offchain_ext(&mut ext);

	// verify that up to n=10, valid proofs are generated for all possible block number
	// combinations.
	for n in 1..=10 {
		ext.execute_with(|| new_block());
		ext.persist_offchain_overlay();

		// generate powerset (skipping empty set) of all possible block number combinations for mmr
		// size n.
		let blocks_set: Vec<Vec<u64>> = (1..=n).into_iter().powerset().skip(1).collect();

		blocks_set.iter().for_each(|blocks_subset| {
			generate_and_verify_batch_proof(&mut ext, &blocks_subset, 0);
			ext.persist_offchain_overlay();
		});
	}

	// verify that up to n=15, valid proofs are generated for all possible 2-block number
	// combinations.
	for n in 11..=15 {
		ext.execute_with(|| new_block());
		ext.persist_offchain_overlay();

		// generate all possible 2-block number combinations for mmr size n.
		let blocks_set: Vec<Vec<u64>> = (1..=n).into_iter().combinations(2).collect();

		blocks_set.iter().for_each(|blocks_subset| {
			generate_and_verify_batch_proof(&mut ext, &blocks_subset, 0);
			ext.persist_offchain_overlay();
		});
	}

	generate_and_verify_batch_proof(&mut ext, &vec![8, 12], 20);
	ext.execute_with(|| add_blocks(1000));
	ext.persist_offchain_overlay();
	generate_and_verify_batch_proof(&mut ext, &vec![8, 12, 100, 800], 100);
}

#[test]
fn verification_should_be_stateless() {
	let _ = env_logger::try_init();

	// Start off with chain initialisation and storing indexing data off-chain
	// (MMR Leafs)
	let mut ext = new_test_ext();
	let (root_6, root_7) = ext.execute_with(|| {
		add_blocks(6);
		let root_6 = crate::Pallet::<Test>::mmr_root();
		add_blocks(1);
		let root_7 = crate::Pallet::<Test>::mmr_root();
		(root_6, root_7)
	});
	ext.persist_offchain_overlay();

	// Try to generate proof now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	let (leaves, proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_proof(vec![5], None).unwrap()
	});
	let (_, historical_proof5) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_proof(vec![5], Some(6)).unwrap()
	});

	// Verify proof without relying on any on-chain data.
	let leaf = crate::primitives::DataOrHash::Data(leaves[0].clone());
	assert_eq!(
		crate::verify_leaves_proof::<<Test as Config>::Hashing, _>(
			root_7,
			vec![leaf.clone()],
			proof5
		),
		Ok(())
	);
	assert_eq!(
		crate::verify_leaves_proof::<<Test as Config>::Hashing, _>(
			root_6,
			vec![leaf],
			historical_proof5
		),
		Ok(())
	);
}

#[test]
fn should_verify_batch_proof_statelessly() {
	let _ = env_logger::try_init();

	// Start off with chain initialisation and storing indexing data off-chain
	// (MMR Leafs)
	let mut ext = new_test_ext();
	let (root_6, root_7) = ext.execute_with(|| {
		add_blocks(6);
		let root_6 = crate::Pallet::<Test>::mmr_root();
		add_blocks(1);
		let root_7 = crate::Pallet::<Test>::mmr_root();
		(root_6, root_7)
	});
	ext.persist_offchain_overlay();

	// Try to generate proof now. This requires the offchain extensions to be present
	// to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	let (leaves, proof) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_proof(vec![1, 4, 5], None).unwrap()
	});
	let (historical_leaves, historical_proof) = ext.execute_with(|| {
		// when
		crate::Pallet::<Test>::generate_proof(vec![1, 4, 5], Some(6)).unwrap()
	});

	// Verify proof without relying on any on-chain data.
	assert_eq!(
		crate::verify_leaves_proof::<<Test as Config>::Hashing, _>(
			root_7,
			leaves
				.into_iter()
				.map(|leaf| crate::primitives::DataOrHash::Data(leaf))
				.collect(),
			proof
		),
		Ok(())
	);
	assert_eq!(
		crate::verify_leaves_proof::<<Test as Config>::Hashing, _>(
			root_6,
			historical_leaves
				.into_iter()
				.map(|leaf| crate::primitives::DataOrHash::Data(leaf))
				.collect(),
			historical_proof
		),
		Ok(())
	);
}

#[test]
fn should_verify_on_the_next_block_since_there_is_no_pruning_yet() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();
	// given
	ext.execute_with(|| add_blocks(7));

	ext.persist_offchain_overlay();
	register_offchain_ext(&mut ext);

	ext.execute_with(|| {
		// when
		let (leaves, proof5) = crate::Pallet::<Test>::generate_proof(vec![5], None).unwrap();
		new_block();

		// then
		assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proof5), Ok(()));
	});
}

#[test]
fn should_verify_canonicalized() {
	use frame_support::traits::Hooks;
	let _ = env_logger::try_init();

	// How deep is our fork-aware storage (in terms of blocks/leaves, nodes will be more).
	let block_hash_size: u64 = <Test as frame_system::Config>::BlockHashCount::get();

	// Start off with chain initialisation and storing indexing data off-chain.
	// Create twice as many leaf entries than our fork-aware capacity,
	// resulting in ~half of MMR storage to use canonical keys and the other half fork-aware keys.
	// Verify that proofs can be generated (using leaves and nodes from full set) and verified.
	let mut ext = new_test_ext();
	register_offchain_ext(&mut ext);
	for blocknum in 0u32..(2 * block_hash_size).try_into().unwrap() {
		ext.execute_with(|| {
			new_block();
			<Pallet<Test> as Hooks<BlockNumber>>::offchain_worker(blocknum.into());
		});
		ext.persist_offchain_overlay();
	}

	// Generate proofs for some blocks.
	let (leaves, proofs) =
		ext.execute_with(|| crate::Pallet::<Test>::generate_proof(vec![1, 4, 5, 7], None).unwrap());
	// Verify all previously generated proofs.
	ext.execute_with(|| {
		assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proofs), Ok(()));
	});

	// Generate proofs for some new blocks.
	let (leaves, proofs) = ext.execute_with(|| {
		crate::Pallet::<Test>::generate_proof(vec![block_hash_size + 7], None).unwrap()
	});
	// Add some more blocks then verify all previously generated proofs.
	ext.execute_with(|| {
		add_blocks(7);
		assert_eq!(crate::Pallet::<Test>::verify_leaves(leaves, proofs), Ok(()));
	});
}

#[test]
fn does_not_panic_when_generating_historical_proofs() {
	let _ = env_logger::try_init();
	let mut ext = new_test_ext();

	// given 7 blocks (7 MMR leaves)
	ext.execute_with(|| add_blocks(7));
	ext.persist_offchain_overlay();

	// Try to generate historical proof with invalid arguments. This requires the offchain
	// extensions to be present to retrieve full leaf data.
	register_offchain_ext(&mut ext);
	ext.execute_with(|| {
		// when leaf index is invalid
		assert_eq!(crate::Pallet::<Test>::generate_proof(vec![10], None), Err(Error::LeafNotFound),);

		// when leaves count is invalid
		assert_eq!(
			crate::Pallet::<Test>::generate_proof(vec![3], Some(100)),
			Err(Error::GenerateProof),
		);

		// when both leaf index and leaves count are invalid
		assert_eq!(
			crate::Pallet::<Test>::generate_proof(vec![10], Some(100)),
			Err(Error::LeafNotFound),
		);
	});
}
