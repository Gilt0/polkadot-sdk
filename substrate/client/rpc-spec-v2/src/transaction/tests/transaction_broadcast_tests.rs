// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use super::utils::*;
use crate::{hex_string, transaction};
use assert_matches::assert_matches;
use codec::Encode;
use jsonrpsee::{core::error::Error, rpc_params};
use sc_transaction_pool::{Options, PoolLimit};
use sc_transaction_pool_api::{ChainEvent, MaintainedTransactionPool, TransactionPool};
use std::{collections::HashMap, sync::Arc};
use substrate_test_runtime_client::AccountKeyring::*;
use substrate_test_runtime_transaction_pool::uxt;

/// Get the next event from the provided middleware in at most 60 seconds.
macro_rules! get_next_event {
	($middleware:expr) => {
		tokio::time::timeout(std::time::Duration::from_secs(60), $middleware.recv())
			.await
			.unwrap()
			.unwrap()
	};
}

/// Collect N transaction status events from the provided middleware.
macro_rules! collect_n_tx_events {
	($middleware:expr, $num:expr) => {{
		let mut events = HashMap::new();
		for _ in 0..$num {
			let event = get_next_event!($middleware);
			match event {
				MiddlewarePoolEvent::TransactionStatus { transaction, status } => {
					events.insert(transaction, status);
				},
				_ => panic!("Expected TransactionStatus"),
			};
		}
		events
	}};
}

/// Collect N future exit events from the provided middleware.
macro_rules! collect_n_exit_events {
	($middleware:expr, $num:expr) => {{
		let mut events = HashMap::new();
		for _ in 0..$num {
			let event = get_next_event!($middleware);
			match event {
				MiddlewareEvent::Exit { id, is_aborted } => {
					events.insert(id, is_aborted);
				},
				_ => panic!("Expected Exit"),
			};
		}
		events
	}};
}

#[tokio::test]
async fn tx_broadcast_enters_pool() {
	let (api, pool, client_mock, tx_api, mut middleware, mut pool_middleware) = setup_api(Default::default());

	// Start at block 1.
	let block_1_header = api.push_block(1, vec![], true);

	let uxt = uxt(Alice, ALICE_NONCE);
	let xt = hex_string(&uxt.encode());

	let operation_id: String =
		tx_api.call("transaction_unstable_broadcast", rpc_params![&xt]).await.unwrap();

	// Announce block 1 to `transaction_unstable_broadcast`.
	client_mock.trigger_import_stream(block_1_header).await;

	// Ensure the tx propagated from `transaction_unstable_broadcast` to the transaction pool.
	let event = get_next_event!(&mut pool_middleware);
	assert_eq!(
		event,
		MiddlewarePoolEvent::TransactionStatus {
			transaction: xt.clone(),
			status: TxStatusTypeTest::Ready
		}
	);

	assert_eq!(1, pool.inner_pool.status().ready);
	assert_eq!(uxt.encode().len(), pool.inner_pool.status().ready_bytes);

	// Import block 2 with the transaction included.
	let block_2_header = api.push_block(2, vec![uxt.clone()], true);
	let block_2 = block_2_header.hash();

	// Announce block 2 to the pool.inner_pool.
	let event = ChainEvent::NewBestBlock { hash: block_2, tree_route: None };
	pool.inner_pool.maintain(event).await;

	assert_eq!(0, pool.inner_pool.status().ready);

	let event = get_next_event!(&mut pool_middleware);
	assert_eq!(
		event,
		MiddlewarePoolEvent::TransactionStatus {
			transaction: xt.clone(),
			status: TxStatusTypeTest::InBlock((block_2, 0))
		}
	);

	// The future broadcast awaits for the finalized status to be reached.
	// Force the future to exit by calling stop.
	let _: () = tx_api
		.call("transaction_unstable_stop", rpc_params![&operation_id])
		.await
		.unwrap();

	// Ensure the future terminated properly.
	// let event = get_next_event!(&mut middleware);
	// assert_eq!(event, MiddlewareEvent::Exit { id: operation_id.clone(), is_aborted: true });
}

#[tokio::test]
async fn tx_broadcast_stop_finished_broadcast() {
	// This test is very similar to `tx_broadcast_enters_pool`
	// However the last block is announced as finalized to force the
	// broadcast future to exit before the `stop` is called.

	let (api, pool, client_mock, tx_api, mut middleware, mut pool_middleware) = setup_api(Default::default());

	// Start at block 1.
	let block_1_header = api.push_block(1, vec![], true);

	let uxt = uxt(Alice, ALICE_NONCE);
	let xt = hex_string(&uxt.encode());

	let operation_id: String =
		tx_api.call("transaction_unstable_broadcast", rpc_params![&xt]).await.unwrap();

	// Announce block 1 to `transaction_unstable_broadcast`.
	client_mock.trigger_import_stream(block_1_header).await;

	// Ensure the tx propagated from `transaction_unstable_broadcast` to the transaction pool.inner_pool.
	let event = get_next_event!(&mut pool_middleware);
	assert_eq!(
		event,
		MiddlewarePoolEvent::TransactionStatus {
			transaction: xt.clone(),
			status: TxStatusTypeTest::Ready
		}
	);

	assert_eq!(1, pool.inner_pool.status().ready);
	assert_eq!(uxt.encode().len(), pool.inner_pool.status().ready_bytes);

	// Import block 2 with the transaction included.
	let block_2_header = api.push_block(2, vec![uxt.clone()], true);
	let block_2 = block_2_header.hash();

	// Announce block 2 to the pool.inner_pool.
	let event = ChainEvent::Finalized { hash: block_2, tree_route: Arc::from(vec![]) };
	pool.inner_pool.maintain(event).await;

	assert_eq!(0, pool.inner_pool.status().ready);

	let event = get_next_event!(&mut pool_middleware);
	assert_eq!(
		event,
		MiddlewarePoolEvent::TransactionStatus {
			transaction: xt.clone(),
			status: TxStatusTypeTest::InBlock((block_2, 0))
		}
	);

	let event = get_next_event!(&mut pool_middleware);
	assert_eq!(
		event,
		MiddlewarePoolEvent::TransactionStatus {
			transaction: xt.clone(),
			status: TxStatusTypeTest::Finalized((block_2, 0))
		}
	);

	// // Ensure the broadcast future terminated properly.
	// let event = get_next_event!(&mut middleware);
	// assert_eq!(event, MiddlewareEvent::Exit { id: operation_id.clone(), is_aborted: false });

	// Call stop after the broadcast finished.
	let _: () = tx_api
		.call("transaction_unstable_stop", rpc_params![&operation_id])
		.await
		.unwrap();
}

#[tokio::test]
async fn tx_broadcast_invalid_tx() {
	let (_, pool, _, tx_api, _, _) = setup_api(Default::default());

	// Invalid parameters.
	let err = tx_api
		.call::<_, serde_json::Value>("transaction_unstable_broadcast", [1u8])
		.await
		.unwrap_err();
	assert_matches!(err,
		Error::Call(err) if err.code() == transaction::error::json_rpc_spec::INVALID_PARAM_ERROR && err.message() == "Invalid params"
	);

	assert_eq!(0, pool.inner_pool.status().ready);

	// Invalid transaction that cannot be decoded. The broadcast silently exits.
	let xt = "0xdeadbeef";
	let operation_id: String =
		tx_api.call("transaction_unstable_broadcast", rpc_params![&xt]).await.unwrap();

	assert_eq!(0, pool.inner_pool.status().ready);

	// Ensure stop can be called, the tx was decoded and the broadcast future terminated.
	let _: () = tx_api
		.call("transaction_unstable_stop", rpc_params![&operation_id])
		.await
		.unwrap();
}

#[tokio::test]
async fn tx_invalid_stop() {
	let (_, _, _, tx_api, _, _) = setup_api(Default::default());

	// Make an invalid stop call.
	let err = tx_api
		.call::<_, serde_json::Value>("transaction_unstable_stop", ["invalid_operation_id"])
		.await
		.unwrap_err();
	assert_matches!(err,
		Error::Call(err) if err.code() == transaction::error::json_rpc_spec::INVALID_PARAM_ERROR && err.message() == "Invalid operation id"
	);
}

#[tokio::test]
async fn tx_broadcast_resubmits_future_nonce_tx() {
	let (api, pool, client_mock, tx_api, mut middleware, mut pool_middleware) = setup_api(Default::default());

	// Start at block 1.
	let block_1_header = api.push_block(1, vec![], true);
	let block_1 = block_1_header.hash();

	let current_uxt = uxt(Alice, ALICE_NONCE);
	let current_xt = hex_string(&current_uxt.encode());
	// This lives in the future.
	let future_uxt = uxt(Alice, ALICE_NONCE + 1);
	let future_xt = hex_string(&future_uxt.encode());

	let future_operation_id: String = tx_api
		.call("transaction_unstable_broadcast", rpc_params![&future_xt])
		.await
		.unwrap();

	// Announce block 1 to `transaction_unstable_broadcast`.
	client_mock.trigger_import_stream(block_1_header).await;

	// Ensure the tx propagated from `transaction_unstable_broadcast` to the transaction pool.
	let event = get_next_event!(&mut pool_middleware);
	assert_eq!(
		event,
		MiddlewarePoolEvent::TransactionStatus {
			transaction: future_xt.clone(),
			status: TxStatusTypeTest::Future
		}
	);

	let event = ChainEvent::NewBestBlock { hash: block_1, tree_route: None };
	pool.inner_pool.maintain(event).await;
	assert_eq!(0, pool.inner_pool.status().ready);
	// Ensure the tx is in the future.
	assert_eq!(1, pool.inner_pool.status().future);

	let block_2_header = api.push_block(2, vec![], true);
	let block_2 = block_2_header.hash();

	let operation_id: String = tx_api
		.call("transaction_unstable_broadcast", rpc_params![&current_xt])
		.await
		.unwrap();

	// Announce block 2 to `transaction_unstable_broadcast`.
	client_mock.trigger_import_stream(block_2_header).await;

	// Collect the events of both transactions.
	let events = collect_n_tx_events!(&mut pool_middleware, 2);
	// Transactions entered the ready queue.
	assert_eq!(events.get(&current_xt).unwrap(), &TxStatusTypeTest::Ready);
	assert_eq!(events.get(&future_xt).unwrap(), &TxStatusTypeTest::Ready);

	let event = ChainEvent::NewBestBlock { hash: block_2, tree_route: None };
	pool.inner_pool.maintain(event).await;
	assert_eq!(2, pool.inner_pool.status().ready);
	assert_eq!(0, pool.inner_pool.status().future);

	// Finalize transactions.
	let block_3_header = api.push_block(3, vec![current_uxt, future_uxt], true);
	let block_3 = block_3_header.hash();
	client_mock.trigger_import_stream(block_3_header).await;

	let event = ChainEvent::Finalized { hash: block_3, tree_route: Arc::from(vec![]) };
	pool.inner_pool.maintain(event).await;
	assert_eq!(0, pool.inner_pool.status().ready);
	assert_eq!(0, pool.inner_pool.status().future);

	let events = collect_n_tx_events!(&mut pool_middleware, 2);
	assert_eq!(events.get(&current_xt).unwrap(), &TxStatusTypeTest::InBlock((block_3, 0)));
	assert_eq!(events.get(&future_xt).unwrap(), &TxStatusTypeTest::InBlock((block_3, 1)));

	let events = collect_n_tx_events!(&mut pool_middleware, 2);
	assert_eq!(events.get(&current_xt).unwrap(), &TxStatusTypeTest::Finalized((block_3, 0)));
	assert_eq!(
		events.get(&future_xt).unwrap(),
		&TxStatusTypeTest::Finalized((block_3, 1))
	);

	// let events = collect_n_exit_events!(&mut middleware, 2);
	// assert_eq!(events.get(&operation_id).unwrap(), &false);
	// assert_eq!(events.get(&future_xt).unwrap(), &false);
}

#[tokio::test]
async fn tx_broadcast_resubmits_invalid_tx() {
	let limits = PoolLimit { count: 8192, total_bytes: 20 * 1024 * 1024 };
	let options = Options {
		ready: limits.clone(),
		future: limits,
		reject_future_transactions: false,
		// This ensures that a transaction is not banned.
		ban_time: std::time::Duration::ZERO,
	};

	let (api, pool, client_mock, tx_api, mut middleware, mut pool_middleware) = setup_api(options);

	let uxt = uxt(Alice, ALICE_NONCE);
	let xt = hex_string(&uxt.encode());
	let operation_id: String =
		tx_api.call("transaction_unstable_broadcast", rpc_params![&xt]).await.unwrap();

	let block_1_header = api.push_block(1, vec![], true);
	let block_1 = block_1_header.hash();
	// Announce block 1 to `transaction_unstable_broadcast`.
	client_mock.trigger_import_stream(block_1_header).await;

	// Ensure the tx propagated from `transaction_unstable_broadcast` to the transaction pool.
	let event = get_next_event!(&mut pool_middleware);
	assert_eq!(
		event,
		MiddlewarePoolEvent::TransactionStatus {
			transaction: xt.clone(),
			status: TxStatusTypeTest::Ready,
		}
	);
	assert_eq!(1, pool.inner_pool.status().ready);
	assert_eq!(uxt.encode().len(), pool.inner_pool.status().ready_bytes);

	// Mark the transaction as invalid from the API, causing a temporary ban.
	api.add_invalid(&uxt);

	// Push an event to the pool to ensure the transaction is excluded.
	let event = ChainEvent::NewBestBlock { hash: block_1, tree_route: None };
	pool.inner_pool.maintain(event).await;
	assert_eq!(1, pool.inner_pool.status().ready);

	// Ensure the `transaction_unstable_broadcast` is aware of the invalid transaction.
	let event = get_next_event!(&mut pool_middleware);
	// Because we have received an `Invalid` status, we try to broadcast the transaction with the
	// next announced block.
	assert_eq!(
		event,
		MiddlewarePoolEvent::TransactionStatus {
			transaction: xt.clone(),
			status: TxStatusTypeTest::Invalid
		}
	);

	// Import block 2.
	let block_2_header = api.push_block(2, vec![], true);
	client_mock.trigger_import_stream(block_2_header).await;

	// Ensure we propagate the temporary ban error to `submit_and_watch`.
	// This ensures we'll loop again with the next annmounced block and try to resubmit the
	// transaction. The transaction remains temporarily banned until the pool is maintained.
	let event = get_next_event!(&mut pool_middleware);
	assert_matches!(event, MiddlewarePoolEvent::PoolError { transaction, err } if transaction == xt && err.contains("Transaction temporarily Banned"));

	// Import block 3.
	let block_3_header = api.push_block(3, vec![], true);
	let block_3 = block_3_header.hash();
	// Remove the invalid transaction from the pool to allow it to pass through.
	api.remove_invalid(&uxt);
	let event = ChainEvent::NewBestBlock { hash: block_3, tree_route: None };
	// We have to maintain the pool to ensure the transaction is no longer invalid.
	// This clears out the banned transactions.
	pool.inner_pool.maintain(event).await;
	assert_eq!(0, pool.inner_pool.status().ready);

	// Announce block to `transaction_unstable_broadcast`.
	client_mock.trigger_import_stream(block_3_header).await;

	let event = get_next_event!(&mut pool_middleware);
	assert_eq!(
		event,
		MiddlewarePoolEvent::TransactionStatus {
			transaction: xt.clone(),
			status: TxStatusTypeTest::Ready,
		}
	);
	assert_eq!(1, pool.inner_pool.status().ready);

	let block_4_header = api.push_block(4, vec![uxt], true);
	let block_4 = block_4_header.hash();
	let event = ChainEvent::Finalized { hash: block_4, tree_route: Arc::from(vec![]) };
	pool.inner_pool.maintain(event).await;

	let event = get_next_event!(&mut pool_middleware);
	assert_eq!(
		event,
		MiddlewarePoolEvent::TransactionStatus {
			transaction: xt.clone(),
			status: TxStatusTypeTest::InBlock((block_4, 0)),
		}
	);
	let event = get_next_event!(&mut pool_middleware);
	assert_eq!(
		event,
		MiddlewarePoolEvent::TransactionStatus {
			transaction: xt.clone(),
			status: TxStatusTypeTest::Finalized((block_4, 0)),
		}
	);
	// // At this point the broadcast future has exited.
	// let event = get_next_event!(&mut middleware);
	// assert_eq!(event, MiddlewareEvent::Exit { id: operation_id.clone(), is_aborted: false });
}
