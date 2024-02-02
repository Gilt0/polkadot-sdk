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

use crate::{
	chain_head::test_utils::ChainHeadMockClient,
	transaction::{
		TransactionBroadcast as RpcTransactionBroadcast, TransactionBroadcastMiddleware, *,
	},
};
use futures::Future;
use jsonrpsee::RpcModule;
use sc_transaction_pool::BasicPool;
use sc_transaction_pool_api::error::Error as PoolError;
use sp_core::{testing::TaskExecutor, H256};
use sp_runtime::traits::Block as BlockT;
use std::{pin::Pin, sync::Arc};
use substrate_test_runtime_client::{prelude::*, Client};
use substrate_test_runtime_transaction_pool::TestApi;
use tokio::sync::mpsc;

pub type Block = substrate_test_runtime_client::runtime::Block;

pub type TxTestPool = BasicPool<TestApi, Block>;
pub type TxStatusType<Pool> = sc_transaction_pool_api::TransactionStatus<
	sc_transaction_pool_api::TxHash<Pool>,
	sc_transaction_pool_api::BlockHash<Pool>,
>;
pub type TxStatusTypeTest = TxStatusType<TxTestPool>;

/// Initial Alice account nonce.
pub const ALICE_NONCE: u64 = 209;

pub fn create_basic_pool_with_genesis(
	test_api: Arc<TestApi>,
) -> (BasicPool<TestApi, Block>, Pin<Box<dyn Future<Output = ()> + Send>>) {
	let genesis_hash = {
		test_api
			.chain()
			.read()
			.block_by_number
			.get(&0)
			.map(|blocks| blocks[0].0.header.hash())
			.expect("there is block 0. qed")
	};
	BasicPool::new_test(test_api, genesis_hash, genesis_hash)
}

pub fn maintained_pool() -> (BasicPool<TestApi, Block>, Arc<TestApi>, futures::executor::ThreadPool)
{
	let api = Arc::new(TestApi::with_alice_nonce(ALICE_NONCE));
	let (pool, background_task) = create_basic_pool_with_genesis(api.clone());

	let thread_pool = futures::executor::ThreadPool::new().unwrap();
	thread_pool.spawn_ok(background_task);
	(pool, api, thread_pool)
}

pub fn setup_api() -> (
	Arc<TestApi>,
	Arc<BasicPool<TestApi, Block>>,
	Arc<ChainHeadMockClient<Client<Backend>>>,
	RpcModule<
		TransactionBroadcast<
			BasicPool<TestApi, Block>,
			ChainHeadMockClient<Client<Backend>>,
			TransactionMiddlware,
		>,
	>,
	mpsc::UnboundedReceiver<MiddlewareEvent>,
) {
	let (pool, api, _) = maintained_pool();
	let pool = Arc::new(pool);

	let builder = TestClientBuilder::new();
	let client = Arc::new(builder.build());
	let client_mock = Arc::new(ChainHeadMockClient::new(client.clone()));
	let (middleware, recv) = TransactionMiddlware::new();

	let tx_api = RpcTransactionBroadcast::with_middleware(
		client_mock.clone(),
		pool.clone(),
		Arc::new(TaskExecutor::default()),
		middleware,
	)
	.into_rpc();

	(api, pool, client_mock, tx_api, recv)
}

/// The type of the event that the middleware captures.
#[derive(Debug, PartialEq)]
pub enum MiddlewareEvent {
	TransactionStatus {
		id: String,
		status: sc_transaction_pool_api::TransactionStatus<
			<Block as BlockT>::Hash,
			<Block as BlockT>::Hash,
		>,
	},
	PoolError {
		id: String,
		err: String,
	},
	Exit {
		id: String,
		is_aborted: bool,
	},
}

/// A middleware that captures the callback events and provides
/// them back to the testing code.
#[derive(Clone)]
pub struct TransactionMiddlware {
	/// Send the middleware events to the test.
	sender: mpsc::UnboundedSender<MiddlewareEvent>,
}

impl TransactionMiddlware {
	/// Construct a new middleware and a receiver to capture the events.
	pub fn new() -> (Self, mpsc::UnboundedReceiver<MiddlewareEvent>) {
		let (sender, recv) = mpsc::unbounded_channel();
		(TransactionMiddlware { sender }, recv)
	}
}

impl TransactionBroadcastMiddleware<sc_transaction_pool_api::TransactionStatus<H256, H256>>
	for TransactionMiddlware
{
	fn on_transaction_status(
		&self,
		operation_id: &str,
		status: &sc_transaction_pool_api::TransactionStatus<H256, H256>,
	) {
		self.sender
			.send(MiddlewareEvent::TransactionStatus {
				id: operation_id.to_string(),
				status: status.clone(),
			})
			.unwrap();
	}

	fn on_pool_error(&self, operation_id: &str, error: &PoolError) {
		self.sender
			.send(MiddlewareEvent::PoolError {
				id: operation_id.to_string(),
				err: error.to_string(),
			})
			.unwrap();
	}

	fn on_exit(&self, operation_id: &str, is_aborted: bool) {
		// We might drop the test receiver before the broadcast future is done.
		let _ = self
			.sender
			.send(MiddlewareEvent::Exit { id: operation_id.to_string(), is_aborted });
	}
}
