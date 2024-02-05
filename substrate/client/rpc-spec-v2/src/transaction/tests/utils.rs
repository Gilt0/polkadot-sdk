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
use codec::Encode;
use futures::Future;
use jsonrpsee::RpcModule;
use sc_transaction_pool::{BasicPool, Options};
use sc_transaction_pool_api::{
	error::Error as PoolError, ImportNotificationStream, PoolFuture, PoolStatus, ReadyTransactions,
	TransactionFor, TransactionPool, TransactionSource, TransactionStatusStreamFor, TxHash,
};

use crate::hex_string;
use futures::FutureExt;
use futures::StreamExt;

use sp_core::{testing::TaskExecutor, H256};
use sp_runtime::traits::Block as BlockT;
use sp_runtime::traits::NumberFor;
use std::{collections::HashMap, pin::Pin, sync::Arc};
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
	options: Options,
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
	BasicPool::new_test(test_api, genesis_hash, genesis_hash, options)
}

pub fn maintained_pool(
	options: Options,
) -> (BasicPool<TestApi, Block>, Arc<TestApi>, futures::executor::ThreadPool) {
	let api = Arc::new(TestApi::with_alice_nonce(ALICE_NONCE));
	let (pool, background_task) = create_basic_pool_with_genesis(api.clone(), options);

	let thread_pool = futures::executor::ThreadPool::new().unwrap();
	thread_pool.spawn_ok(background_task);
	(pool, api, thread_pool)
}

pub fn setup_api(
	options: Options,
) -> (
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
	let (pool, api, _) = maintained_pool(options);
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

/// The type of the event that the middleware captures.
#[derive(Debug, PartialEq)]
pub enum MiddlewarePoolEvent {
	TransactionStatus {
		transaction: String,
		status: sc_transaction_pool_api::TransactionStatus<
			<Block as BlockT>::Hash,
			<Block as BlockT>::Hash,
		>,
	},
	PoolError {
		transaction: String,
		err: String,
	},
}

/// Add a middleware to the transaction pool.
///
/// This wraps the `submit_and_watch` to gain access to the events.
struct MiddlewarePool {
	pool: Arc<BasicPool<TestApi, Block>>,
	/// Send the middleware events to the test.
	sender: mpsc::UnboundedSender<MiddlewarePoolEvent>,
}

impl MiddlewarePool {
	/// Construct a new [`MiddlewarePool`].
	fn new(
		pool: Arc<BasicPool<TestApi, Block>>,
	) -> (Self, mpsc::UnboundedReceiver<MiddlewarePoolEvent>) {
		let (sender, recv) = mpsc::unbounded_channel();
		(MiddlewarePool { pool, sender }, recv)
	}
}

impl TransactionPool for MiddlewarePool {
	type Block = <BasicPool<TestApi, Block> as TransactionPool>::Block;
	type Hash = <BasicPool<TestApi, Block> as TransactionPool>::Hash;
	type InPoolTransaction = <BasicPool<TestApi, Block> as TransactionPool>::InPoolTransaction;
	type Error = <BasicPool<TestApi, Block> as TransactionPool>::Error;

	fn submit_at(
		&self,
		at: <Self::Block as BlockT>::Hash,
		source: TransactionSource,
		xts: Vec<TransactionFor<Self>>,
	) -> PoolFuture<Vec<Result<TxHash<Self>, Self::Error>>, Self::Error> {
		self.pool.submit_at(at, source, xts)
	}

	fn submit_one(
		&self,
		at: <Self::Block as BlockT>::Hash,
		source: TransactionSource,
		xt: TransactionFor<Self>,
	) -> PoolFuture<TxHash<Self>, Self::Error> {
		self.pool.submit_one(at, source, xt)
	}

	fn submit_and_watch(
		&self,
		at: <Self::Block as BlockT>::Hash,
		source: TransactionSource,
		xt: TransactionFor<Self>,
	) -> PoolFuture<Pin<Box<TransactionStatusStreamFor<Self>>>, Self::Error> {
		let pool = self.pool.clone();
		let sender = self.sender.clone();
		let transaction = hex_string(&xt.encode());

		async move {
			let watcher = match pool.submit_and_watch(at, source, xt).await {
				Ok(watcher) => watcher,
				Err(err) => {
					let _ = sender.send(MiddlewarePoolEvent::PoolError {
						transaction: transaction.clone(),
						err: err.to_string(),
					});
					return Err(err);
				},
			};

			let watcher = watcher.map(move |status| {
				let sender = sender.clone();
				let transaction = transaction.clone();

				let _ = sender.send(MiddlewarePoolEvent::TransactionStatus {
					transaction,
					status: status.clone(),
				});

				status
			});

			Ok(watcher.boxed())
		}
		.boxed()
	}

	fn remove_invalid(&self, hashes: &[TxHash<Self>]) -> Vec<Arc<Self::InPoolTransaction>> {
		self.pool.remove_invalid(hashes)
	}

	fn status(&self) -> PoolStatus {
		self.pool.status()
	}

	fn import_notification_stream(&self) -> ImportNotificationStream<TxHash<Self>> {
		self.pool.import_notification_stream()
	}

	fn hash_of(&self, xt: &TransactionFor<Self>) -> TxHash<Self> {
		self.pool.hash_of(xt)
	}

	fn on_broadcasted(&self, propagations: HashMap<TxHash<Self>, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}

	fn ready_transaction(&self, hash: &TxHash<Self>) -> Option<Arc<Self::InPoolTransaction>> {
		self.pool.ready_transaction(hash)
	}

	fn ready_at(
		&self,
		at: NumberFor<Self::Block>,
	) -> Pin<
		Box<
			dyn Future<
					Output = Box<dyn ReadyTransactions<Item = Arc<Self::InPoolTransaction>> + Send>,
				> + Send,
		>,
	> {
		self.pool.ready_at(at)
	}

	fn ready(&self) -> Box<dyn ReadyTransactions<Item = Arc<Self::InPoolTransaction>> + Send> {
		self.pool.ready()
	}

	fn futures(&self) -> Vec<Self::InPoolTransaction> {
		self.pool.futures()
	}
}
