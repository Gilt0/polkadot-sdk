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

use super::setup::Block;
use crate::transaction::TransactionBroadcastMiddleware;
use futures::channel::mpsc;
use sc_transaction_pool_api::error::Error as PoolError;
use sp_core::H256;
use sp_runtime::traits::Block as BlockT;

/// The type of the event that the middleware captures.
#[derive(Debug, PartialEq)]
enum MiddlewareEvent {
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
struct TransactionMiddlware {
	/// Send the middleware events to the test.
	send: mpsc::UnboundedSender<MiddlewareEvent>,
}

impl TransactionMiddlware {
	/// Construct a new middleware and a receiver to capture the events.
	pub fn new() -> (Self, mpsc::UnboundedReceiver<MiddlewareEvent>) {
		let (send, recv) = mpsc::unbounded();
		(TransactionMiddlware { send }, recv)
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
		self.send
			.unbounded_send(MiddlewareEvent::TransactionStatus {
				id: operation_id.to_string(),
				status: status.clone(),
			})
			.unwrap();
	}

	fn on_pool_error(&self, operation_id: &str, error: &PoolError) {
		self.send
			.unbounded_send(MiddlewareEvent::PoolError {
				id: operation_id.to_string(),
				err: error.to_string(),
			})
			.unwrap();
	}

	fn on_exit(&self, operation_id: &str, is_aborted: bool) {
		// We might drop the test receiver before the broadcast future is done.
		let _ = self
			.send
			.unbounded_send(MiddlewareEvent::Exit { id: operation_id.to_string(), is_aborted });
	}
}
