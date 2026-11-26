// src/driver/nvme_async.rs
use core::future::Future;
use core::task::{Context, Poll, Waker};
use core::pin::Pin;
use alloc::sync::Arc;
use spin::Mutex;
use crate::driver::nvme_rs::SqEntry;

pub struct PendingRequest {
    pub waker: Option<Waker>,
    pub result: Option<syscall::Result<usize>>,
}

pub struct NvmeDriverContext {
    pending: hashbrown::HashMap<u16, Arc<Mutex<PendingRequest>>>,
}

pub struct NvmeRequest {
    pub cmd_id: u16,
    pub state: Arc<Mutex<PendingRequest>>,
    pub sq_entry: SqEntry,
}

impl Future for NvmeRequest {
    type Output = syscall::Result<usize>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut state = self.state.lock();

        if let Some(result) = state.result.take() {
            Poll::Ready(result)
        } else {
            state.waker = Some(cx.waker().clone());
            // Real submission logic to driver would happen here or at construction
            Poll::Pending
        }
    }
}