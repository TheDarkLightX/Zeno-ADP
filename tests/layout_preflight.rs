#![cfg(target_pointer_width = "64")]

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use zeno_adp::compiled::{Grammar, TokenGrammar};
use zeno_adp::{Error, Operator};

// The two review lengths have individually representable span counts and
// a product above usize::MAX. Allocate inputs before observing bind.
const LONG: usize = 2_000_000;
const SHORT: usize = 5_000;

struct Observe;

thread_local! {
    static BIND_ALLOCATIONS: Cell<Option<(usize, bool)>> = const { Cell::new(None) };
}

#[global_allocator]
static ALLOCATOR: Observe = Observe;

// Measurement only affects the thread executing the binding call.
unsafe impl GlobalAlloc for Observe {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if refuse_attempt() {
            return std::ptr::null_mut();
        }
        unsafe { System.alloc(layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, old: Layout, size: usize) -> *mut u8 {
        if refuse_attempt() {
            return std::ptr::null_mut();
        }
        unsafe { System.realloc(ptr, old, size) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

fn refuse_attempt() -> bool {
    BIND_ALLOCATIONS
        .try_with(|count| {
            if let Some((n, refuse)) = count.get() {
                count.set(Some((n + 1, refuse)));
                refuse
            } else {
                false
            }
        })
        .unwrap_or(false)
}

fn observe<T>(refuse: bool, bind: impl FnOnce() -> T) -> (T, usize) {
    BIND_ALLOCATIONS.set(Some((0, refuse)));
    let result = bind();
    (result, BIND_ALLOCATIONS.replace(None).unwrap().0)
}

#[derive(Clone)]
struct Leaf;

impl Operator for Leaf {
    fn arity(&self) -> usize {
        0
    }
}

#[test]
fn overflowing_product_never_allocates_offsets() {
    let byte = Grammar::<Leaf, 2>::new(&["S"], 0, vec![]).unwrap();
    let typed = TokenGrammar::<Leaf, 2, ()>::new(&["S"], 0, vec![]).unwrap();
    let (a, b) = (vec![0; LONG], vec![0; SHORT]);
    let (x, y) = (vec![(); LONG], vec![(); SHORT]);
    for (inputs, label) in [([&a[..], &b[..]], "long-first"), ([&b, &a], "short-first")] {
        let (bound, attempts) = observe(false, || byte.bind(inputs));
        assert_eq!(
            (bound.err(), attempts),
            (Some(Error::Overflow), 0),
            "byte {label}"
        );
    }
    for (inputs, label) in [([&x[..], &y[..]], "long-first"), ([&y, &x], "short-first")] {
        let (bound, attempts) = observe(false, || typed.bind(inputs));
        assert_eq!(
            (bound.err(), attempts),
            (Some(Error::Overflow), 0),
            "typed {label}"
        );
    }
}

#[test]
fn representable_layout_returns_reservation_failure() {
    let byte = Grammar::<Leaf, 2>::new(&["S"], 0, vec![]).unwrap();
    let typed = TokenGrammar::<Leaf, 2, ()>::new(&["S"], 0, vec![]).unwrap();
    // Empty tracks have one span each and request one offset apiece.
    let (bound, attempts) = observe(true, || byte.bind([&[], &[]]));
    assert_eq!((bound.err(), attempts), (Some(Error::AllocationFailed), 1));
    let (bound, attempts) = observe(true, || typed.bind([&[], &[]]));
    assert_eq!((bound.err(), attempts), (Some(Error::AllocationFailed), 1));
}
