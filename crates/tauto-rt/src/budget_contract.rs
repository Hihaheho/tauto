//! Explicit Rust embedding assertions for nonresuming budget facades.

/// An embedding's assertion of the `closed-host-v1` backend contract.
///
/// Passing a borrowed token to a qualified facade asserts this contract for
/// that invocation's inputs and context, not just for an individual callback.
/// The promise covers all reached Rust host code: callbacks, extern bindings,
/// captured values, implicit conversions, and custom `Clone` or `Drop`
/// implementations, including implementations attached to generated non-`Copy`
/// types. It also covers observers elsewhere in the embedding, including hooks.
///
/// Admitted host calls must return normally: no divergence, suspension, panic
/// or unwind, and no triggering or invocation of panic hooks. Host code must not
/// reenter Tauto or its runtime, retain supplied borrows or callbacks, or observe
/// or depend on transient reference counts, destruction order, or borrow and
/// value lifetimes. No host interaction may expose these distinctions through
/// an effect, a return value, or subsequent program behavior. Observable host
/// effects beyond the admitted calls' return values are outside this contract;
/// private scalar telemetry that cannot affect or be observed by the program
/// is not such an effect. These obligations also apply to implicit host calls
/// and to hooks invoked while the qualified invocation is active.
///
/// The caller must establish the input and context bounds needed by these
/// promises. The token does not own, inspect, invoke or validate any callback,
/// host value, or implementation. It is a trusted caller assertion, not a
/// compiler check, a kernel proof, or a security boundary. A false assertion can change program
/// behavior under optimization; it is not a memory-safety precondition and
/// does not permit generated unsafe code. Ordinary facades do not acquire the
/// assertion from a bare `Fn`, an empty effect row, or extern metadata alone.
///
/// Test counters can observe which implementation ran; they do not establish
/// this contract for an arbitrary callback or embedding.
#[must_use]
pub struct TrustedBudgetHost {
    _assertion: (),
}

impl TrustedBudgetHost {
    /// Assert the documented embedding contract for each qualified invocation
    /// that borrows this token. This performs no semantic validation.
    pub fn assert_contract() -> Self {
        Self { _assertion: () }
    }
}

#[cfg(test)]
mod tests {
    use super::TrustedBudgetHost;

    #[test]
    fn an_assertion_token_contains_no_host_state() {
        let contract = TrustedBudgetHost::assert_contract();
        assert_eq!(std::mem::size_of_val(&contract), 0);
        assert!(!std::mem::needs_drop::<TrustedBudgetHost>());
    }

    #[test]
    fn the_token_can_be_borrowed_without_any_callback_parameter() {
        fn borrow_contract(_: &TrustedBudgetHost) {}

        let contract = TrustedBudgetHost::assert_contract();
        borrow_contract(&contract);
        borrow_contract(&contract);
    }
}
