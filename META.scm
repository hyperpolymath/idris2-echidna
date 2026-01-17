;; SPDX-License-Identifier: MPL-2.0
;; META.scm - Meta-level information for idris2-echidna

(meta
  (architecture-decisions
    (adr-001
      (title "Use dependent types for proof verification")
      (status "accepted")
      (date "2025-01-17")
      (context "Need to ensure proof results are type-safe and verifiable at compile time")
      (decision "Use Idris2 dependent types to encode proof validity in the type system")
      (consequences
        "Proofs are verified at compile time"
        "Invalid proofs cannot be constructed"
        "Requires understanding of dependent types to use"))

    (adr-002
      (title "Prover-agnostic core API")
      (status "accepted")
      (date "2025-01-17")
      (context "Multiple theorem provers exist with different interfaces")
      (decision "Define abstract Prover interface with concrete implementations per prover")
      (consequences
        "Easy to add new provers"
        "Consistent API across provers"
        "Some prover-specific features may be harder to expose"))

    (adr-003
      (title "FFI for native prover integration")
      (status "proposed")
      (date "2025-01-17")
      (context "Native prover bindings would be faster than process spawning")
      (decision "Use Idris2 FFI for provers with C APIs, fall back to process for others")
      (consequences
        "Better performance for supported provers"
        "More complex build setup"
        "Platform-specific considerations")))

  (development-practices
    (code-style "Follow Idris2 community style guide")
    (security "Sanitize all inputs to provers")
    (testing "Unit tests for each prover module")
    (versioning "Semantic versioning")
    (documentation "Module-level doc comments")
    (branching "main for stable, feature/* for development"))

  (design-rationale
    (why-idris2 "Dependent types enable compile-time proof verification")
    (why-multiple-provers "Different provers excel at different problem domains")
    (why-smt-lib-encoding "Standard format supported by many provers")))
