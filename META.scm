; SPDX-License-Identifier: MPL-2.0
; META.scm - Project metadata and architectural decisions

(meta
  (version "1.0")
  (project "idris2-echidna")

  (architecture-decisions
    (adr-001
      (status "accepted")
      (date "2025-01-17")
      (title "Use C FFI for ECHIDNA integration")
      (context "Need to call ECHIDNA's Rust library from Idris2")
      (decision "Use Idris2's C FFI with ECHIDNA's C-compatible API")
      (consequences
        "Requires ECHIDNA to expose C-compatible functions"
        "Need to handle memory management at FFI boundary"
        "Portable across platforms that support C ABI"))

    (adr-002
      (status "accepted")
      (date "2025-01-17")
      (title "Interface-based prover abstraction")
      (context "Need unified API for 12 different provers")
      (decision "Use Idris2 interfaces to define Prover typeclass")
      (consequences
        "Each prover can have custom implementation"
        "Users can select prover at type level"
        "Enables prover-specific optimizations"))

    (adr-003
      (status "accepted")
      (date "2025-01-17")
      (title "Aspect tagging for proof organization")
      (context "Need to categorize and search proofs semantically")
      (decision "Implement aspect tagging system matching ECHIDNA's")
      (consequences
        "Proofs can be tagged by domain, technique, complexity"
        "Enables semantic search across proof libraries"))

    (adr-004
      (status "accepted")
      (date "2025-01-17")
      (title "Prover tier system")
      (context "Provers have different capabilities and reliability")
      (decision "Implement 4-tier system: Tier1 (core SMT + dependent), Tier2 (classical), Tier3 (specialized), Tier4 (legacy)")
      (consequences
        "Users can target appropriate tier for their needs"
        "Tier guides prover selection strategies"))

    (adr-005
      (status "accepted")
      (date "2025-01-17")
      (title "Integration modules for ecosystem")
      (context "Need to work with idris2-dyadt and idris2-cno")
      (decision "Create dedicated Integration.* modules for each sibling library")
      (consequences
        "Clean separation of concerns"
        "Optional dependencies - base echidna works standalone"
        "Easy to extend for future ecosystem libraries")))

  (development-practices
    (code-style
      "Follow Idris2 standard naming conventions"
      "Use total functions where possible (%default total)"
      "Public exports explicit with 'public export'"
      "Document all public functions with ||| comments")
    (security
      "Validate all FFI inputs"
      "Sandbox prover execution where possible"
      "No arbitrary code execution from provers")
    (testing
      "Type-checking as primary test"
      "Property-based tests for FFI boundary"
      "Integration tests with actual provers")
    (versioning "Semantic versioning (SemVer)")
    (documentation
      "README.adoc with quick start"
      "Doc comments on all public APIs"
      "Examples directory with working code")
    (branching
      "main is stable"
      "feature/* for new features"
      "fix/* for bug fixes"))

  (design-rationale
    (why-idris2
      "Dependent types enable encoding proof obligations in types"
      "Strong compile-time guarantees"
      "Good FFI story for external integration")
    (why-ffi
      "ECHIDNA is Rust-based; FFI is most practical integration"
      "Avoid reimplementing 12 provers in Idris2"
      "Leverage existing battle-tested implementations")
    (why-multiple-provers
      "Different provers excel at different domains"
      "Redundancy for verification confidence"
      "User choice based on problem characteristics")
    (why-separate-integration-modules
      "Keep core echidna minimal and focused"
      "Allow ecosystem libraries to be optional"
      "Reduce compile times for users not needing all integrations")))
