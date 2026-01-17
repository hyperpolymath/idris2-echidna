; SPDX-License-Identifier: MPL-2.0
; STATE.scm - Project state tracking

(state
  (metadata
    (version "0.1.0")
    (schema-version "1.0")
    (created "2025-01-17")
    (updated "2025-01-17")
    (project "idris2-echidna")
    (repo "https://github.com/hyperpolymath/idris2-echidna"))

  (project-context
    (name "idris2-echidna")
    (tagline "Idris2 FFI bindings to ECHIDNA theorem proving platform")
    (tech-stack ("Idris2" "FFI" "ECHIDNA" "Rust")))

  (current-position
    (phase "scaffolding-complete")
    (overall-completion 45)
    (components
      (core-prover-interface 85)
      (z3-bindings 80)
      (cvc5-bindings 20)
      (lean-bindings 20)
      (coq-bindings 20)
      (agda-bindings 20)
      (isabelle-bindings 20)
      (hol-light-bindings 10)
      (mizar-bindings 10)
      (vampire-bindings 10)
      (eprover-bindings 10)
      (tlc-bindings 10)
      (alloy-bindings 10)
      (aspect-tagging 70)
      (neural-integration 15)
      (ffi-layer 40)
      (dyadt-integration 75)
      (cno-integration 75)
      (documentation 60))
    (working-features
      "Prover interface with 12 prover kinds"
      "ProverKind enumeration and tier system"
      "Theorem type with format support"
      "Z3 prover module with SMT-LIB helpers"
      "Aspect tagging system (MathDomain, ProofTechnique, Complexity)"
      "SMT-LIB builder (forall, exists, implies, equals)"
      "Dyadt claim verification integration"
      "CNO theorem generation and verification"
      "Session management with configuration"
      "Example proof workflows"))

  (route-to-mvp
    (milestone "M1: Core FFI" (status "in-progress")
      (items
        (item "Implement echidna C library bindings" (status "started"))
        (item "Test FFI with Z3" (status "pending"))
        (item "Add error handling" (status "partial"))))
    (milestone "M2: Full Prover Support" (status "pending")
      (items
        (item "Complete all 12 prover modules" (status "scaffolded"))
        (item "Add format translation" (status "pending"))
        (item "Add configuration options" (status "partial"))))
    (milestone "M3: Integration" (status "complete")
      (items
        (item "Integration with idris2-dyadt" (status "complete"))
        (item "Integration with idris2-cno" (status "complete"))
        (item "Documentation and examples" (status "complete"))))
    (milestone "M4: Production Ready" (status "pending")
      (items
        (item "Full test coverage" (status "pending"))
        (item "Performance benchmarks" (status "pending"))
        (item "CI/CD pipeline" (status "pending")))))

  (blockers-and-issues
    (critical ())
    (high
      (issue "Need ECHIDNA C library headers for FFI"
        (workaround "Using placeholder FFI signatures"))
      (issue "Need to test FFI on multiple platforms"
        (workaround "Targeting Linux first")))
    (medium
      (issue "JSON parsing for prover responses not implemented"
        (workaround "Using string-based responses"))
      (issue "Neural integration requires ECHIDNA neural module"
        (workaround "Stubbed for now"))))

  (critical-next-actions
    (immediate
      "Create C header file for FFI bindings"
      "Implement actual FFI calls to libechidna"
      "Add unit tests for Z3 module")
    (this-week
      "Test with actual ECHIDNA installation"
      "Complete CVC5 and Lean modules"
      "Add more SMT-LIB helper functions")
    (this-month
      "Complete all 12 prover bindings"
      "Add format translation layer"
      "Performance testing and optimization"))

  (session-history
    (session "2025-01-17-scaffold"
      (accomplishments
        "Created initial project structure"
        "Implemented Prover interface"
        "Added Z3 module with helpers"
        "Created aspect tagging system"
        "Added dyadt and cno integrations"))))
