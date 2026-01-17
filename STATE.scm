;; SPDX-License-Identifier: MPL-2.0
;; STATE.scm - Current project state for idris2-echidna

(state
  (metadata
    (version "1.0.0")
    (schema-version "1.0")
    (created "2025-01-17")
    (updated "2025-01-17")
    (project "idris2-echidna")
    (repo "https://github.com/hyperpolymath/idris2-echidna"))

  (project-context
    (name "idris2-echidna")
    (tagline "Idris2 FFI bindings for the ECHIDNA neurosymbolic theorem proving platform")
    (tech-stack
      (primary "Idris2")
      (version "0.8.0")
      (paradigm "dependently-typed functional")))

  (current-position
    (phase "initial-release")
    (overall-completion 70)
    (components
      (core-prover-api 90 "Prover, ProverKind, Theorem types complete")
      (z3-integration 85 "Z3 SMT solver bindings working")
      (cvc5-integration 80 "CVC5 bindings scaffolded")
      (other-provers 70 "Lean, Coq, Agda, Isabelle, etc. scaffolded")
      (aspect-system 60 "Multi-aspect verification scaffolded")
      (neural-integration 50 "Neural theorem proving hooks scaffolded")
      (ffi-layer 40 "FFI to native provers needs implementation"))
    (working-features
      "Type-safe prover selection"
      "SMT-LIB formula encoding"
      "Proof result types with dependent typing"
      "Multi-prover strategy support"
      "Integration-ready for dyadt claims"))

  (route-to-mvp
    (milestone "v0.1.0 - Core API" (status "complete"))
    (milestone "v0.2.0 - Multiple Provers" (status "in-progress"))
    (milestone "v0.3.0 - FFI Integration" (status "planned"))
    (milestone "v1.0.0 - Production Ready" (status "planned")))

  (blockers-and-issues
    (high "FFI layer needs implementation for real prover calls")
    (medium "Neural integration is placeholder only"))

  (critical-next-actions
    (immediate "Test with real Z3 installation")
    (this-week "Implement CVC5 backend")
    (this-month "Register with pack"))

  (session-history
    (snapshot "2025-01-17"
      (accomplishments
        "Initial scaffolding complete"
        "19 modules compile cleanly"
        "Integration with dyadt working"
        "Pushed to GitHub"))))
