; SPDX-License-Identifier: MPL-2.0
; ECOSYSTEM.scm - Project ecosystem positioning

(ecosystem
  (version "1.0")
  (name "idris2-echidna")
  (type "library")
  (purpose "Idris2 FFI bindings to ECHIDNA neurosymbolic theorem proving platform")

  (position-in-ecosystem
    "Bridge between Idris2's dependent type system and ECHIDNA's 12 theorem provers"
    "Central proving backend for the hyperpolymath Idris2 verification stack"
    "Enables external theorem proving when Idris2's type system is insufficient"
    "Provides unified API across SMT solvers, ITPs, and ATP systems")

  (ecosystem-diagram
    "
    ┌─────────────────────────────────────────────────────────────┐
    │                    User Applications                         │
    └─────────────────────────────────────────────────────────────┘
                                 │
         ┌───────────────────────┼───────────────────────┐
         ▼                       ▼                       ▼
    ┌─────────┐           ┌─────────────┐         ┌─────────┐
    │idris2-  │           │ idris2-     │         │idris2-  │
    │ dyadt   │◄─────────►│ echidna     │◄───────►│  cno    │
    │(claims) │           │ (provers)   │         │(CNOs)   │
    └─────────┘           └─────────────┘         └─────────┘
                                 │
                                 ▼
                         ┌─────────────┐
                         │  ECHIDNA    │
                         │   (Rust)    │
                         └─────────────┘
                                 │
         ┌──────────┬──────────┬┴───────────┬──────────┐
         ▼          ▼          ▼            ▼          ▼
       ┌───┐     ┌─────┐    ┌─────┐     ┌──────┐   ┌─────┐
       │Z3 │     │Lean4│    │ Coq │     │Agda  │   │+8   │
       └───┘     └─────┘    └─────┘     └──────┘   └─────┘
    ")

  (related-projects
    (echidna
      (relationship "upstream-dependency")
      (integration "FFI to libechidna.so")
      (description "The core theorem proving platform this binds to"))
    (idris2-dyadt
      (relationship "downstream-consumer")
      (integration "Echidna.Integration.Dyadt module")
      (description "Uses echidna to verify complex claims"))
    (idris2-cno
      (relationship "downstream-consumer")
      (integration "Echidna.Integration.CNO module")
      (description "Uses echidna to prove CNO properties"))
    (llm-verify
      (relationship "ecosystem-sibling")
      (integration "Same ECHIDNA backend")
      (description "Haskell equivalent using same proving backend"))
    (did-you-actually-do-that
      (relationship "conceptual-ancestor")
      (integration "Claim patterns inspired design")
      (description "Runtime verification that inspired compile-time approach"))
    (absolute-zero
      (relationship "proof-source")
      (integration "Can verify absolute-zero theorems")
      (description "Formal CNO proofs from multiple proof assistants")))

  (integration-points
    (provides
      "Prover interface for arbitrary theorem proving"
      "SMT-LIB builder for theorem construction"
      "Aspect tagging for proof categorization"
      "Multi-prover orchestration")
    (consumes
      "ECHIDNA library via FFI"
      "External prover installations"))

  (what-this-is
    "FFI bindings to ECHIDNA's 12 theorem provers"
    "Type-safe prover interface for Idris2"
    "Aspect tagging system for proof categorization"
    "SMT-LIB builder helpers for theorem construction"
    "Integration layer for dyadt claims and CNO proofs"
    "Session management for prover connections")

  (what-this-is-not
    "Not a standalone theorem prover (uses external provers)"
    "Not a replacement for native Idris2 proofs (complementary)"
    "Not a proof assistant GUI (library only)"
    "Not the provers themselves (bindings only)"))
