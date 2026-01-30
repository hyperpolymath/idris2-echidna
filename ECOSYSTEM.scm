;; SPDX-License-Identifier: PMPL-1.0-or-later
;; ECOSYSTEM.scm - Ecosystem relationships for idris2-echidna

(ecosystem
  (version "1.0.0")
  (name "idris2-echidna")
  (type "library")
  (purpose "Theorem prover bindings for Idris2 dependent type verification")

  (position-in-ecosystem
    (role "foundation")
    (layer "prover-interface")
    (description "Provides the interface between Idris2 code and external theorem provers"))

  (related-projects
    (project "idris2-dyadt"
      (relationship "consumer")
      (description "Uses echidna to verify dyadt claims with theorem provers"))

    (project "idris2-cno"
      (relationship "sibling")
      (description "Certified Null Operations - can use echidna for external verification"))

    (project "Z3"
      (relationship "external-dependency")
      (description "Microsoft's SMT solver - primary backend"))

    (project "CVC5"
      (relationship "external-dependency")
      (description "Stanford's SMT solver - alternative backend")))

  (what-this-is
    "Idris2 FFI bindings to theorem provers"
    "Type-safe prover invocation"
    "Multi-prover strategy support"
    "SMT-LIB formula encoding utilities")

  (what-this-is-not
    "A theorem prover itself"
    "A proof assistant"
    "A replacement for Idris2's built-in verification"))
