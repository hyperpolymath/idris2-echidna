;; SPDX-License-Identifier: MPL-2.0
;; NEUROSYM.scm - Symbolic semantics for idris2-echidna

(define-module (idris2-echidna neurosym)
  #:export (operation-definitions proof-obligations composition-rules))

(define operation-definitions
  '((theorem-construct
     (forward-semantics . "Create a Theorem from statement and format")
     (inverse . #f)
     (claim-type . "verified")
     (entropy-contribution . 2)
     (idris-type . "String -> TheoremFormat -> Theorem"))

    (prove
     (forward-semantics . "Submit theorem to prover and await result")
     (inverse . #f)
     (claim-type . "unverified")
     (entropy-contribution . 15)
     (idris-type . "Prover p => Theorem -> IO (Either ProverError ProofResult)")
     (note . "Result depends on external prover - unverified until checked"))

    (verify-proof
     (forward-semantics . "Check ProofResult status")
     (inverse . #f)
     (claim-type . "verified")
     (entropy-contribution . 1)
     (idris-type . "ProofResult -> Bool"))

    (encode-smt-lib
     (forward-semantics . "Encode claim as SMT-LIB formula")
     (inverse . "parse-smt-lib")
     (claim-type . "verified")
     (entropy-contribution . 3)
     (idris-type . "Claim -> String"))))

(define proof-obligations
  '((prover-soundness
     (description . "Prover results must be consistent with proof theory")
     (verification-method . "external-prover-guarantee")
     (failure-action . "downgrade-to-unverified"))

    (format-validity
     (description . "Theorem format must be supported by target prover")
     (verification-method . "supportsFormat check")
     (failure-action . "reject-operation"))

    (result-integrity
     (description . "ProofResult must faithfully represent prover output")
     (verification-method . "type-level-encoding")
     (failure-action . "downgrade-to-unverified"))))

(define composition-rules
  '((sequential
     (rule . "weakest-claim-wins")
     (example . "prove >>= verify: unverified (from prove)"))
    (parallel
     (rule . "weakest-claim-wins")
     (example . "prove-with-z3 ||| prove-with-cvc5: unverified"))
    (conditional
     (rule . "branch-specific")
     (example . "if proven then verified else unverified"))))
