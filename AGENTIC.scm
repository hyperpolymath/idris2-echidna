;; SPDX-License-Identifier: MPL-2.0
;; AGENTIC.scm - AI agent gating policies for idris2-echidna

(define-module (idris2-echidna agentic)
  #:export (gating-policies entropy-budgets risk-classifications))

(define gating-policies
  '((default
     (mode . "strict")
     (require-explicit-intent . #t)
     (description . "Prover bindings require careful handling"))

    (prover-invocation
     (mode . "gated")
     (require-explicit-intent . #t)
     (description . "External prover calls require user confirmation")
     (reason . "Provers may have long execution times or resource usage"))

    (ffi-operations
     (mode . "strict")
     (require-explicit-intent . #t)
     (description . "FFI calls to native provers are gated")
     (reason . "Native code execution requires explicit approval"))))

(define entropy-budgets
  '((session
     (max-entropy . 100)
     (current . 0)
     (reset-on . "session-end"))
    (operation-costs
     (prover-call . 15)
     (theorem-construct . 2)
     (proof-verify . 5)
     (ffi-call . 25)
     (file-read . 1))))

(define risk-classifications
  '((low
     (operations . ("theorem-construct" "format-check" "api-exploration"))
     (auto-approve . #t))
    (medium
     (operations . ("prover-call" "proof-verify"))
     (require-confirmation . #f)
     (log-decision . #t))
    (high
     (operations . ("ffi-call" "external-process"))
     (require-confirmation . #t)
     (log-decision . #t))))
