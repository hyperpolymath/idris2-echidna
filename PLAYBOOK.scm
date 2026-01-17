;; SPDX-License-Identifier: MPL-2.0
;; PLAYBOOK.scm - Operational runbook for idris2-echidna

(define-module (idris2-echidna playbook)
  #:export (derivation-source procedures alerts))

(define derivation-source
  '((type . "derived")
    (meta-rules . (adr-001 adr-002 adr-003))
    (state-context . "v0.1.0-released")
    (timestamp . "2025-01-17T20:00:00Z")))

(define procedures
  '((build
     (description . "Build the idris2-echidna package")
     (steps
       ((step 1) (action . "idris2 --build idris2-echidna.ipkg") (timeout . 300))
       ((step 2) (action . "idris2 --check tests/TestProver.idr") (timeout . 120)))
     (on-failure . "abort-and-notify"))

    (install
     (description . "Install to local Idris2 package path")
     (preconditions . ("build-successful"))
     (steps
       ((step 1) (action . "idris2 --install idris2-echidna.ipkg") (timeout . 120)))
     (on-failure . "abort"))

    (test
     (description . "Run compile-time verification tests")
     (steps
       ((step 1) (action . "idris2 --check tests/TestProver.idr") (timeout . 180)))
     (on-failure . "report-failure"))

    (pack-install
     (description . "Install using pack package manager")
     (steps
       ((step 1) (action . "pack install idris2-echidna") (timeout . 600)))
     (on-failure . "abort-and-notify"))))

(define alerts
  '((build-failure
     (severity . "high")
     (channels . ("log"))
     (message . "idris2-echidna build failed"))))
