(defsystem "logic-backend-datalog"
  :version "0.2.0"
  :description "Pure-Lisp Datalog backend for logic-protocol: semi-naive, incremental (DRed), stratified negation, time steps"
  :author "egao1980"
  :license "MIT"
  :depends-on ((:version "logic-protocol" "0.2.0"))
  :serial t
  :pathname "src"
  :components ((:file "package")
               (:file "backend"))
  :in-order-to ((test-op (test-op "logic-backend-datalog/tests"))))

(defsystem "logic-backend-datalog/tests"
  :description "logic-protocol's own tests and conformance suite on this backend, plus Datalog-specific tests: incremental cost, :AUTO = :REFERENCE equivalence, benchmarks"
  :depends-on ("logic-backend-datalog" "logic-protocol/tests" "logic-protocol/conformance"
               (:version "rove" "0.11.1"))
  :pathname "tests"
  :serial t
  :components ((:file "package")
               (:file "support")
               (:file "backend-test")
               (:file "incremental-cost-test")
               (:file "equivalence-test")
               (:file "perf-test"))
  :perform (test-op (o c)
             ;; One verdict for the slice: the protocol's tests (mock
             ;; backend), the conformance suite on this backend, this
             ;; repo's tests. Everything runs on the default evaluator
             ;; (:AUTO); the equivalence tests and benchmarks also run
             ;; :REFERENCE themselves.
             (let ((ok (progv (list (find-symbol* :*logic-backend* :logic-protocol))
                           (list (symbol-call :logic-backend-datalog :make-datalog-backend))
                         (symbol-call :rove :run
                                      (list "logic-protocol/tests" "logic-protocol/conformance" c)))))
               (unless ok
                 (error "tests failed for ~A" (component-name c))))))
