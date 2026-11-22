(defsystem "logic-backend-datalog"
  :version "0.0.0"
  :description "Pure-Lisp Datalog backend for logic-protocol: semi-naive, incremental, stratified negation, time steps"
  :author "egao1980"
  :license "MIT"
  :depends-on ()
  :serial t
  :pathname "src"
  :components ((:file "package"))
  :in-order-to ((test-op (test-op "logic-backend-datalog/tests"))))

(defsystem "logic-backend-datalog/tests"
  :depends-on ("logic-backend-datalog" "rove")
  :pathname "tests"
  :serial t
  :components ((:file "package"))
  :perform (test-op (o c)
             (unless (symbol-call :rove :run c)
               (error "tests failed for ~A" (component-name c)))))
