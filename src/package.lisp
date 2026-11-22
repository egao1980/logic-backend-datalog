(defpackage #:logic-backend-datalog
  (:use #:cl #:logic-protocol)
  (:nicknames #:stack-logic-datalog)
  (:export #:datalog-backend #:make-datalog-backend))

(in-package #:logic-backend-datalog)

