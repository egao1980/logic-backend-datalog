(defpackage #:logic-backend-datalog/tests
  (:use #:cl #:rove))

(in-package #:logic-backend-datalog/tests)

(deftest package-exists
  (ok (find-package :logic-backend-datalog)))
