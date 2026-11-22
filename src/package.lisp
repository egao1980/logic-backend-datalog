(defpackage #:logic-backend-datalog
  (:use #:cl #:logic-protocol)
  (:nicknames #:stack-logic-datalog)
  (:export #:datalog-backend #:make-datalog-backend))

(in-package #:logic-backend-datalog)

(define-condition logic0-pending (error)
  ((what :initarg :what :reader logic0-pending-what))
  (:report (lambda (c s)
             (format s "L0 contract stub not implemented: ~S" (logic0-pending-what c)))))

(defun %logic0-pending (what)
  "Contract stub. Every call site is replaced by the L0 implementation, then
this function and LOGIC0-PENDING are deleted."
  (error 'logic0-pending :what what))
