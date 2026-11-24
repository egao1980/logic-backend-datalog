(in-package #:logic-backend-datalog/tests)

;;; Helpers for the 0.2.0 equivalence tests and benchmarks: the backend's
;;; internal switches (src/backend.lisp, PERFORMANCE), a portable seeded
;;; generator, proofs as data, timing.

(defmacro with-strategy ((strategy) &body body)
  "Run BODY with the backend's evaluator set to STRATEGY (:AUTO or :REFERENCE)."
  `(let ((logic-backend-datalog::*strategy* ,strategy))
     ,@body))

(defmacro with-thresholds ((ratio minimum) &body body)
  "Run BODY with the set-at-a-time thresholds bound."
  `(let ((logic-backend-datalog::*set-at-a-time-ratio* ,ratio)
         (logic-backend-datalog::*set-at-a-time-minimum* ,minimum))
     ,@body))

(defun call-in-regime (regime thunk)
  "Call THUNK under :AUTO with REGIME's thresholds: :ALWAYS (every phase
set-at-a-time), :NEVER (every phase per fact), :DEFAULT (the shipped values)."
  (with-strategy (:auto)
    (ecase regime
      (:always (with-thresholds (0 1) (funcall thunk)))
      (:never (with-thresholds (nil nil) (funcall thunk)))
      (:default (funcall thunk)))))

(defmacro collecting-modes ((var) &body body)
  "Run BODY with VAR bound to a fresh list that collects every
(STRATUM PHASE MODE) the :AUTO maintenance reports, oldest first, through
LOGIC-BACKEND-DATALOG::*MODE-HOOK*. Returns the list."
  `(let ((,var '()))
     (let ((logic-backend-datalog::*mode-hook*
             (lambda (stratum phase mode) (push (list stratum phase mode) ,var))))
       ,@body)
     (nreverse ,var)))

;;; Seeded generator: a 31-bit LCG (the same numbers on every implementation).

(defun make-rng (seed)
  (let ((state (mod (+ (* seed 7919) 1) 2147483648)))
    (lambda (n)
      (setf state (mod (+ (* state 1103515245) 12345) 2147483648))
      (mod (ash state -8) n))))

(defun pick (rng list)
  (nth (funcall rng (length list)) list))

(defun chance (rng n)
  "True with probability 1/N."
  (zerop (funcall rng n)))

;;; Results as plain data, for exact comparison.

(defun proof-sexp (proof)
  (list (proof-fact proof)
        (and (proof-rule proof) (rule-form (proof-rule proof)))
        (mapcar #'proof-sexp (proof-premises proof))
        (proof-negated proof)
        (proof-builtins proof)
        (proof-bindings proof)))

(defun explanation-sexp (explanation)
  "A PROOF or a WHY-NOT as data."
  (if (typep explanation 'proof)
      (list :proof (proof-sexp explanation))
      (list :why-not (why-not-fact explanation)
            (mapcar (lambda (r) (list (rule-form (reason-rule r)) (reason-literal r) (reason-index r)))
                    (why-not-reasons explanation)))))

(defun delta-sexp (delta)
  (list (delta-added delta) (delta-removed delta)))

;;; Timing. CPU seconds; the best of several runs for the fast path, so that
;;; a ratio errs towards the slower side.

(defun seconds (thunk)
  (let ((start (get-internal-run-time)))
    (funcall thunk)
    (/ (float (- (get-internal-run-time) start) 1d0) internal-time-units-per-second)))

(defun best-seconds (runs thunk)
  (loop repeat runs minimize (seconds thunk)))

(defun report (name &rest pairs)
  "Print one benchmark line: NAME, then label / seconds pairs."
  (format t "~&  [bench] ~A:~{ ~A ~,4Fs~^,~}~%" name pairs)
  (finish-output))

(defun at-least-times-faster-p (slow fast factor)
  "Is FAST at least FACTOR times faster than SLOW? Times under a
millisecond count as one, so a timer tick cannot decide the outcome."
  (>= (max slow 0.001d0) (* factor (max fast 0.001d0))))
