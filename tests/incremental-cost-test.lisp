(in-package #:logic-backend-datalog/tests)

;;; Cost: an update charges in proportion to what it changes. Each budget
;;; here is far below the size of the model, so a backend that recomputes
;;; from scratch (at least one step per derived fact, ~1770 here) exceeds it.

(defparameter *chain* 60)

(defun chain-program ()
  (make-program :backend (make-datalog-backend)
                :rules '((rule (path ?x ?y) :- (edge ?x ?y))
                         (rule (path ?x ?z) :- (edge ?x ?y) (path ?y ?z)))
                :facts (loop for i from 1 below *chain* collect (list 'edge i (1+ i)))
                :budget :unlimited))

(defun fits-p (thunk)
  "Did THUNK finish without exceeding its budget?"
  (handler-case (progn (funcall thunk) t)
    (logic-budget-exceeded () nil)))

(deftest model-is-large
  (ok (= (length (program-facts (chain-program) :relation 'path))
         (/ (* *chain* (1- *chain*)) 2))))

(deftest unrelated-assert-is-cheap
  (let ((p (chain-program)))
    (ok (fits-p (lambda () (update p :assert '((value :email "a@b.c")) :budget 10))))
    (ok (fits-p (lambda () (update p :retract '((value :email "a@b.c")) :budget 10))))))

(deftest extend-chain-is-cheap
  (let ((p (chain-program)))
    (ok (fits-p (lambda () (assert-fact p (list 'edge *chain* (1+ *chain*)) :budget 500))))
    (ok (= (length (program-facts p :relation 'path))
           (/ (* (1+ *chain*) *chain*) 2)))))

(deftest retract-chain-end-is-cheap
  (let ((p (chain-program)))
    (ok (fits-p (lambda () (retract-fact p (list 'edge (1- *chain*) *chain*) :budget 1000))))
    (ok (= (length (program-facts p :relation 'path))
           (/ (* (1- *chain*) (- *chain* 2)) 2)))))

(deftest retract-chain-start-is-cheap
  (let ((p (chain-program)))
    (ok (fits-p (lambda () (retract-fact p '(edge 1 2) :budget 1000))))
    (ok (not (holds-p p '(path 1 3))))))

(deftest ground-query-is-cheap
  (let ((p (chain-program)))
    (ok (fits-p (lambda () (holds-p p (list 'path 1 *chain*) :budget 10))))))

(deftest assumed-request-is-cheap
  ;; The L1 path: a request asserted for one query and withdrawn.
  (let ((p (chain-program)))
    (add-rule p '(rule (allowed ?who) :- (request ?who) (member ?who)) :budget :unlimited)
    (update p :assert '((member "ann")) :budget :unlimited)
    (ok (fits-p (lambda () (holds-p p '(allowed "ann") :assume '((request "ann")) :budget 50))))
    (ok (holds-p p '(allowed "ann") :assume '((request "ann"))))
    (ok (not (holds-p p '(allowed "ann"))))))
