(in-package #:logic-backend-datalog/tests)

(deftest backend-identity
  (let ((b (make-datalog-backend)))
    (ok (typep b 'logic-backend))
    (ok (eq (backend-name b) :datalog))
    (ok (subsetp '(:stratified-negation :time-step :incremental) (backend-features b)))
    (ok (null (intersection '(:choice :constraint :unstratified-negation) (backend-features b))))))

(deftest loading-sets-the-default
  ;; Loading sets the global default; the test-op also binds one.
  (ok (typep *logic-backend* (quote datalog-backend)))
  (ok (typep (program-backend (make-program)) 'datalog-backend)))

(deftest asp-rules-are-refused
  (let ((p (make-program :backend (make-datalog-backend))))
    (ok (handler-case (progn (add-rule p '(rule (choice 1 1 (pick ?x)) :- (item ?x))) nil)
          (logic-unsupported-rule (c) (eq (logic-error-feature c) :choice))))
    (ok (handler-case (progn (add-rule p '(rule :- (pick ?x) (bad ?x))) nil)
          (logic-unsupported-rule (c) (eq (logic-error-feature c) :constraint))))
    (ok (handler-case (progn (add-rules p '((rule (p ?x) :- (d ?x) (not (q ?x)))
                                            (rule (q ?x) :- (d ?x) (not (p ?x)))))
                             nil)
          (logic-unstratifiable (c) (equal (logic-error-cycle c) '(p q)))))
    (ok (null (program-rules p)) "an abandoned ADD-RULES adds nothing")))

(deftest larger-closure
  (let* ((edges (loop for i from 0 below 200
                      collect (list 'edge i (mod (+ (* i 7) 3) 200))))
         (p (make-program :backend (make-datalog-backend)
                          :rules '((rule (path ?x ?y) :- (edge ?x ?y))
                                   (rule (path ?x ?z) :- (edge ?x ?y) (path ?y ?z)))
                          :facts edges
                          :budget :unlimited)))
    ;; i -> 7i+3 mod 200 is a permutation: every node is on a cycle, so it
    ;; reaches exactly the nodes of its own cycle.
    (ok (every (lambda (i) (holds-p p (list 'path i i))) '(0 1 2 50 199)))
    (ok (= (length (program-facts p :relation 'path))
           (loop for i from 0 below 200
                 sum (length (query p (list 'path i '?y))))))))
