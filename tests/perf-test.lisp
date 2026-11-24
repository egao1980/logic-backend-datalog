(in-package #:logic-backend-datalog/tests)

;;; Benchmarks (0.2.0) as soft tests. Each prints its times ("[bench]"
;;; lines) and asserts a generous ratio against the :REFERENCE evaluator or
;;; between two orders of the same work, never an absolute time, so a slow
;;; machine or implementation does not fail them. The bounds sit well under
;;; the speedups a throwaway reference implementation measured on SBCL and
;;; on ECL (see the PR); ECL's are the tighter ones.

(defun bench-symbol (format-control &rest args)
  (intern (apply #'format nil format-control args) '#:logic-backend-datalog/tests))

;;; Issue #4: 5k facts x 20 rules, facts-then-rules vs rules-then-facts.

(defun bulk-facts ()
  "5000 facts: R1..R5 of arity 4, 1000 each. (Rk X Y A B) with Y = X + k
(mod 1000), A = X mod 3, B = X mod 4."
  (loop for k from 1 to 5
        for rel = (bench-symbol "R~D" k)
        nconc (loop for x below 1000
                    collect (list rel x (mod (+ x k) 1000) (mod x 3) (mod x 4)))))

(defun bulk-rules ()
  "20 rules: 16 chains of 4 to 6 atoms over R1..R5, two joins of chains, two
negations (a second and a third stratum)."
  (append
   (loop for i below 16
         collect (let ((n (+ 4 (mod i 3))))
                   `(rule (,(bench-symbol "C~D" i) ?l0 ,(bench-symbol "?L~D" n))
                          :- ,@(loop for a below n
                                     collect (list (bench-symbol "R~D" (1+ (mod (+ i a) 5)))
                                                   (bench-symbol "?L~D" a) (bench-symbol "?L~D" (1+ a))
                                                   (bench-symbol "?A~D" a) (bench-symbol "?B~D" a))))))
   (list `(rule (pair ?x ?z) :- (,(bench-symbol "C0") ?x ?y) (,(bench-symbol "C1") ?y ?z))
         `(rule (pair ?x ?z) :- (,(bench-symbol "C2") ?x ?y) (,(bench-symbol "C3") ?y ?z))
         `(rule (gap ?x) :- (,(bench-symbol "R1") ?x ?y ?a ?b) (not (,(bench-symbol "C4") ?x ?y)))
         `(rule (odd ?x) :- (,(bench-symbol "C5") ?x ?y) (not (pair ?x ?y))))))

(defun facts-then-rules (facts rules)
  (let ((p (make-program :facts facts :budget :unlimited)))
    (add-rules p rules :budget :unlimited)
    p))

(defun rules-then-facts (facts rules)
  (make-program :rules rules :facts facts :budget :unlimited))

(deftest bench-bulk-load-order
  (let* ((facts (bulk-facts))
         (rules (bulk-rules))
         (ref-p nil)
         (auto-p nil)
         (ref-ftr (with-strategy (:reference)
                    (seconds (lambda () (setf ref-p (facts-then-rules facts rules))))))
         (ref-rtf (with-strategy (:reference) (seconds (lambda () (rules-then-facts facts rules)))))
         (ftr (with-strategy (:auto) (best-seconds 3 (lambda () (facts-then-rules facts rules)))))
         (rtf (with-strategy (:auto)
                (best-seconds 3 (lambda () (setf auto-p (rules-then-facts facts rules)))))))
    (report "5k facts x 20 rules"
            "reference facts-then-rules" ref-ftr "reference rules-then-facts" ref-rtf
            "auto facts-then-rules" ftr "auto rules-then-facts" rtf)
    (ok (= (length rules) 20) "20 rules")
    (ok (= (length facts) 5000) "5000 facts")
    (ok (equal (program-facts ref-p) (program-facts auto-p))
        "the same model in either order and on either evaluator")
    (ok (<= rtf (+ (* 2 ftr) 0.01d0))
        "rules-then-facts costs at most twice facts-then-rules (set-at-a-time)")
    (ok (at-least-times-faster-p ref-rtf rtf 2.5d0)
        "rules-then-facts at least 2.5x faster than the per-fact reference")))

;;; Join order: three relations, the first atom a large unbound table.

(defun join-facts ()
  (append (loop for i below 20000 collect (list 'big (mod i 2000) i))
          (loop for i below 20000 collect (list 'mid i (mod (* i 3) 97)))
          (loop for i below 10 collect (list 'small (* i 7)))))

(defparameter *join-rule* '(rule (hit ?x ?z) :- (big ?x ?y) (mid ?y ?z) (small ?x)))

(defun join-work (program)
  "ADD-RULE of *JOIN-RULE*, then its body as a query, ten times."
  (add-rule program *join-rule* :budget :unlimited)
  (dotimes (i 10)
    (query program '(and (big ?x ?y) (mid ?y ?z) (small ?x)) :budget :unlimited)))

(deftest bench-large-unbound-first-atom
  (let* ((facts (join-facts))
         (ref-p (with-strategy (:reference) (make-program :facts facts :budget :unlimited)))
         (auto-p (with-strategy (:auto) (make-program :facts facts :budget :unlimited)))
         (reference (with-strategy (:reference) (seconds (lambda () (join-work ref-p)))))
         (auto (with-strategy (:auto)
                 (+ (seconds (lambda () (add-rule auto-p *join-rule* :budget :unlimited)))
                    (best-seconds 3 (lambda ()
                                      (dotimes (i 10)
                                        (query auto-p '(and (big ?x ?y) (mid ?y ?z) (small ?x))
                                               :budget :unlimited))))))))
    (report "big x mid x small" "reference" reference "auto" auto)
    (ok (equal (program-facts ref-p :relation 'hit) (program-facts auto-p :relation 'hit)))
    (ok (= (length (program-facts ref-p :relation 'hit)) 100))
    (ok (at-least-times-faster-p reference auto 5)
        "the join starts from the small table, at least 5x faster")))

;;; EXPLAIN of a height-4 fact in a 20-rule program, after a write (so
;;; nothing is cached).

(defun narrow-facts (&optional (n 1000))
  (append (loop for i below n collect (list 'node i))
          (loop for i below n
                nconc (list (list 'edge i (mod (+ (* i 7) 1) n))
                            (list 'edge i (mod (+ (* i 11) 2) n))))
          (loop for i below n collect (list 'color i (mod i 5)))
          (loop for i below n collect (list 'weight i (mod (* i 13) 100)))))

(defparameter *narrow-rules*
  '((rule (succ2 ?a ?c) :- (edge ?a ?b) (edge ?b ?c))
    (rule (same-color ?a ?b) :- (edge ?a ?b) (color ?a ?c) (color ?b ?c))
    (rule (heavy ?a) :- (weight ?a ?w) (> ?w 50))
    (rule (light ?a) :- (node ?a) (not (heavy ?a)))
    (rule (heavy-edge ?a ?b) :- (edge ?a ?b) (heavy ?a) (heavy ?b))
    (rule (colored-succ ?a ?c) :- (succ2 ?a ?b) (color ?b ?c))
    (rule (red ?a) :- (color ?a 0))
    (rule (red-reach ?a) :- (red ?a) (heavy ?a))
    (rule (red-reach ?b) :- (red-reach ?a) (edge ?a ?b))
    (rule (hub ?a) :- (edge ?a ?b) (edge ?c ?a) (/= ?b ?c))
    (rule (sink ?a) :- (node ?a) (not (hub ?a)))
    (rule (w-edge ?a ?b ?w) :- (edge ?a ?b) (weight ?b ?w))
    (rule (cheap ?a ?b) :- (w-edge ?a ?b ?w) (< ?w 10))
    (rule (pair-color ?c1 ?c2) :- (edge ?a ?b) (color ?a ?c1) (color ?b ?c2))
    (rule (light-red ?a) :- (light ?a) (red ?a))
    (rule (level1 ?a ?b) :- (cheap ?a ?b) (heavy ?a))
    (rule (level2 ?a ?c) :- (level1 ?a ?b) (edge ?b ?c))
    (rule (level3 ?a ?d) :- (level2 ?a ?c) (edge ?c ?d))
    (rule (mid ?a) :- (weight ?a ?w) (>= ?w 25) (< ?w 75))
    (rule (mid-sink ?a) :- (mid ?a) (sink ?a))))

(defun cold-explain (program fact)
  "EXPLAIN FACT after a write that drops every cache."
  (update program :assert '((scratch 1)) :budget :unlimited)
  (update program :retract '((scratch 1)) :budget :unlimited)
  (explain program fact))

(deftest bench-explain-four-level-proof
  (let* ((ref-p (with-strategy (:reference)
                  (make-program :rules *narrow-rules* :facts (narrow-facts) :budget :unlimited)))
         (auto-p (with-strategy (:auto)
                   (make-program :rules *narrow-rules* :facts (narrow-facts) :budget :unlimited)))
         (fact (first (program-facts ref-p :relation 'level2)))
         (reference (with-strategy (:reference) (seconds (lambda () (cold-explain ref-p fact)))))
         (auto (with-strategy (:auto) (best-seconds 3 (lambda () (cold-explain auto-p fact))))))
    (report "explain, height 4, 20 rules" "reference" reference "auto" auto)
    (ok (= (proof-height (with-strategy (:auto) (explain auto-p fact))) 4))
    (ok (equal (proof-sexp (with-strategy (:reference) (explain ref-p fact)))
               (proof-sexp (with-strategy (:auto) (explain auto-p fact)))))
    (ok (at-least-times-faster-p reference auto 4)
        "least heights without re-solving every rule at every height, at least 4x faster")))

;;; Issue #5: 40 rules of 20 variables and 8 atoms over 5k facts of arity 10.

(defun wide-facts ()
  "5250 facts: W1..W5 of arity 10, 1050 each. (Wk X Y :C X%3 :D X%5 :E X%7
X%2 :F) with Y = X + 210k (mod 1050), which keeps X mod 2, 3, 5 and 7, so
attribute variables shared along a chain stay consistent."
  (loop for k from 1 to 5
        for rel = (bench-symbol "W~D" k)
        nconc (loop for x below 1050
                    collect (list rel x (mod (+ x (* 210 k)) 1050)
                                  :c (mod x 3) :d (mod x 5) :e (mod x 7) (mod x 2) :f))))

(defun wide-rules (&optional (count 40))
  "COUNT rules, each a chain of 8 atoms over W1..W5 with 20 variables: 9
links, 4 shared attributes, 7 attributes of their own."
  (loop for r below count
        collect `(rule (,(bench-symbol "OUT~D" (mod r 10)) ?l0 ?l8 ?m3)
                   :- ,@(loop for a below 8
                              collect (list (bench-symbol "W~D" (1+ (mod (+ r a) 5)))
                                            (bench-symbol "?L~D" a) (bench-symbol "?L~D" (1+ a))
                                            :c '?m3 :d '?m5 :e '?m7
                                            (if (zerop a) '?m2 (bench-symbol "?F~D" a))
                                            :f)))))

(deftest bench-wide-rules
  (let* ((facts (wide-facts))
         (rules (wide-rules))
         (ref-p (with-strategy (:reference) (make-program :facts facts :budget :unlimited)))
         (auto-ps (with-strategy (:auto)
                    (loop repeat 3 collect (make-program :facts facts :budget :unlimited))))
         (reference (with-strategy (:reference)
                      (seconds (lambda () (add-rules ref-p rules :budget :unlimited)))))
         (auto (with-strategy (:auto)
                 (loop for p in auto-ps
                       minimize (seconds (lambda () (add-rules p rules :budget :unlimited)))))))
    (report "40 rules x 20 variables x 8 atoms, 5k facts" "reference" reference "auto" auto)
    (ok (every (lambda (r) (and (= (length (atom-variables r)) 20)
                                (= (length (cdddr r)) 8)))
               rules))
    (ok (equal (program-facts ref-p) (program-facts (first auto-ps))))
    (ok (= (length (program-facts ref-p)) (+ 5250 (* 10 1050))) "ten chains of 1050 answers")
    (ok (at-least-times-faster-p reference auto 2)
        "compiled rules and vector environments, at least 2x faster")))

;;; Retracting a whole relation that a higher stratum joins (over-delete).

(defparameter *retract-rules*
  '((rule (blocked ?c) :- (node ?c) (color ?c 3))
    (rule (x2 ?a ?b) :- (edge ?a ?b) (edge ?b ?c) (not (blocked ?c)))))

(defun retract-cycle (program edges)
  "(values RETRACT-SECONDS ASSERT-SECONDS) for retracting EDGES and asserting
them again."
  (values (seconds (lambda () (update program :retract edges :budget :unlimited)))
          (seconds (lambda () (update program :assert edges :budget :unlimited)))))

(deftest bench-bulk-retract
  (let* ((facts (narrow-facts 2000))
         (edges (remove 'edge facts :key #'car :test-not #'eq))
         (ref-p (with-strategy (:reference)
                  (make-program :rules *retract-rules* :facts facts :budget :unlimited)))
         (auto-p (with-strategy (:auto)
                   (make-program :rules *retract-rules* :facts facts :budget :unlimited))))
    (multiple-value-bind (ref-retract ref-assert)
        (with-strategy (:reference) (retract-cycle ref-p edges))
      (let ((runs (with-strategy (:auto)
                    (loop repeat 3 collect (multiple-value-list (retract-cycle auto-p edges))))))
        (let ((retract (reduce #'min runs :key #'first))
              (assert (reduce #'min runs :key #'second)))
          (report "retract 4000 edges under a negation stratum"
                  "reference retract" ref-retract "reference assert" ref-assert
                  "auto retract" retract "auto assert" assert)
          (ok (equal (program-facts ref-p) (program-facts auto-p)))
          (ok (<= retract (+ (* 4 assert) 0.01d0))
              "a bulk retraction costs about what the bulk assertion costs")
          (ok (at-least-times-faster-p ref-retract retract 5)
              "at least 5x faster than the reference over-delete"))))))
