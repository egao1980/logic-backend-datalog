(in-package #:logic-backend-datalog/tests)

;;; Equivalence (0.2.0). Random stratified programs (several relations,
;;; recursion, negation over lower strata, built-ins, = bindings, base facts
;;; in derived relations, :NEXT rules) and random operation sequences (fact
;;; batches of random size asserted and retracted, rules added to a populated
;;; program, ticks). Two programs run the same sequence, one under
;;; :REFERENCE (the 0.1.0 evaluator) and one under :AUTO in a threshold
;;; regime (always set-at-a-time, never, the shipped defaults). After every
;;; operation the delta, the model, the base facts and EXPLAIN (proofs of
;;; every fact of the model, why-not traces of absent atoms) must be
;;; identical.

(defparameter *base-relations* '((b0 1) (b1 2) (b2 2)))

(defparameter *derived-relations* '((d1 1 1) (d2 2 2) (d3 1 3) (d4 2 4) (d5 2 5))
  "(NAME ARITY LEVEL). A rule for a relation of level L reads relations of
level <= L positively (so recursion) and of level < L under NOT, so every
program is stratifiable.")

(defparameter *pool* '(?a ?b ?c ?d))

(defparameter *domain* 6)

(defparameter *next-rules*
  '((rule (next (b0 ?x)) :- (d1 ?x))
    (rule (next (b1 ?x ?y)) :- (b1 ?x ?y) (not (d3 ?x)))
    (rule (next (b2 ?x ?y)) :- (b2 ?y ?x))))

(defun relation-names ()
  (append (mapcar #'first *base-relations*) (mapcar #'first *derived-relations*)))

(defun relation-level (name)
  (if (assoc name *base-relations*) 0 (third (assoc name *derived-relations*))))

(defun relation-arity (name)
  (second (or (assoc name *base-relations*) (assoc name *derived-relations*))))

(defun random-constant (rng)
  (1+ (funcall rng *domain*)))

(defun random-term (rng vars)
  (if (or (null vars) (chance rng 6)) (random-constant rng) (pick rng vars)))

(defun random-atom (rng relations)
  (let ((r (pick rng relations)))
    (cons r (loop repeat (relation-arity r)
                  collect (if (chance rng 8) (random-constant rng) (pick rng *pool*))))))

(defun shuffle (rng list)
  (let ((v (coerce list 'vector)))
    (loop for i from (1- (length v)) downto 1
          do (rotatef (aref v i) (aref v (funcall rng (1+ i)))))
    (coerce v 'list)))

(defun random-rule (rng head)
  "A safe rule for HEAD (NAME ARITY LEVEL), body literals in random order."
  (destructuring-bind (name arity level) head
    (let* ((lower (remove-if-not (lambda (r) (< (relation-level r) level)) (relation-names)))
           (upto (remove-if-not (lambda (r) (<= (relation-level r) level)) (relation-names)))
           (positive (cons (random-atom rng lower)
                           (loop repeat (funcall rng 3) collect (random-atom rng upto))))
           (vars (atom-variables positive))
           (extra '()))
      (when (and vars (chance rng 3))
        (let ((r (pick rng lower)))
          (push `(not (,r ,@(loop repeat (relation-arity r) collect (random-term rng vars))))
                extra)))
      (when (and (cdr vars) (chance rng 4))
        (push (list (pick rng '(/= < <=)) (pick rng vars) (pick rng vars)) extra))
      (when (and vars (chance rng 5))
        (push (list '= '?e (random-term rng vars)) extra)
        (setf vars (append vars '(?e))))
      `(rule (,name ,@(loop repeat arity collect (random-term rng vars)))
         :- ,@(shuffle rng (append positive extra))))))

(defun random-program-rules (rng)
  "One or two rules per derived relation, a closure step for some binary
ones (deep recursion, cycles), sometimes a rule without positive atoms, in
random order."
  (let ((rules (loop for head in *derived-relations*
                     nconc (loop repeat (1+ (funcall rng 2)) collect (random-rule rng head))
                     when (and (= (second head) 2) (chance rng 2))
                       collect (let ((step (pick rng (remove-if-not
                                                      (lambda (r) (and (= (relation-arity r) 2)
                                                                       (< (relation-level r) (third head))))
                                                      (relation-names)))))
                                 `(rule (,(first head) ?a ?c) :- (,(first head) ?a ?b) (,step ?b ?c))))))
    (when (chance rng 3)
      (push `(rule (d1 ,(random-constant rng)) :- (not (b0 ,(random-constant rng)))) rules))
    (shuffle rng rules)))

(defun random-fact (rng)
  (let ((r (if (chance rng 10)
               (first (pick rng *derived-relations*))
               (first (pick rng *base-relations*)))))
    (cons r (loop repeat (relation-arity r) collect (random-constant rng)))))

(defun random-batch (rng size)
  (loop repeat size collect (random-fact rng)))

(defun random-retraction (rng base)
  "Some of the base facts BASE: none, a few, a random share, or all of one
relation."
  (when base
    (case (funcall rng 6)
      ((0 1) '())
      (2 (list (pick rng base)))
      (3 (loop repeat (1+ (funcall rng 5)) collect (pick rng base)))
      (4 (remove-if (lambda (f) (declare (ignore f)) (chance rng 2)) base))
      (t (let ((r (car (pick rng base))))
           (remove r base :key #'car :test-not #'eq))))))

(defun absent-atoms (rng program count)
  "COUNT random ground atoms of derived relations that do not hold in
PROGRAM (asked under :REFERENCE)."
  (with-strategy (:reference)
    (loop repeat (* 4 count)
          for r = (first (pick rng *derived-relations*))
          for a = (cons r (loop repeat (relation-arity r) collect (random-constant rng)))
          unless (holds-p program a)
            collect a into out
          when (>= (length out) count) return out
          finally (return out))))

(defun same-explanations-p (reference auto regime facts)
  "Do REFERENCE (under :REFERENCE) and AUTO (under REGIME) explain every one
of FACTS the same way, in that order? Returns the first fact that differs,
or NIL."
  (dolist (f facts nil)
    (let ((a (with-strategy (:reference) (explanation-sexp (explain reference f))))
          (b (call-in-regime regime (lambda () (explanation-sexp (explain auto f))))))
      (unless (equal a b)
        (return (list f :reference a :auto b))))))

(defun check-equivalence (seed regime &key (steps 14))
  "Run one random program and operation sequence on both evaluators.
Returns NIL when everything agrees, else a description of the first
difference."
  (let* ((rng (make-rng seed))
         (rules (random-program-rules rng))
         (next (and (chance rng 3) *next-rules*))
         (split (funcall rng (1+ (length rules))))
         (initial (append (subseq rules 0 split) next))
         (pending (subseq rules split))
         (facts (random-batch rng (funcall rng 30)))
         (reference (with-strategy (:reference)
                      (make-program :rules initial :facts facts :budget :unlimited)))
         (auto (call-in-regime regime
                               (lambda () (make-program :rules initial :facts facts :budget :unlimited)))))
    (loop for step from 0 to steps
          do (let* ((op (cond ((zerop step) '(:start))
                              ((and pending (chance rng 5))
                               (let ((n (1+ (funcall rng (min 2 (length pending))))))
                                 (prog1 (list :add-rules (subseq pending 0 n))
                                   (setf pending (nthcdr n pending)))))
                              ((and next (chance rng 5)) '(:tick))
                              (t (let ((base (program-base-facts reference)))
                                   (list :update
                                         (random-batch rng (pick rng '(0 1 1 2 3 5 8 20 40)))
                                         (random-retraction rng base))))))
                    (run (lambda (program)
                           (ecase (first op)
                             (:start nil)
                             (:add-rules (add-rules program (second op) :budget :unlimited))
                             (:tick (tick program :budget :unlimited))
                             (:update (update program :assert (second op) :retract (third op)
                                                      :budget :unlimited)))))
                    (d1 (with-strategy (:reference) (funcall run reference)))
                    (d2 (call-in-regime regime (lambda () (funcall run auto)))))
               (flet ((fail (what &rest details)
                        (return-from check-equivalence
                          (list* :step step :op (first op) what details))))
                 (unless (equal (and d1 (delta-sexp d1)) (and d2 (delta-sexp d2)))
                   (fail :delta :reference (delta-sexp d1) :auto (delta-sexp d2)))
                 (let ((m1 (program-facts reference)) (m2 (program-facts auto)))
                   (unless (equal m1 m2)
                     (fail :model :reference m1 :auto m2))
                   (unless (equal (program-base-facts reference) (program-base-facts auto))
                     (fail :base-facts))
                   (let ((bad (same-explanations-p reference auto regime
                                                   (shuffle rng (append m1 (absent-atoms rng reference 6))))))
                     (when bad (fail :explain bad)))))))
    nil))

(deftest-parametrize auto-equals-reference
    ((seed regime)
     (1 :always) (1 :never) (1 :default)
     (2 :always) (2 :never) (2 :default)
     (3 :always) (3 :never) (3 :default)
     (4 :always) (4 :never) (4 :default)
     (5 :always) (5 :never) (5 :default)
     (6 :always) (6 :never) (6 :default)
     (7 :always) (7 :never) (7 :default)
     (8 :always) (8 :never) (8 :default)
     (9 :always) (9 :never) (9 :default)
     (10 :always) (10 :never) (10 :default)
     (11 :always) (11 :never) (11 :default)
     (12 :always) (12 :never) (12 :default))
  (let ((failure (check-equivalence seed regime)))
    (ok (null failure) (format nil "seed ~D, ~S: ~S" seed regime failure))))

(deftest auto-equals-reference-on-a-bulk-cycle
  ;; Load everything at once, retract everything at once, load it again:
  ;; the bulk paths in both directions, plus EXPLAIN after each.
  (let* ((rng (make-rng 77))
         (rules (random-program-rules rng))
         (facts (random-batch rng 60)))
    (dolist (regime '(:always :never :default))
      (let ((reference (with-strategy (:reference) (make-program :rules rules :budget :unlimited)))
            (auto (call-in-regime regime (lambda () (make-program :rules rules :budget :unlimited)))))
        (dolist (op (list (list facts '()) (list '() facts) (list facts '())))
          (let ((d1 (with-strategy (:reference)
                      (update reference :assert (first op) :retract (second op) :budget :unlimited)))
                (d2 (call-in-regime regime
                                    (lambda ()
                                      (update auto :assert (first op) :retract (second op)
                                                   :budget :unlimited)))))
            (ok (equal (delta-sexp d1) (delta-sexp d2)) (format nil "~S: same delta" regime))
            (ok (equal (program-facts reference) (program-facts auto)) (format nil "~S: same model" regime))
            (ok (null (same-explanations-p reference auto regime (reverse (program-facts reference))))
                (format nil "~S: same proofs" regime))))))))

;;; The switch and the thresholds

(deftest default-strategy-is-auto
  (ok (eq logic-backend-datalog::*strategy* :auto)
      "0.2.0 runs the :AUTO evaluator unless a caller binds *STRATEGY*"))

(deftest strategy-is-checked
  (ok (signals (with-strategy (:fastest) (make-program :facts '((a 1)) :budget :unlimited))
               'type-error)))

(defparameter *mode-rules*
  '((rule (path2 ?x ?z) :- (edge ?x ?y) (edge ?y ?z))
    (rule (looped ?x) :- (path2 ?x ?x))
    (rule (open ?x) :- (node ?x) (not (looped ?x)))))

(defun mode-facts (&optional (n 1000))
  (append (loop for i below n collect (list 'node i))
          (loop for i below n
                nconc (list (list 'edge i (mod (+ i 1) n)) (list 'edge i (mod (+ (* 3 i) 2) n))))))

(defun mode-run ()
  "Bulk load, one fact, bulk retract."
  (let ((p (make-program :rules *mode-rules* :budget :unlimited)))
    (update p :assert (mode-facts) :budget :unlimited)
    (update p :assert '((edge 0 5000)) :budget :unlimited)
    (update p :retract (remove 'edge (mode-facts) :key #'car :test-not #'eq) :budget :unlimited)
    p))

(deftest modes-follow-the-thresholds
  (let ((always (call-in-regime :always (lambda () (collecting-modes (m) (mode-run)))))
        (never (call-in-regime :never (lambda () (collecting-modes (m) (mode-run))))))
    (ok (and always (every (lambda (m) (eq (third m) :set-at-a-time)) always))
        "ratio 0, minimum 1: every phase set-at-a-time")
    (ok (and never (every (lambda (m) (eq (third m) :per-fact)) never))
        "no thresholds: every phase per fact")
    (ok (equal (mapcar #'butlast always) (mapcar #'butlast never))
        "the same stratum phases are reported in both regimes")
    (ok (member :over-delete always :key #'second))
    (ok (member :insert always :key #'second))))

(deftest default-thresholds-choose-by-size
  (with-strategy (:auto)
    (let* ((p (make-program :rules *mode-rules* :budget :unlimited))
           (edges (remove 'edge (mode-facts) :key #'car :test-not #'eq))
           (load (collecting-modes (m) (update p :assert (mode-facts) :budget :unlimited)))
           (one (collecting-modes (m) (update p :assert '((edge 0 5000)) :budget :unlimited)))
           (bulk-retract (collecting-modes (m) (update p :retract edges :budget :unlimited))))
      (ok (member '(0 :insert :set-at-a-time) load :test #'equal) "a bulk load is set-at-a-time")
      (ok (member '(0 :insert :per-fact) one :test #'equal) "one fact into a large relation is per fact")
      (ok (notany (lambda (m) (eq (third m) :set-at-a-time)) one))
      (ok (member '(0 :over-delete :set-at-a-time) bulk-retract :test #'equal)
          "retracting a whole relation over-deletes set-at-a-time"))))

(deftest reference-reports-no-modes
  (ok (null (with-strategy (:reference) (collecting-modes (m) (mode-run))))
      "*MODE-HOOK* belongs to :AUTO"))
