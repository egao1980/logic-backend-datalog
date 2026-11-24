(in-package #:logic-backend-datalog)

;;; The default logic-protocol backend: pure Lisp, no dependencies.
;;;
;;; Normative for L0 (the brief's locked decisions plus this contract), and
;;; PERFORMANCE for 0.2.0 (issues #4 and #5):
;;;
;;; - EVALUATION. Bottom-up, stratum by stratum in the order of
;;;   LOGIC-PROTOCOL:STRATIFY over the program's :NORMAL rules. Within a
;;;   stratum, semi-naive: each round joins at least one literal against the
;;;   previous round's new facts only. Body literals may be reordered for
;;;   evaluation (positive atoms first as they bind variables, = as soon as one
;;;   side is bound, negations and other built-ins as soon as all their
;;;   variables are bound); the semantics never depend on the written order.
;;;   Facts are indexed by relation and by every argument position (I2), so a
;;;   ground lookup does not scan the relation. PERFORMANCE says how the
;;;   default evaluator orders a body and runs a stratum.
;;;
;;; - INCREMENTAL MAINTENANCE. Additions: semi-naive from the added facts
;;;   (the new base facts, or for ADD-RULES the new rules' first derivations).
;;;   Retractions: DRed (delete and re-derive; Gupta, Mumick, Subrahmanian
;;;   1993): (1) over-delete every fact with a derivation that uses a deleted
;;;   fact, transitively, stratum by stratum; (2) re-derive the over-deleted
;;;   facts that still have a derivation from what remains; (3) propagate the
;;;   re-derived facts semi-naively. Negation crosses strata: a deletion in a
;;;   lower stratum can add facts above it (through (not …)) and an addition
;;;   can delete them; each stratum is maintained after the ones below it, with
;;;   both its insertions and its deletions. One UPDATE runs its retractions and
;;;   assertions as one change; the returned delta is the net model change.
;;;
;;;   Why DRed and not counting: counting keeps a derivation count per fact,
;;;   which is only correct for non-recursive rules. Recursive programs (every
;;;   closure, the L1 layers, the L3 dependencies) need DRed or the
;;;   recursive-counting variants, and DRed is the simplest of those that also
;;;   handles stratified negation, with no extra state per fact. The brief
;;;   locks it.
;;;
;;; - COST (the reason the algorithm is incremental, tested in
;;;   tests/incremental-cost-test.lisp). An UPDATE that touches K facts of the
;;;   model charges O(K × body matches per fact), not O(|model|): one input
;;;   field in an L3 form, or one request asserted in L1, costs about what it
;;;   changes. Since 0.2.0 a bulk change also costs what it changes: loading
;;;   facts into a program that already has its rules costs about what adding
;;;   the rules to the loaded facts costs, and retracting a batch about what
;;;   asserting it costs (tests/perf-test.lisp).
;;;
;;; - PERFORMANCE (0.2.0). Two evaluators behind the internal switch
;;;   *STRATEGY*: :AUTO, the default, and :REFERENCE, the 0.1.0 evaluator
;;;   kept unchanged as the oracle (alist bindings, %PICK at every search
;;;   step, one %SOLVE-FROM per changed fact and literal, EXPLAIN heights by
;;;   re-solving every rule at every height). Both give the same model, every
;;;   delta, every proof and every why-not trace, on any program and any
;;;   sequence of calls (tests/equivalence-test.lisp, random stratified
;;;   programs and random batches). Both charge per BUDGET; the counts may
;;;   differ, since :AUTO finds fewer duplicate derivations. Both write
;;;   through the logged mutators (I3). Under :AUTO:
;;;
;;;   P1 COMPILED RULES (#5). Each rule is compiled once, on first use:
;;;      variables numbered, bindings in a SIMPLE-VECTOR indexed by variable
;;;      number (NIL is unbound: it is never a constant), every literal's
;;;      arguments as constants or variable numbers. Evaluation follows a
;;;      plan (P2) that fixes where each variable is bound, so a step knows
;;;      which argument positions are bound and picks its index bucket
;;;      directly; there is no ASSOC, no undo (a later step overwrites its
;;;      own slots) and no choice of the next literal at run time.
;;;
;;;   P2 JOIN ORDER. A plan takes built-ins and negations as soon as their
;;;      variables are bound and = as soon as one side is; then the atom
;;;      with the fewest expected candidates: a ground lookup first, then an
;;;      atom sharing a bound variable, then the rest, each group by the size
;;;      of what the atom reads (its relation in the view, a delta, the index
;;;      bucket of a constant argument), written order last. So no body
;;;      starts from a large table with no argument bound while a smaller
;;;      atom is available, and a delta is joined where it is cheapest. Plans
;;;      that run once per call (full solves, set-at-a-time rounds, queries,
;;;      ticks, EXPLAIN levels) use the sizes of that moment; the per-fact
;;;      seed plans are static.
;;;
;;;   P3 SET-AT-A-TIME MAINTENANCE (#4). The over-delete and the insert phase
;;;      of a stratum S (see "Maintenance" below) each choose a mode from
;;;      their input delta D: per relation R, the facts the phase starts
;;;      from. Over-delete: S's retracted base facts, the net removals of the
;;;      lower relations S's rules read positively, the net additions of
;;;      those they read under NOT. Insert: S's asserted and re-derived facts,
;;;      the new rules' first derivations, the net additions of lower
;;;      relations read positively, the net removals of those under NOT.
;;;      SET-AT-A-TIME when for some R, |D_R| >= *SET-AT-A-TIME-MINIMUM*
;;;      (default 256) or |D_R| >= *SET-AT-A-TIME-RATIO* (default 1/4) × |R|,
;;;      |R| being R's facts in the model as the phase decides, plus those of
;;;      D_R that are not in it; a NIL threshold does not apply. Otherwise
;;;      PER-FACT: the 0.1.0 worklist (one seed per fact and literal) on
;;;      compiled rules. *MODE-HOOK*, when set, hears (S PHASE MODE) for each
;;;      phase with a non-empty D. Set-at-a-time runs semi-naive rounds:
;;;      round 0 joins each delta, indexed like a relation, once per body
;;;      literal that reads it; round k+1 joins what round k produced, which
;;;      enters the model when round k ends. In insert rounds a derivation
;;;      is found once per round, not once per new premise: for a delta at
;;;      literal i, the earlier literals that read a delta of the same round
;;;      read the model without it (so a bulk load joins each derivation once,
;;;      as a full solve does). Re-derive stays per fact: it is an existence
;;;      check with the head bound.
;;;
;;;   P4 OLD VIEW. :OLD reads the call's net removals through an index like
;;;      the model's, so an over-delete lookup costs what a :NEW lookup costs
;;;      (0.1.0 appends every removed fact of the relation to each lookup,
;;;      which makes a bulk retraction under a higher stratum quadratic).
;;;
;;;   P5 EXPLAIN HEIGHTS. Least heights are computed only for the positive
;;;      cone of the explained fact's relation (the relations its rules read
;;;      through positive atoms, transitively; negations read the model) and
;;;      kept, with the cone they cover, until the next write. Level k is
;;;      semi-naive: for each positive literal, the facts of height exactly
;;;      k-1 there, the earlier literals reading height <= k-2 and the later
;;;      ones <= k-1. Proofs and why-not traces are then chosen as before.
;;;
;;;   P6 INDEX MEMORY (shared state, so under both evaluators). An index
;;;      bucket, and any table made per delta or per round, starts with a
;;;      few entries (MAKE-HASH-TABLE :SIZE) and grows. ECL's default hash
;;;      table holds 1024 entries, so 0.1.0's one EQUAL table per
;;;      (POSITION . VALUE) costs about 1 GB per 40k facts of distinct
;;;      arguments there, and the benchmarks exhaust ECL's default 4 GB heap.
;;;
;;;   The benchmarks are soft tests with ratio bounds under the speedups a
;;;   throwaway reference implementation measured on SBCL and on ECL (see
;;;   the PR): 5k facts × 20 rules; a three-relation join starting at a large
;;;   unbound table; EXPLAIN of a height-4 fact; 40 rules of 20 variables
;;;   and 8 atoms over 5k facts; a bulk retraction.
;;;
;;; - BUDGET. Call LOGIC-PROTOCOL:CHARGE-BUDGET once per derivation (a rule
;;;   body match that produces a head fact, new or not), once per fact
;;;   over-deleted and once per fact re-derived, and once per answer in
;;;   BACKEND-QUERY. During a query, keep
;;;   (BUDGET-METER-PARTIAL-FUNCTION METER) returning the answers so far.
;;;
;;; - TRANSACTIONS. BACKEND-ADD-RULES, BACKEND-UPDATE and BACKEND-TICK leave
;;;   the state as before the call on a non-local exit (an undo log, or work
;;;   on a copy that is installed at the end).
;;;
;;; - TIME STEPS (Dedalus, :NEXT rules). BACKEND-TICK reads the :NEXT rules'
;;;   bodies against the current model, makes their heads the new base facts
;;;   (all other base facts go), and maintains the model incrementally from
;;;   the old base set to the new one (the base change is an ordinary
;;;   retract + assert). :NEXT rules take no part in stratification.
;;;
;;; - EXPLAIN. Proofs and why-not traces exactly as logic-protocol's
;;;   model.lisp defines them (least height, rule order, premise order). The
;;;   backend may compute heights on demand from the model; it need not store
;;;   derivations. Under :AUTO, P5.
;;;
;;; - FEATURES. :STRATIFIED-NEGATION :TIME-STEP :INCREMENTAL. Not :CHOICE,
;;;   :CONSTRAINT or :UNSTRATIFIED-NEGATION (those are logic-backend-asp, L5);
;;;   the protocol signals LOGIC-UNSUPPORTED-RULE / LOGIC-UNSTRATIFIABLE for
;;;   them, with USE-BACKEND.
;;;
;;; - DEFAULT. Loading this system sets LOGIC-PROTOCOL:*LOGIC-BACKEND* to a
;;;   DATALOG-BACKEND when it is NIL.
;;;
;;; - PORTABILITY. Portable CL only (SBCL, CCL, ECL): no implementation
;;;   internals; hash tables with EQUAL keys; no reliance on hash-table
;;;   iteration order for anything the protocol returns.

(defclass datalog-backend (logic-backend) ()
  (:documentation "Semi-naive Datalog with DRed maintenance, stratified
negation and Dedalus time steps."))

(defun make-datalog-backend ()
  (make-instance 'datalog-backend))

(defmethod backend-name ((backend datalog-backend)) :datalog)

(defmethod backend-features ((backend datalog-backend))
  '(:stratified-negation :time-step :incremental))

;;; ------------------------------------------------------------------
;;; The evaluator switch and the set-at-a-time thresholds (PERFORMANCE).
;;; Internal, not exported: tests/equivalence-test.lisp and
;;; tests/perf-test.lisp bind them.
;;;
;;; CONTRACT: *STRATEGY* ships as :REFERENCE until the :AUTO stubs at the end
;;; of this file are implemented; the implementation makes :AUTO the default
;;; (test DEFAULT-STRATEGY-IS-AUTO).

(defvar *strategy* :reference
  "The evaluator the backend GFs run: :AUTO (the 0.2.0 evaluator, the
default once it is implemented) or :REFERENCE (the 0.1.0 evaluator, kept
unchanged as the equivalence oracle). Read on every backend GF call; one
state works under either.")

(defvar *set-at-a-time-ratio* 1/4
  "Under :AUTO, a maintenance phase runs set-at-a-time when, for some
relation R, its input delta D_R has |D_R| >= this * |R| (see the header).
NIL turns the ratio test off; 0 makes every non-empty phase set-at-a-time.")

(defvar *set-at-a-time-minimum* 256
  "Under :AUTO, a maintenance phase also runs set-at-a-time when some input
delta D_R has at least this many facts. NIL turns the absolute test off.")

(defvar *mode-hook* nil
  "NIL, or a function the :AUTO maintenance calls as (STRATUM PHASE MODE) once
for every stratum phase whose input delta is not empty: PHASE :OVER-DELETE or
:INSERT, MODE :PER-FACT or :SET-AT-A-TIME. For tests.")

(defun %auto-p ()
  "Is the :AUTO evaluator selected? A *STRATEGY* other than :AUTO or
:REFERENCE signals a TYPE-ERROR (with STORE-VALUE)."
  (check-type *strategy* (member :auto :reference))
  (eq *strategy* :auto))

;;; ------------------------------------------------------------------
;;; State
;;;
;;; Invariants:
;;; I1  the model (the RTABs) is the stratified fixpoint of BASE under the
;;;     :NORMAL rules;
;;; I2  a fact is in an RTAB's ALL table iff it is in each bucket
;;;     (POSITION . VALUE) of its arguments;
;;; I3  every write to the RTABs or BASE goes through the four logged
;;;     mutators, and BACKEND-ADD-RULES replaces (never mutates) the rule
;;;     slots, so a rollback replays the undo log and restores the slots.

(defstruct (rtab (:constructor make-rtab ()))
  (all (make-hash-table :test 'equal))     ; fact -> T
  (index (make-hash-table :test 'equal)))  ; (POSITION . VALUE) -> fact set

(defstruct (crule (:constructor %make-crule (rule kind head body)))
  rule kind head body
  (compiled nil))                       ; :AUTO only: %CRULE-COMPILED fills it once

(defstruct (dstate (:constructor make-dstate ()))
  (rels (make-hash-table :test 'eq))       ; relation -> RTAB (the model)
  (base (make-hash-table :test 'equal))    ; fact -> T
  (rules '())                              ; CRULEs, PROGRAM-RULES order
  (normal '())
  (next '())
  (strata (vector '()))                    ; stratum -> :NORMAL CRULEs, rule order
  (stratum-of (make-hash-table :test 'eq)) ; relation -> stratum (absent: 0)
  (readers (make-hash-table :test 'eq))    ; relation -> ((CRULE INDEX STRATUM) ...) positive atoms
  (neg-readers (make-hash-table :test 'eq)) ; relation -> ((CRULE INDEX STRATUM) ...) (not ATOM)
  (log :off)                               ; undo log during a transaction
  (heights nil))                           ; EXPLAIN cache, dropped on every write

(defun %stratum (st relation)
  (gethash relation (dstate-stratum-of st) 0))

(defun in-model-p (st fact)
  (let ((tab (gethash (car fact) (dstate-rels st))))
    (and tab (gethash fact (rtab-all tab)) t)))

(defun base-p (st fact)
  (and (gethash fact (dstate-base st)) t))

(defun %raw-model-add (st fact)
  (let ((tab (or (gethash (car fact) (dstate-rels st))
                 (setf (gethash (car fact) (dstate-rels st)) (make-rtab)))))
    (setf (gethash fact (rtab-all tab)) t)
    (loop for arg in (cdr fact)
          for pos from 0
          do (let ((key (cons pos arg)))
               (setf (gethash fact (or (gethash key (rtab-index tab))
                                       (setf (gethash key (rtab-index tab))
                                             (make-hash-table :test 'equal))))
                     t)))))

(defun %raw-model-remove (st fact)
  (let ((tab (gethash (car fact) (dstate-rels st))))
    (when tab
      (remhash fact (rtab-all tab))
      (loop for arg in (cdr fact)
            for pos from 0
            do (let* ((key (cons pos arg))
                      (bucket (gethash key (rtab-index tab))))
                 (when bucket
                   (remhash fact bucket)
                   (when (zerop (hash-table-count bucket))
                     (remhash key (rtab-index tab)))))))))

(defun %log (st op fact)
  (let ((log (dstate-log st)))
    (unless (eq log :off)
      (setf (dstate-log st) (cons (cons op fact) log))))
  (setf (dstate-heights st) nil))

(defun model-add (st fact)
  "Add FACT to the model; T when it was not there."
  (unless (in-model-p st fact)
    (%raw-model-add st fact)
    (%log st :model-add fact)
    t))

(defun model-remove (st fact)
  "Remove FACT from the model; T when it was there."
  (when (in-model-p st fact)
    (%raw-model-remove st fact)
    (%log st :model-remove fact)
    t))

(defun base-add (st fact)
  (unless (base-p st fact)
    (setf (gethash fact (dstate-base st)) t)
    (%log st :base-add fact)
    t))

(defun base-remove (st fact)
  (when (base-p st fact)
    (remhash fact (dstate-base st))
    (%log st :base-remove fact)
    t))

(defun %undo (st entry)
  (let ((fact (cdr entry)))
    (ecase (car entry)
      (:model-add (%raw-model-remove st fact))
      (:model-remove (%raw-model-add st fact))
      (:base-add (remhash fact (dstate-base st)))
      (:base-remove (setf (gethash fact (dstate-base st)) t)))))

(defun %rule-slots (st)
  (list (dstate-rules st) (dstate-normal st) (dstate-next st) (dstate-strata st)
        (dstate-stratum-of st) (dstate-readers st) (dstate-neg-readers st)))

(defun %restore-rule-slots (st slots)
  (destructuring-bind (rules normal next strata stratum-of readers neg-readers) slots
    (setf (dstate-rules st) rules (dstate-normal st) normal (dstate-next st) next
          (dstate-strata st) strata (dstate-stratum-of st) stratum-of
          (dstate-readers st) readers (dstate-neg-readers st) neg-readers)))

(defmacro with-transaction ((st) &body body)
  "Run BODY; on a non-local exit undo every write it made to ST."
  (let ((s (gensym "STATE")) (saved (gensym "SLOTS")) (ok (gensym "OK")))
    `(let* ((,s ,st)
            (,saved (%rule-slots ,s))
            (,ok nil))
       (setf (dstate-log ,s) '())
       (unwind-protect
            (multiple-value-prog1 (progn ,@body) (setf ,ok t))
         (unless ,ok
           (dolist (entry (dstate-log ,s)) ; newest first
             (%undo ,s entry))
           (%restore-rule-slots ,s ,saved))
         (setf (dstate-log ,s) :off
               (dstate-heights ,s) nil)))))

(defun %not-p (lit)
  (and (consp lit) (symbolp (car lit)) (string= (symbol-name (car lit)) "NOT")))

(defun %install-rules (st rules)
  "Append RULES to ST with fresh rule slots (strata, readers). Returns the
new CRULEs."
  (let* ((new (mapcar (lambda (r) (%make-crule r (rule-kind r) (rule-head r) (rule-body r)))
                      rules))
         (all (append (dstate-rules st) new))
         (normal (remove :normal all :key #'crule-kind :test-not #'eq))
         (next (remove :next all :key #'crule-kind :test-not #'eq))
         (strata (stratify (mapcar #'crule-rule normal)))
         (stratum-of (make-hash-table :test 'eq))
         (readers (make-hash-table :test 'eq))
         (neg-readers (make-hash-table :test 'eq)))
    (loop for relations in strata
          for s from 0
          do (dolist (r relations) (setf (gethash r stratum-of) s)))
    (let ((vector (make-array (max 1 (length strata)) :initial-element '())))
      (dolist (cr (reverse normal))
        (let ((s (gethash (car (crule-head cr)) stratum-of 0)))
          (push cr (aref vector s))
          (loop for lit in (reverse (crule-body cr))
                for i downfrom (1- (length (crule-body cr)))
                do (cond ((logic-atom-p lit)
                          (push (list cr i s) (gethash (car lit) readers)))
                         ((and (%not-p lit) (logic-atom-p (second lit)))
                          (push (list cr i s) (gethash (car (second lit)) neg-readers)))))))
      (setf (dstate-rules st) all (dstate-normal st) normal (dstate-next st) next
            (dstate-strata st) vector (dstate-stratum-of st) stratum-of
            (dstate-readers st) readers (dstate-neg-readers st) neg-readers))
    new))

;;; ------------------------------------------------------------------
;;; Joins
;;;
;;; A VIEW says which facts a positive atom sees:
;;;   :NEW     the model as it is now;
;;;   :OLD     the model before this maintenance call, for strata already
;;;            maintained: (model - net added) + net removed (*CHANGE*);
;;;   integer  facts whose least height (*HEIGHTS*) is at most that.
;;; A negated atom reads :OLD under :OLD and the model otherwise.

(defvar *change* nil
  "During maintenance: relation -> (fact -> :ADDED | :REMOVED), the net
model change of the current call.")

(defvar *heights* nil
  "During EXPLAIN: fact -> least proof height.")

(defun %change-status (fact)
  (let ((table (and *change* (gethash (car fact) *change*))))
    (and table (gethash fact table))))

(defun %changed (relation status)
  "The facts of RELATION with net STATUS in *CHANGE*."
  (let ((table (and *change* (gethash relation *change*))))
    (when table
      (loop for f being the hash-keys of table using (hash-value s)
            when (eq s status) collect f))))

(defun %note (fact status)
  "Record a net change of FACT; a fact that comes back cancels out."
  (let ((table (or (gethash (car fact) *change*)
                   (setf (gethash (car fact) *change*) (make-hash-table :test 'equal)))))
    (if (gethash fact table)
        (remhash fact table)
        (setf (gethash fact table) status))))

(defun %visible-p (st fact view)
  (cond ((eq view :new) (in-model-p st fact))
        ((eq view :old) (case (%change-status fact)
                          (:removed t)
                          (:added nil)
                          (t (in-model-p st fact))))
        (t (let ((h (gethash fact *heights*))) (and h (<= h view))))))

(defun %val (x env)
  (if (logic-variable-p x)
      (let ((b (assoc x env))) (if b (cdr b) x))
      x))

(defun %bound-p (x env)
  (not (logic-variable-p (%val x env))))

(defun %unify-args (pattern args env)
  "ENV extended so that the terms PATTERN match the constants ARGS, or :FAIL."
  (loop
    (cond ((and (null pattern) (null args)) (return env))
          ((or (null pattern) (null args)) (return :fail)))
    (let ((v (%val (pop pattern) env))
          (a (pop args)))
      (cond ((logic-variable-p v) (push (cons v a) env))
            ((not (equal v a)) (return :fail))))))

(defun %candidates (st atom env view)
  "A fresh list of facts of ATOM's relation that VIEW sees and that may match
ATOM under ENV (the caller unifies)."
  (let* ((args (mapcar (lambda (x) (%val x env)) (cdr atom)))
         (tab (gethash (car atom) (dstate-rels st))))
    (if (notany #'logic-variable-p args)
        (let ((fact (cons (car atom) args)))
          (and (%visible-p st fact view) (list fact)))
        (let ((source (and tab (rtab-all tab))))
          (when tab
            (loop for a in args
                  for pos from 0
                  unless (logic-variable-p a)
                    do (let ((bucket (gethash (cons pos a) (rtab-index tab))))
                         (cond ((null bucket) (setf source nil) (return))
                               ((< (hash-table-count bucket) (hash-table-count source))
                                (setf source bucket))))))
          (let ((out '()))
            (when source
              (maphash (lambda (f v)
                         (declare (ignore v))
                         (when (or (eq view :new) (%visible-p st f view))
                           (push f out)))
                       source))
            (when (eq view :old)
              (setf out (nconc (%changed (car atom) :removed) out)))
            out)))))

(defun %builtin-holds (name a b)
  (flet ((compare (int-fn str-fn)
           (cond ((and (integerp a) (integerp b)) (and (funcall int-fn a b) t))
                 ((and (stringp a) (stringp b)) (and (funcall str-fn a b) t))
                 (t nil))))
    (cond ((string= name "=") (equal a b))
          ((string= name "/=") (not (equal a b)))
          ((string= name "<") (compare #'< #'string<))
          ((string= name "<=") (compare #'<= #'string<=))
          ((string= name ">") (compare #'> #'string>))
          ((string= name ">=") (compare #'>= #'string>=))
          ((string= name "GLOB") (and (stringp a) (stringp b) (%glob a b)))
          ((string= name "PREFIX")
           (and (stringp a) (stringp b) (<= (length a) (length b))
                (string= a b :end2 (length a))))
          (t (error "Unknown built-in ~S" name)))))

(defun %glob (pattern string)
  "Does PATTERN (* any run, ? one character) match the whole of STRING?"
  (let ((np (length pattern)) (ns (length string)))
    (labels ((match (i j)
               (cond ((= i np) (= j ns))
                     ((char= (char pattern i) #\*)
                      (loop for k from j to ns thereis (match (1+ i) k)))
                     ((= j ns) nil)
                     ((or (char= (char pattern i) #\?)
                          (char= (char pattern i) (char string j)))
                      (match (1+ i) (1+ j)))
                     (t nil))))
      (match 0 0))))

(defun %ground-in-p (lit env)
  (every (lambda (x) (%bound-p x env)) (cdr lit)))

(defun %filter-holds-p (st lit env view)
  "LIT (a built-in or a negation, every variable bound) under ENV."
  (if (%not-p lit)
      (let ((inner (second lit)))
        (if (builtin-literal-p inner)
            (not (%builtin-holds (symbol-name (car inner))
                                 (%val (second inner) env) (%val (third inner) env)))
            (not (%visible-p st (cons (car inner) (mapcar (lambda (x) (%val x env)) (cdr inner)))
                             (if (eq view :old) :old :new)))))
      (%builtin-holds (symbol-name (car lit)) (%val (second lit) env) (%val (third lit) env))))

(defun %pick (lits env)
  "The literal to evaluate next and how: :FILTER, :BIND or :ATOM."
  (let ((bind nil) (best nil) (best-score -1))
    (dolist (lit lits)
      (cond ((%not-p lit)
             (when (%ground-in-p (second lit) env) (return-from %pick (values lit :filter))))
            ((builtin-literal-p lit)
             (let ((a (%bound-p (second lit) env)) (b (%bound-p (third lit) env)))
               (cond ((and a b) (return-from %pick (values lit :filter)))
                     ((and (or a b) (string= (symbol-name (car lit)) "=") (null bind))
                      (setf bind lit)))))
            (t (let ((score (count-if (lambda (x) (%bound-p x env)) (cdr lit))))
                 (when (> score best-score) (setf best lit best-score score))))))
    (cond (bind (values bind :bind))
          (best (values best :atom))
          (t (error "No literal of ~S can be evaluated under ~S (unsafe body)" lits env)))))

(defun %solve (st lits env view fn)
  "Call FN with every extension of ENV that satisfies all of LITS in VIEW."
  (if (null lits)
      (funcall fn env)
      (multiple-value-bind (lit how) (%pick lits env)
        (let ((rest (remove lit lits :count 1 :test #'eq)))
          (ecase how
            (:filter (when (%filter-holds-p st lit env view)
                       (%solve st rest env view fn)))
            (:bind (let ((a (second lit)) (b (third lit)))
                     (if (%bound-p a env)
                         (%solve st rest (acons (%val b env) (%val a env) env) view fn)
                         (%solve st rest (acons (%val a env) (%val b env) env) view fn))))
            (:atom (dolist (f (%candidates st lit env view))
                     (let ((e (%unify-args (cdr lit) (cdr f) env)))
                       (unless (eq e :fail)
                         (%solve st rest e view fn))))))))))

(defun %without (list index)
  (loop for x in list for i from 0 unless (= i index) collect x))

(defun %solve-from (st crule index fact view fn)
  "Solutions of CRULE's body with literal INDEX bound to FACT. A positive
literal is consumed; for (not ATOM), ATOM is unified with FACT and the
negation stays in the body, so it is still checked in VIEW."
  (let* ((body (crule-body crule))
         (lit (nth index body)))
    (if (%not-p lit)
        (let ((env (%unify-args (cdr (second lit)) (cdr fact) '())))
          (unless (eq env :fail) (%solve st body env view fn)))
        (let ((env (%unify-args (cdr lit) (cdr fact) '())))
          (unless (eq env :fail) (%solve st (%without body index) env view fn))))))

(defun %head (crule env)
  (substitute-bindings (crule-head crule) env))

(defun %unify-head (crule fact)
  "The bindings that make CRULE's head FACT, or :FAIL."
  (if (eq (car (crule-head crule)) (car fact))
      (%unify-args (cdr (crule-head crule)) (cdr fact) '())
      :fail))

;;; ------------------------------------------------------------------
;;; Maintenance: one stratum at a time, lowest first. Per stratum S:
;;;
;;; 1. Over-delete (view :OLD): seeds are the retracted base facts of S, the
;;;    derivations of S's old rules through a net-removed lower fact (positive
;;;    literal) or a net-added lower fact (negated literal); then
;;;    transitively through S's own relations. A fact enters OD when it is in
;;;    the model and not a base fact. The removals are applied after OD is
;;;    complete, so S's relations still show the old model meanwhile.
;;; 2. Re-derive (view :NEW): each OD fact with a one-step derivation from
;;;    what remains comes back.
;;; 3. Insert (view :NEW, semi-naive worklist): the re-derived facts, the
;;;    asserted base facts of S, derivations through a net-added lower fact
;;;    (positive) or a net-removed one (negated), and the new rules' full
;;;    body solutions; then transitively through S's own relations.
;;;
;;; Charges: one per derivation (each body match, new head or not), one per
;;; over-deleted fact, one per re-derived fact, one per asserted base fact
;;; that enters the model.
;;;
;;; This is %MAINTAIN-STRATUM, the :REFERENCE path. Under :AUTO the same
;;; phases run in %MAINTAIN-STRATUM-AUTO, phases 1 and 3 per fact or
;;; set-at-a-time (PERFORMANCE, P3).

(defun %maintain (st retracted asserted new-crules meter)
  "Bring the model up to date after the base change RETRACTED / ASSERTED
(already applied to BASE) and the addition of NEW-CRULES. Returns the DELTA."
  (let ((*change* (make-hash-table :test 'eq))
        (n (length (dstate-strata st)))
        (maintain-stratum (if (%auto-p) #'%maintain-stratum-auto #'%maintain-stratum)))
    (dotimes (s n)
      (flet ((here (facts) (remove-if-not (lambda (f) (= (%stratum st (car f)) s)) facts)))
        (funcall maintain-stratum st s (here retracted) (here asserted)
                 (remove-if-not (lambda (cr) (member cr (aref (dstate-strata st) s)))
                                new-crules)
                 meter)))
    (let ((added '()) (removed '()))
      (maphash (lambda (rel table)
                 (declare (ignore rel))
                 (maphash (lambda (f status)
                            (if (eq status :added) (push f added) (push f removed)))
                          table))
               *change*)
      (make-delta :added added :removed removed))))

(defun %maintain-stratum (st s retracted asserted new meter)
  (let* ((rules (aref (dstate-strata st) s))
         (old-rules (remove-if (lambda (cr) (member cr new)) rules))
         (od (make-hash-table :test 'equal))
         (work '()))
    (flet ((lower-p (relation) (< (%stratum st relation) s))
           (readers (fact table rule-filter)
             (loop for entry in (gethash (car fact) table)
                   when (and (= (third entry) s) (funcall rule-filter (first entry)))
                     collect entry)))
      ;; 1. Over-delete.
      (flet ((od-add (f)
               (when (and (in-model-p st f) (not (base-p st f)) (not (gethash f od)))
                 (charge-budget meter)
                 (setf (gethash f od) t)
                 (push f work))))
        (dolist (f retracted) (od-add f))
        (dolist (cr old-rules)
          (loop for lit in (crule-body cr)
                for i from 0
                do (cond ((and (logic-atom-p lit) (lower-p (car lit)))
                          (dolist (g (%changed (car lit) :removed))
                            (%solve-from st cr i g :old
                                         (lambda (env) (charge-budget meter) (od-add (%head cr env))))))
                         ((and (%not-p lit) (logic-atom-p (second lit)))
                          (dolist (g (%changed (car (second lit)) :added))
                            (%solve-from st cr i g :old
                                         (lambda (env) (charge-budget meter) (od-add (%head cr env)))))))))
        (loop while work
              do (let ((f (pop work)))
                   (dolist (entry (readers f (dstate-readers st)
                                           (lambda (cr) (not (member cr new)))))
                     (let ((cr (first entry)))
                       (%solve-from st cr (second entry) f :old
                                    (lambda (env) (charge-budget meter) (od-add (%head cr env)))))))))
      (let ((deleted (loop for f being the hash-keys of od collect f)))
        (dolist (f deleted)
          (model-remove st f)
          (%note f :removed))
        ;; 2. Re-derive.
        (dolist (f deleted)
          (when (%derivable-p st rules f)
            (charge-budget meter)
            (model-add st f)
            (%note f :added)
            (push f work))))
      ;; 3. Insert.
      (flet ((derive (cr)
               (lambda (env)
                 (charge-budget meter)
                 (let ((f (%head cr env)))
                   (when (model-add st f)
                     (%note f :added)
                     (push f work))))))
        (dolist (f asserted)
          (unless (in-model-p st f)
            (charge-budget meter)
            (model-add st f)
            (%note f :added)
            (push f work)))
        (dolist (cr old-rules)
          (loop for lit in (crule-body cr)
                for i from 0
                do (cond ((and (logic-atom-p lit) (lower-p (car lit)))
                          (dolist (g (%changed (car lit) :added))
                            (%solve-from st cr i g :new (derive cr))))
                         ((and (%not-p lit) (logic-atom-p (second lit)))
                          (dolist (g (%changed (car (second lit)) :removed))
                            (%solve-from st cr i g :new (derive cr)))))))
        (dolist (cr new)
          (%solve st (crule-body cr) '() :new (derive cr)))
        (loop while work
              do (let ((f (pop work)))
                   (dolist (entry (readers f (dstate-readers st) (constantly t)))
                     (let ((cr (first entry)))
                       (%solve-from st cr (second entry) f :new (derive cr))))))))))

(defun %derivable-p (st rules fact)
  "Does one of RULES derive FACT in one step from the current model?"
  (dolist (cr rules nil)
    (let ((env (%unify-head cr fact)))
      (unless (eq env :fail)
        (%solve st (crule-body cr) env :new
                (lambda (e) (declare (ignore e)) (return-from %derivable-p t)))))))

;;; ------------------------------------------------------------------
;;; Protocol GFs

(defmethod backend-make-state ((backend datalog-backend))
  (make-dstate))

(defmethod backend-add-rules ((backend datalog-backend) state rules meter)
  (with-transaction (state)
    (let ((new (%install-rules state rules)))
      (%maintain state '() '() (remove :normal new :key #'crule-kind :test-not #'eq) meter))))

(defmethod backend-update ((backend datalog-backend) state assert retract meter)
  (with-transaction (state)
    (let* ((in-assert (let ((h (make-hash-table :test 'equal)))
                        (dolist (f assert h) (setf (gethash f h) t))))
           (retracted (remove-if-not (lambda (f) (and (base-p state f) (not (gethash f in-assert))))
                                     retract))
           (asserted (remove-if (lambda (f) (base-p state f)) assert)))
      (dolist (f retracted) (base-remove state f))
      (dolist (f asserted) (base-add state f))
      (%maintain state retracted asserted '() meter))))

(defmethod backend-tick ((backend datalog-backend) state meter)
  (with-transaction (state)
    (let ((next (if (%auto-p)
                    (%next-base-auto state meter)
                    (let ((next (make-hash-table :test 'equal)))
                      (dolist (cr (dstate-next state) next)
                        (%solve state (crule-body cr) '() :new
                                (lambda (env)
                                  (charge-budget meter)
                                  (setf (gethash (%head cr env) next) t))))))))
      (let ((retracted (loop for f being the hash-keys of (dstate-base state)
                             unless (gethash f next) collect f))
            (asserted (loop for f being the hash-keys of next
                            unless (base-p state f) collect f)))
        (dolist (f retracted) (base-remove state f))
        (dolist (f asserted) (base-add state f))
        (%maintain state retracted asserted '() meter)))))

(defmethod backend-query ((backend datalog-backend) state pattern meter)
  (if (%auto-p)
      (%query-auto state pattern meter)
      (let ((answers '())
            (variables (atom-variables pattern)))
        (setf (budget-meter-partial-function meter) (lambda () answers))
        (%solve state pattern '() :new
                (lambda (env)
                  (push (mapcar (lambda (v) (cons v (cdr (assoc v env)))) variables) answers)
                  (charge-budget meter)))
        answers)))

(defmethod backend-facts ((backend datalog-backend) state relation)
  (flet ((facts-of (tab) (loop for f being the hash-keys of (rtab-all tab) collect f)))
    (if relation
        (let ((tab (gethash relation (dstate-rels state))))
          (and tab (facts-of tab)))
        (loop for tab being the hash-values of (dstate-rels state)
              nconc (facts-of tab)))))

(defmethod backend-base-facts ((backend datalog-backend) state)
  (loop for f being the hash-keys of (dstate-base state) collect f))

;;; ------------------------------------------------------------------
;;; Explain (unbudgeted). Least heights, level by level: base facts 0; a
;;; fact gets height K when some rule derives it with every positive premise
;;; of height <= K-1 (negations read the model).

(defun %compute-heights (st)
  (let ((heights (make-hash-table :test 'equal)))
    (maphash (lambda (f v) (declare (ignore v)) (setf (gethash f heights) 0)) (dstate-base st))
    (let ((*heights* heights))
      (loop for k from 1
            do (let ((fresh '()))
                 (dolist (cr (dstate-normal st))
                   (%solve st (crule-body cr) '() (1- k)
                           (lambda (env)
                             (let ((f (%head cr env)))
                               (unless (gethash f heights) (push f fresh))))))
                 (when (null fresh) (return))
                 (dolist (f fresh) (setf (gethash f heights) k)))))
    heights))

(defun %heights (st)
  (or (dstate-heights st)
      (setf (dstate-heights st) (%compute-heights st))))

(defun %facts< (a b)
  "Lexicographic FACT< on two lists of facts of the same length."
  (loop for x in a for y in b
        do (cond ((fact< x y) (return t))
                 ((fact< y x) (return nil)))
        finally (return nil)))

(defun %positive-premises (crule env)
  (loop for lit in (crule-body crule)
        when (logic-atom-p lit) collect (substitute-bindings lit env)))

(defun %prove (st fact memo)
  (or (gethash fact memo)
      (setf (gethash fact memo)
            (if (base-p st fact)
                (make-instance 'proof :fact fact)
                (let ((limit (1- (gethash fact *heights*))))
                  (dolist (cr (dstate-normal st)
                              (error "No proof of ~S in the model" fact))
                    (let ((env0 (%unify-head cr fact))
                          (found nil) (best nil) (best-premises nil))
                      (unless (eq env0 :fail)
                        (%solve st (crule-body cr) env0 limit
                                (lambda (env)
                                  (let ((premises (%positive-premises cr env)))
                                    (when (or (not found) (%facts< premises best-premises))
                                      (setf found t best env best-premises premises)))))
                        (when found
                          (return (%make-proof st cr fact best best-premises memo)))))))))))

(defun %make-proof (st cr fact env premises memo)
  (let ((body (crule-body cr)))
    (make-instance 'proof
                   :fact fact
                   :rule (crule-rule cr)
                   :premises (mapcar (lambda (p) (%prove st p memo)) premises)
                   :negated (loop for lit in body
                                  when (and (%not-p lit) (logic-atom-p (second lit)))
                                    collect (substitute-bindings (second lit) env))
                   :builtins (loop for lit in body
                                   when (or (builtin-literal-p lit)
                                            (and (%not-p lit) (builtin-literal-p (second lit))))
                                     collect (substitute-bindings lit env))
                   :bindings (mapcar (lambda (v) (cons v (cdr (assoc v env))))
                                     (atom-variables (rule-form (crule-rule cr)))))))

(defun %prefix-bound (prefix)
  "Variables the positive atoms and the = chain of PREFIX bind."
  (let ((bound (atom-variables (remove-if-not #'logic-atom-p prefix)))
        (equalities (remove-if-not (lambda (l) (and (builtin-literal-p l)
                                                    (string= (symbol-name (car l)) "=")))
                                   prefix)))
    (flet ((known-p (x) (or (logic-constant-p x) (member x bound))))
      (loop
        (let ((changed nil))
          (dolist (e equalities)
            (let ((a (second e)) (b (third e)))
              (cond ((and (logic-variable-p b) (not (member b bound)) (known-p a))
                     (push b bound) (setf changed t))
                    ((and (logic-variable-p a) (not (member a bound)) (known-p b))
                     (push a bound) (setf changed t)))))
          (unless changed (return bound)))))))

(defun %has-solution-p (st lits)
  (%solve st lits '() :new (lambda (env) (declare (ignore env)) (return-from %has-solution-p t)))
  nil)

(defun %why-not (st fact)
  (let ((reasons '()))
    (dolist (cr (dstate-normal st))
      (let ((env (%unify-head cr fact)))
        (unless (eq env :fail)
          (let ((b (mapcar (lambda (lit) (substitute-bindings lit env)) (crule-body cr))))
            (loop for k from 0 below (length b)
                  do (let* ((prefix (subseq b 0 (1+ k)))
                            (bound (%prefix-bound prefix))
                            (kept (remove-if-not
                                   (lambda (lit)
                                     (or (logic-atom-p lit)
                                         (every (lambda (v) (member v bound))
                                                (atom-variables lit))))
                                   prefix)))
                       (unless (%has-solution-p st kept)
                         (push (make-instance 'why-not-reason :rule (crule-rule cr)
                                                              :literal (nth k b) :index k)
                               reasons)
                         (return))))))))
    (make-instance 'why-not :fact fact :reasons (nreverse reasons))))

(defmethod backend-explain ((backend datalog-backend) state fact)
  (if (in-model-p state fact)
      (let ((*heights* (if (%auto-p) (%heights-auto state fact) (%heights state))))
        (%prove state fact (make-hash-table :test 'equal)))
      (%why-not state fact)))

;;; ------------------------------------------------------------------
;;; The 0.2.0 evaluator (:AUTO). Contract stubs. The four entry points the
;;; GFs call under :AUTO are %MAINTAIN-STRATUM-AUTO, %QUERY-AUTO,
;;; %NEXT-BASE-AUTO and %HEIGHTS-AUTO; %COMPILE-CRULE, %PLAN and
;;; %SET-AT-A-TIME-P are the intended building blocks (their signatures may
;;; change; tests/ only reach *STRATEGY*, the thresholds and *MODE-HOOK*).
;;; The :REFERENCE evaluator above stays as it is; P6 changes only the
;;; shared model index (%RAW-MODEL-ADD).

(define-condition perf-pending (error)
  ((what :initarg :what :reader perf-pending-what))
  (:report (lambda (c s)
             (format s "0.2.0 performance contract stub not implemented: ~S"
                     (perf-pending-what c)))))

(defun %perf-pending (what)
  "Contract stub. Every call is replaced by the 0.2.0 implementation, then
this function and PERF-PENDING are deleted."
  (error 'perf-pending :what what))

(defun %compile-crule (crule)
  "CRULE compiled once (P1): its variables numbered in the order of
(ATOM-VARIABLES (RULE-FORM RULE)), so an environment is a SIMPLE-VECTOR
indexed by variable number and the proof bindings come out in order; each
literal's arguments as constants or variable numbers; a static plan (%PLAN
with no state) per body literal that can seed a derivation, for the rest of
the body with that literal's variables bound, and one with the head's
variables bound (re-derive)."
  (declare (ignore crule))
  (%perf-pending '%compile-crule))

(defun %crule-compiled (crule)
  "CRULE's compiled form, made on first use and kept on the CRULE."
  (or (crule-compiled crule)
      (setf (crule-compiled crule) (%compile-crule crule))))

(defun %plan (st literals known sources)
  "A join plan (P2) for the compiled LITERALS with the variables KNOWN
bound: their evaluation order, for each atom the facts it reads (SOURCES
maps an atom to its view or delta) and the argument positions bound when it
is reached. With ST, atoms are ordered by the sizes at that time; with ST
NIL the plan is static (bound positions, then written order)."
  (declare (ignore st literals known sources))
  (%perf-pending '%plan))

(defun %set-at-a-time-p (st deltas)
  "Is a maintenance phase whose input delta is DELTAS, a list of
(RELATION . FACTS), run set-at-a-time (P3)? True when some FACTS has at
least *SET-AT-A-TIME-MINIMUM* elements, or at least *SET-AT-A-TIME-RATIO*
times the relation's size (its facts in the model of ST now, plus those of
FACTS not in it). A NIL threshold does not apply."
  (declare (ignore st deltas))
  (%perf-pending '%set-at-a-time-p))

(defun %maintain-stratum-auto (st s retracted asserted new meter)
  "%MAINTAIN-STRATUM under :AUTO, with the same arguments, phases, charges
and result (the model and *CHANGE* updated through the logged mutators and
%NOTE): over-delete, re-derive, insert. Over-delete and insert each choose
PER-FACT or SET-AT-A-TIME from their input delta (%SET-AT-A-TIME-P), tell
*MODE-HOOK* (S PHASE MODE) when that delta is not empty, and run on compiled
rules (P1, P2) with an indexed :OLD view (P4); re-derive is per fact."
  (declare (ignore st s retracted asserted new meter))
  (%perf-pending '%maintain-stratum-auto))

(defun %query-auto (st pattern meter)
  "BACKEND-QUERY under :AUTO: PATTERN compiled and planned once against the
current sizes, the same answers, charges and partial function."
  (declare (ignore st pattern meter))
  (%perf-pending '%query-auto))

(defun %next-base-auto (st meter)
  "BACKEND-TICK's next base facts under :AUTO: an EQUAL hash table holding
the head of every solution of every :NEXT rule's body in the current model,
one charge per solution."
  (declare (ignore st meter))
  (%perf-pending '%next-base-auto))

(defun %heights-auto (st fact)
  "The least-height table %PROVE reads for FACT under :AUTO (P5): the same
heights as %COMPUTE-HEIGHTS for every relation in the positive cone of
FACT's relation, computed semi-naively level by level and cached in the
state until the next write."
  (declare (ignore st fact))
  (%perf-pending '%heights-auto))

(unless *logic-backend*
  (setf *logic-backend* (make-datalog-backend)))
