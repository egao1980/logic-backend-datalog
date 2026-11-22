(in-package #:logic-backend-datalog)

;;; The default logic-protocol backend: pure Lisp, no dependencies.
;;;
;;; Normative for L0 (the brief's locked decisions plus this contract):
;;;
;;; - EVALUATION. Bottom-up, stratum by stratum in the order of
;;;   LOGIC-PROTOCOL:STRATIFY over the program's :NORMAL rules. Within a
;;;   stratum, semi-naive: each round joins at least one literal against the
;;;   previous round's new facts only. Body literals may be reordered for
;;;   evaluation (positive atoms first as they bind variables, = as soon as one
;;;   side is bound, negations and other built-ins as soon as all their
;;;   variables are bound); the semantics never depend on the written order.
;;;   Facts are indexed by relation (and, as the implementer sees fit, by
;;;   bound argument positions), so a ground lookup does not scan the relation.
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
;;;   changes.
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
;;;   derivations.
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
  rule kind head body)

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

(defun %maintain (st retracted asserted new-crules meter)
  "Bring the model up to date after the base change RETRACTED / ASSERTED
(already applied to BASE) and the addition of NEW-CRULES. Returns the DELTA."
  (let ((*change* (make-hash-table :test 'eq))
        (n (length (dstate-strata st))))
    (dotimes (s n)
      (flet ((here (facts) (remove-if-not (lambda (f) (= (%stratum st (car f)) s)) facts)))
        (%maintain-stratum st s (here retracted) (here asserted)
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
    (let ((next (make-hash-table :test 'equal)))
      (dolist (cr (dstate-next state))
        (%solve state (crule-body cr) '() :new
                (lambda (env)
                  (charge-budget meter)
                  (setf (gethash (%head cr env) next) t))))
      (let ((retracted (loop for f being the hash-keys of (dstate-base state)
                             unless (gethash f next) collect f))
            (asserted (loop for f being the hash-keys of next
                            unless (base-p state f) collect f)))
        (dolist (f retracted) (base-remove state f))
        (dolist (f asserted) (base-add state f))
        (%maintain state retracted asserted '() meter)))))

(defmethod backend-query ((backend datalog-backend) state pattern meter)
  (let ((answers '())
        (variables (atom-variables pattern)))
    (setf (budget-meter-partial-function meter) (lambda () answers))
    (%solve state pattern '() :new
            (lambda (env)
              (push (mapcar (lambda (v) (cons v (cdr (assoc v env)))) variables) answers)
              (charge-budget meter)))
    answers))

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
      (let ((*heights* (%heights state)))
        (%prove state fact (make-hash-table :test 'equal)))
      (%why-not state fact)))

(unless *logic-backend*
  (setf *logic-backend* (make-datalog-backend)))
