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

(defmethod backend-make-state ((backend datalog-backend))
  (%logic0-pending 'backend-make-state))

(defmethod backend-add-rules ((backend datalog-backend) state rules meter)
  (declare (ignore state rules meter))
  (%logic0-pending 'backend-add-rules))

(defmethod backend-update ((backend datalog-backend) state assert retract meter)
  (declare (ignore state assert retract meter))
  (%logic0-pending 'backend-update))

(defmethod backend-query ((backend datalog-backend) state pattern meter)
  (declare (ignore state pattern meter))
  (%logic0-pending 'backend-query))

(defmethod backend-explain ((backend datalog-backend) state fact)
  (declare (ignore state fact))
  (%logic0-pending 'backend-explain))

(defmethod backend-tick ((backend datalog-backend) state meter)
  (declare (ignore state meter))
  (%logic0-pending 'backend-tick))

(defmethod backend-facts ((backend datalog-backend) state relation)
  (declare (ignore state relation))
  (%logic0-pending 'backend-facts))

(defmethod backend-base-facts ((backend datalog-backend) state)
  (declare (ignore state))
  (%logic0-pending 'backend-base-facts))

(unless *logic-backend*
  (setf *logic-backend* (make-datalog-backend)))
