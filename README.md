# logic-backend-datalog

The default backend for [logic-protocol](https://github.com/egao1980/logic-protocol), slice L0 of Track L. Pure Lisp, no dependencies besides the protocol:

- semi-naive bottom-up evaluation, stratum by stratum;
- incremental maintenance: semi-naive for additions, DRed (delete and re-derive) for retractions, across strata with stratified negation; an update costs about what it changes;
- optional Dedalus-style time-step rules (`(rule (next …) :- …)`, `tick`);
- proofs and why-not traces as the protocol defines them.

Loading it sets `logic-protocol:*logic-backend*` when unset.

Since 0.2.0 the default evaluator compiles each rule once (numbered variables, vector environments, precomputed join plans), orders joins by the size of what each atom reads, maintains a stratum set-at-a-time when a change is large compared with the relations it touches, indexes the old view that deletions read, and computes EXPLAIN heights semi-naively over the explained relation's dependencies only. So loading facts into a program that already has its rules costs about what adding the rules afterwards costs, and a bulk retraction about what the matching assertion costs. The 0.1.0 evaluator stays available internally as the oracle that the new one is tested against; the API does not change.

Tests: the test-op runs logic-protocol's own tests, logic-protocol's backend conformance suite on this backend, and this repo's Datalog-specific tests: incremental cost, equivalence of the two evaluators on random programs (model, deltas, proofs), and benchmarks with generous ratio bounds.

Design: [cl-stack/docs/capabilities/logic.md](https://github.com/egao1980/cl-stack/blob/main/docs/capabilities/logic.md). Normative notes: the header of `src/backend.lisp`.

## License

MIT — see [LICENSE](LICENSE).
