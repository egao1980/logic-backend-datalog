# logic-backend-datalog

The default backend for [logic-protocol](https://github.com/egao1980/logic-protocol), slice L0 of Track L. Pure Lisp, no dependencies besides the protocol:

- semi-naive bottom-up evaluation, stratum by stratum;
- incremental maintenance: semi-naive for additions, DRed (delete and re-derive) for retractions, across strata with stratified negation; an update costs about what it changes;
- optional Dedalus-style time-step rules (`(rule (next …) :- …)`, `tick`);
- proofs and why-not traces as the protocol defines them.

Loading it sets `logic-protocol:*logic-backend*` when unset.

Tests: the test-op runs logic-protocol's own tests, logic-protocol's backend conformance suite on this backend, and this repo's Datalog-specific tests (incremental cost).

Design: [cl-stack/docs/capabilities/logic.md](https://github.com/egao1980/cl-stack/blob/main/docs/capabilities/logic.md). Normative notes: the header of `src/backend.lisp`.

## License

MIT — see [LICENSE](LICENSE).
