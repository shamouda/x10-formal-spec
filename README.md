# x10-formal-spec
Formal specification for some modules in the X10 runtime system using TLA+

We use TLA+ to formally specify how certain modules are implemented and to prove the correctness of the implementation. Up until December 18th, 2017, we specified the following implementations of the finish
construct: <br />
1) The default implementation <br />
2) The SPMD implementation <br />
3) The resilient centralized implementation (Place0 Finish) <br />
4) Pessimistic distributed finish used for proof of concept in PPoPP14[1], and has a replication bug <br />
5) Pessimistic distributed finish with corrected replication <br />
6) Proposed optimistic distributed finish with correct replication <br />

References: <br />
[1] Resilient X10: Efficient failure-aware programming. David Cunningham, David Grove, Benjamin Herta, Arun Iyengar, Kiyokuni Kawachiya, Hiroki Murata, Vijay Saraswat, Mikio Takeuchi, Olivier Tardieu. Proceedings of the ACM SIGPLAN Symposium on Principles and Practice of Parallel Programming (PPoPP'14), Feb 2014.
