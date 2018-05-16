# x10-formal-spec
Formal specification for some modules in the X10 runtime system using TLA+.

Currently, the main active modules are: <br />
1) async-finish-optimistic: which models the optimistic finish protocol.
2) async-finish-replication: which models the replication protocol used for implementing a distributed resilient store for finish objects.

Old spcifications in the attic folder include:
1) The non-resilient finish implementation <br />
2) The centralized pessimistic finish implementation described in Cunningham et al.[1]. <br />
3) The destributed pessimistic finish implementation described in Cunningham et al.[1] showing a replication bug. <br/>

References: <br />
[1] Resilient X10: Efficient failure-aware programming. David Cunningham, David Grove, Benjamin Herta, Arun Iyengar, Kiyokuni Kawachiya, Hiroki Murata, Vijay Saraswat, Mikio Takeuchi, Olivier Tardieu. Proceedings of the ACM SIGPLAN Symposium on Principles and Practice of Parallel Programming (PPoPP'14), Feb 2014.
