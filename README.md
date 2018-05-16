# x10-formal-spec
Formal specification for some modules in the X10 runtime system using TLA+[1].

Currently, the main active modules are: <br />
1) async-finish-optimistic: which models the optimistic finish protocol.
2) async-finish-replication: which models the replication protocol used for implementing a distributed resilient store for finish objects.

Old spcifications in the attic folder include:
1) The non-resilient finish implementation <br />
2) The centralized pessimistic finish implementation described in Cunningham et al.[2]. <br />
3) The destributed pessimistic finish implementation described in Cunningham et al.[2] showing a replication bug. <br/>

We use TLA+ version 1.5.6 for verifying our models. We avoid using earlier versions since they are impacted by a serious verification bug according to [1]. <br />

References: <br />
[1] TLA+ website: http://lamport.azurewebsites.net/tla/tla.html <br />
[2] Resilient X10: Efficient failure-aware programming. David Cunningham, David Grove, Benjamin Herta, Arun Iyengar, Kiyokuni Kawachiya, Hiroki Murata, Vijay Saraswat, Mikio Takeuchi, Olivier Tardieu. Proceedings of the ACM SIGPLAN Symposium on Principles and Practice of Parallel Programming (PPoPP'14), Feb 2014.
