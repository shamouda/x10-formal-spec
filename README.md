# x10-formal-spec
Formal specification for some modules in the X10 runtime system using TLA+

We use TLA+ to formally specify how certain modules are implemented and to prove the correctness of the implementation. Up until November 6th, 2017, we specified the following modules: <br />
1) The finish construct default implementation <br />
2) The finish construct SPMD implementation <br />
3) The finish construct centralized resilient implementation (Place0 Finish) <br />
4) Part of the work-stealing scheduler that orchestrates finish execution <br />
