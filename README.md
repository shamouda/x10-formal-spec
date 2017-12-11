# x10-formal-spec
Formal specification for some modules in the X10 runtime system using TLA+

We use TLA+ to formally specify how certain modules are implemented and to prove the correctness of the implementation. Up until November 6th, 2017, we specified the following implementations of the finish
construct: <br />
1) The default implementation <br />
2) The SPMD implementation <br />
3) The resilient centralized implementation (Place0 Finish) <br />
4) A buggy resilient distributed implementation used in PPoPP14 paper <br />
5) An implementation that fixes the bugs in (4)   <br />

We are currectly working on another implementation, that aims at reducing the communication 
cost in (4) <br>
