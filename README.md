The Coq formal proof development accompanying APLAS 2019 submission: Pumping, With or Without Choice.

This project was compiled with The Coq Proof Assistant, version 8.8.2 (December 2018) built with OCaml 4.02.3. 

To install and build: 

$ git clone https://github.com/atufchoice/blockpump

$ touch .depend

$ make dep

$ make

The development is organized as follows: 

lib.v : supplementary library for nats, lists and sigma types
finite.v : classical set theoretic library for EPR's proof with choice
pigeonhole.v : pigeonhole principle proof
definitions.v : formal language related definitions
jaffe.v : Jaffe's pumping lemma
closure.v : block pumpable language closure properties
ramsey.v : two-color Ramsey's theorem for sets and specialized two-color Ramsey's theorem for breakpoint sets
lemma2choice.v : classical proof of EPR's lemma 2 (Print Assumptions on line 51) 
lemma2nochoice.v : choice-free proof of EPR's lemma 2 (Print Assumptions on line 1314)
lemma2nochoicebool.v : choice-free proof of EPR's lemma 2 with language as word -> bool
lemma3.v : proof of EPR's lemma 3
toregularity.v : completing the commutative triangle 
