# CS499 Mechanical Reasoning
All team project code for Fall 2016 mechincal reasoning course. 

Course text: 
Semantics with Application: 10.1007/978-1-84628-692-6
Software Fondations: https://www.cis.upenn.edu/~bcpierce/sf/current/index.html
## Project 1 
A partial implementation of the formal proof described by Painter and McCarthy using Coq. The goal of McCarthy was to obtain machine-checked proofs of correctness for compilers. This work is not machine-checked but, unlike most pen-and-paper work, it is quite detailed.
## Project 2 
An implementation of an abstract lanuage using a state, an evaluation stack, and a sequence of instructions. The stack symbols are either of type bool or Z (i.e a number) and the state is defined as a total function from id to Z. The lanuage is formaly desribed in the course text ch 4. The instruction syntax is defined using an inductive defition and the sematic function is defined using operational semantics. The semantic rules can be founded in Table 4.1 of the text. 
