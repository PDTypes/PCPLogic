PCPLogic
--------

This repository contains the code used in the Proof-Carrying Logic paper.

The PCPLogic.agda file describes our proof system and contains all proofs. 

The PCPLogic_no_equality.agda contains all rules except for the equality extension and is used for domains that have no equalities for efficiency.

### Requirements 

This code is tested and compiled with the following:

Agda version 2.6.1

-- Libraries 

Agda Standard Library version 1.4-dev
Agda Prelude master branch as of 13/04/20

It should be noted that the prelude library is only used in instantiations of 
our system so you can compile PCPLogic.agda without it. The main use of the 
prelude library is to automatically derive equality.

### Examples
All examples used in the paper are contained in the examples folder. 

These folders contain the:

- PDDL problem specification.
- PDDL domain specification.
- Generated Agda file.
- Extracted code binary (if applicable)
- A run.lisp file used for automation.

### Automation


### Extraction (TBD)
