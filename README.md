# Automatic-theorem-resolution

This repository contains Dafny files that verify the correctness of various polynomial reductions of famous NP-complete decision problems.

Each file contains the reduction that is specified in its name except for the reduction of Directed_Hamiltonian to Undirected_Hamiltonian, which consists of various files in one folder with the name of the reduction, and where each file contains a certain step of the reduction. The verification of this particular reduction is, at the current moment, unfinished.

The rest of the files are structured in the following way: first, the instance (i) and problems (D1 and D2) are defined, then the reduction function (f) is implemented and, lastly, the decisional equivalence D1(i)<-->D2(f(i)) is verified via a lemma called reduction_lemma, with two auxiliary lemmas, forward_lemma and backward_lemma, verifying each direction of the equivalence.

Last used Dafny version in this work: 4.9.
