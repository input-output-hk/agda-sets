# Abstract Set Theory

An abstract set theory library for Agda. It contains many standard constructions of set theory that are derived from axioms inspired by ZF and various proofs about them. This theory can then be instantiated by various models, e.g. lists or unary predicates (to be implemented). A key feature of this library is that the decidability properties can depend on the model. In the list model for example, membership in an arbitrary set of natural numbers is decidable, while in the predicate model it isn't. As a consequence, this library can be used for finite sets in a program that needs to run as well as for reasoning about infinite sets.