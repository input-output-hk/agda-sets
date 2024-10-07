# Abstract Set Theory

An abstract set theory library for Agda. Explore it interactively [here](https://input-output-hk.github.io/agda-sets/). Its key features are:

- it contains many standard constructions of set theory and various proofs
- the theory is axiomatic, so it can be instantiated by various models, e.g. lists or unary predicates
- decidability properties can depend on the model

The main objective of this library is to provide a set theory whose proofs are fairly standard while allowing for instantiations that can be used without extra overhead compared to non-dependently typed data structures. This is not true if sets are modeled as unary predicates for example, since for `X : Set ℕ`, properties such as `0 ∈ X` are not decidable in general. If we call the property `DecEq X → ∀ x X → Dec (x ∈ X)` type-based decidability, then we have the following table of features of models:

| Model            | Type-based decidability | Axiom of infinity | Axiom of finiteness |
|------------------|-------------------------|-------------------|---------------------|
| List             | ✓                       | ❌                | ✓                   |
| Unary predicates | ❌                      | ✓                 | ❌                  |
