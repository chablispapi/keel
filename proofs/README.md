# Keel Core in Agda

λK₁ from `spec/core.md` §1: syntax, declarative typing, big-step semantics, and the
statement of preservation (Theorem 1). There are no proofs yet: the theorems are postulates.

Check everything with `agda Everything.agda` (Agda 2.8, standard-library 2.4).

| Module | Spec |
|---|---|
| `Keel/Syntax.agda` | §1.1 syntax, §1.2 kinds |
| `Keel/Typing.agda` | §1.2 rule 1, §1.3 declarative rules |
| `Keel/Semantics.agda` | §1.4 |
| `Keel/Theorems.agda` | §1.5 statements |

Variables are de Bruijn indices. A context keeps its length under a split, and a linear
binding owned by the other side shows up as a hole.
