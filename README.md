# Formalization of Pillai's Conjecture in Lean 4
I have formalized the reduction of Pillai's Conjecture to Baker's Theorem and Thue's Theorem. This code proves that the set of all integer solutions (x, y, p, q) for x^p - y^q = k is finite, provided the exponents are at least 3.

# Pillai's Conjecture Formalization in Lean 4

This repository contains a formal verification of the finiteness of solutions to the Pillai equation $x^p - y^q = k$.

## Overview
The proof strategy reduces the problem to two major results in number theory:
1. **Baker's Theorem** on linear forms in logarithms (used to bound the exponents $p$ and $q$).
2. **Thue's Theorem** on the finiteness of integer points on curves of genus $\ge 1$.

By combining these, we establish that for any fixed $k \neq 0$, the set of solutions $(x, y, p, q)$ with $p, q \ge 3$ is finite.

## Structure
- `Pillai.lean`: The core formalization using Lean 4 and Mathlib.
