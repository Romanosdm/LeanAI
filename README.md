# LeanAI

This repository contains Lean 4 and Mathlib proofs developed while learning to formalize mathematics. The exercises cover logic, algebra, linear algebra, and analysis. My longer-term goal is to formalize selected results from my research papers and mathematical lemmas that I use regularly.

## Selected proofs

- **Group homomorphisms — `week5_injective_of_ker_eq_bot`:** A group homomorphism with trivial kernel is injective. The proof shows that if $f(x)=f(y)$, then $xy^{-1}$ belongs to the kernel, so $xy^{-1}=1$ and hence $x=y$.
- **Linear maps — `week6_injective_of_ker_eq_bot`:** A linear map with trivial kernel is injective. This follows the same pattern: $f(x)=f(y)$ implies $x-y$ belongs to the kernel, so $x-y=0$.
- **Limits and continuity — `week7_sequence_continuous_comp`:** If a sequence $u_n$ converges to $a$ and $g$ is continuous, then $g(u_n)$ converges to $g(a)$. The Lean proof composes the limit of the sequence with the limit provided by continuity.

## Checking the proofs

The project uses Lean 4 and Mathlib. From the project root, run:

```text
lake build
lake env lean LeanAI/Week05.lean
lake env lean LeanAI/Week06.lean
lake env lean LeanAI/Week07.lean
```

Checking the individual files is useful because `lake build` may not compile every exercise file unless it is included in the project’s build targets.

## Future work

I plan to extend this learning portfolio with formalizations of selected results from my research and of useful background theorems. These are future goals, not results claimed to be formalized in this repository yet.