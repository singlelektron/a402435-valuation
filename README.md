# The exact 2-adic valuation of OEIS A386381

This is a Lean 4 proof of Peter Luschny's conjecture A402435 about the diagonal of Mikhail Kurkov's weighted Entringer triangle. The proof was developed with AI assistance and checked locally with Lean and Mathlib v4.36.0. Human review is pending. [A402435](https://oeis.org/A402435) · [A386381](https://oeis.org/A386381)

Let $D(n)$ be the diagonal entry in row $n$ and let $v_2$ denote the exponent of 2. For every $m,j\ge 0$, the two branches are

$$
\begin{aligned}
v_2(D(2m+1)) &= v_2((2m)!),\\
v_2(D(2j+2)) &= 2j + e_{j\bmod 8},\qquad (e_0,\ldots,e_7)=(0,1,3,0,0,1,2,0).
\end{aligned}
$$

Together they give the OEIS formula for every positive index. The formal theorem is `MathMiner.A402435.solution`. [Statement and triangle definition](MathMiner/Problems/A402435/Statement.lean) · [Lean proof](MathMiner/Problems/A402435/Proof.lean) · [Proof walkthrough](PROOF.md)

## Reproduce the check

With [elan](https://github.com/leanprover/elan) installed, run these commands from the repository root.

```sh
lake exe cache get
lake build
lake env lean scripts/Audit.lean
```

The audit checks all project declarations and prints the axioms of the final theorem. Its dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

## Related work

ProveIt's *Research report 180* derived the generating-function equation in October 2026. Luschny later recorded it in A386381. TrureTuring also stated the power-of-two subcase as a conjecture. The proof here starts from the triangle recurrence and uses a parity decomposition and a recurrence modulo 16 to obtain the exact valuation. [Report 180](https://github.com/VladimirReshetnikov/ProveIt/blob/3d6e73ab1e4efbbfdb69b6758cade7343f075d01/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a386381-modified-entringer/article.tex#L321-L373) · [Luschny's formula](https://github.com/oeis/oeisdata/blob/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq/A386/A386381.seq#L14-L16) · [Power-of-two conjecture](https://github.com/the-omega-institute/trureturing/issues/34244#issuecomment-7174064769)
