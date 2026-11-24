# Consistency of a group presentation for the Monster Lie algebra

This repository contains a machine-checked proof that the relations of the group $G_{\mathfrak m}$, a group defined by generators and relations and associated with the Monster Lie algebra, are consistent, in the sense that no generator is forced to be trivial. For every coefficient function $c\colon\mathbb N\to\mathbb N$, the generators $X_{-1}(u)$, $Y_{-1}(u)$, $X_{\ell,jk}(u)$, and $Y_{\ell,jk}(u)$ are non-trivial for $u\neq0$, and $H_1(s)$ and $H_2(s)$ are non-trivial for $s\neq1$. The proof maps the real generators to $\mathrm{GL}_2(\mathbb C)$ and, for each pair $X_{\ell,jk}, Y_{\ell,jk}$, constructs a representation on $\mathbb C[x_0,x_1,z]$ in which the pair acts by transvections between two monomials and every other imaginary generator acts trivially. The result was formalized and proved with the AIProver orchestration.

| File | Contents |
|---|---|
| `gm_consistent_proof.lean` | The complete Lean 4 proof. The theorem `solution` states the non-triviality of every generator family. |
| `gm_consistent_informal.tex`, `.pdf` | The theorem and its proof written as a mathematical paper, with each lemma matched to the Lean declaration that states it. |
| `gm_consistent_report.tex`, `.pdf` | The verification report, which presents the formal definitions, the target statement, every lemma with its Lean proof, and the independent faithfulness review. |

The Lean file compiles with Lean 4 v4.23.0 and Mathlib v4.23.0, without `sorry`, and depends only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. It can be checked inside any Lake project that depends on that Mathlib version by running `lake env lean gm_consistent_proof.lean`.
