# McCulloch26-2 — Formalization of *An answer regarding automorphisms of finite abelian groups*

- **Title:** An answer regarding automorphisms of finite abelian groups
- **Author:** Ryan McCulloch
- **arXiv:** [https://arxiv.org/abs/2603.29299](https://arxiv.org/abs/2603.29299)
- **Cached source:** `docs/arxiv/2603.29299/An_Answer.tex`
- **Lean library:** `McCulloch26_2` (root module `McCulloch26_2.lean`, sources in `McCulloch26_2/`)
- **Status:** `make` green, zero `sorry`, verified 2026-09-19.

## Overview

The paper answers negatively a question (also Kourovka notebook \#21.97): is every
positive rational $r$ realized as $|\mathrm{Aut}(G)|/|G|$ for some finite abelian
group $G$? The main results are: if $r = a/b = |\mathrm{Aut}(G)|/|G|$ with $a, b$
coprime, then $b$ is **squarefree** (Theorem 1); every power of $2$ is realized
(Theorem 2); and **no odd prime** can equal $|\mathrm{Aut}(G)|/|G|$ (Theorem 3).

The argument is a clean chain off a single engine formula for $|\mathrm{Aut}(G)|$
when $G = \mathbb{Z}_{p^{e_1}} \times \cdots \times \mathbb{Z}_{p^{e_n}}$ is a finite
abelian $p$-group (Proposition `prop: form`), from which a `$p$-adic` valuation
formula (Proposition `prop: dc`) and a five-case dichotomy for the ratio
(Proposition `prop: class`) are derived, then lifted to multi-prime groups via the
fundamental theorem of finite abelian groups.

This formalization proves, in Lean, **every statement the paper itself derives**,
at an arithmetic "data level" where a finite abelian $p$-group is modeled by its
sorted exponent sequence. Two facts the paper cites from outside sources and does
not re-prove — the Hillar-Rhea automorphism-counting formula (Proposition
`prop: form`) and the coprime-order splitting
$\mathrm{Aut}(G\times H)=\mathrm{Aut}(G)\times\mathrm{Aut}(H)$ — are kept as
explicit unproved *gap lemmas* (see [Gap lemmas](#gap-lemmas)). The two closing
projects (Project 1, classify all realized rationals; Project 2, nilpotent version)
are open research problems and are out of scope.

## File-to-paper mapping

### `Basic.lean` — Exponent-sequence model; Proposition `prop: form` (main.tex lines 133–135)

Models a finite abelian $p$-group by its sorted positive exponent sequence
$f : \mathrm{Fin}\ n \to \mathbb{N}$ standing for
$G \cong \mathbb{Z}_{p^{f(0)}} \times \cdots \times \mathbb{Z}_{p^{f(n-1)}}$. Defines
the block indices $d_r = \max\{s : e_s = e_r\}$ and $c_r = \min\{s : e_s = e_r\}$ of
Proposition `prop: form`, the three products, and the group order, so the ratio
$|\mathrm{Aut}(G)|/|G|$ can be computed.

- `Sorted f` (main.tex lines 133–135): the paper's `1 ≤ e_1 ≤ ⋯ ≤ e_n`.
- `Pos f` (main.tex lines 133–135): positivity `0 < f i`.
- `BlockTop f r` / `BlockBot f r` (main.tex line 134): the paper's $d_r$, $c_r$ as zero-based indices, with the self/order lemmas (`block_top_self`, `le_block_top`, `block_bot_self`, `block_bot_le`, `block_top_ge`, `block_bot_le'`, `block_top_eq_self`, `block_bot_eq_self`, and the constant-pair/triple specializations).
- `ProdOne`, `ProdTwo`, `ProdThree` (main.tex lines 133–135): the three products $\prod (p^{d_k}-p^{k-1})$, $\prod p^{e_j(n-d_j)}$, $\prod p^{(e_i-1)(n-c_i+1)}$.
- `AutFormula p f` (main.tex lines 133–135): the full product from Proposition `prop: form`; the data-level analogue of $|\mathrm{Aut}(G)|$.

### `Formula.lean` — Valuations and divisibility; Proposition `prop: dc` (main.tex lines 151–153), proof of `prop: class` (main.tex lines 166–170)

Two engines: the `$p$-adic` valuation formula and the $(p-1)$-divisibility powering
Proposition `prop: class`.

- `prime_not_dvd_pow_sub_one` (main.tex lines 149–153): a prime never divides $p^t - 1$ for $t>0$, the core valuation argument.
- `factorization_prod_apply`, `factorization_pow_self`, `prodOne_factorization`, `prodTwo_factorization`, `prodThree_factorization` (main.tex lines 149–153): factorization bookkeeping via mathlib `Nat.factorization`.
- `pm1_dvd_pow_sub_one` (main.tex lines 149–153): each first-product factor is divisible by $p-1$; `prodOne_dvd_pm1_pow` (main.tex lines 166–170) lifts this to $(p-1)^n \mid \mathrm{ProdOne}$.
- `prop_dc_val` / `prop_dc` (main.tex lines 149–153): Proposition `prop: dc` — the largest $p$-power dividing $|\mathrm{Aut}(G)|$ equals $p^{\sum k + \sum e_j(n-1-d_j) + \sum(e_i-1)(n-c_i)}$ positionally, plus the closed triangular form.

**Delta:** the paper states `prop: dc` multiplicatively (in the $k_i, e_j$ of the
repeated-prime-classification form); the Lean statement is the positional block-index
form. The distinct-exponent printed equivalence is a noted backlog item in
`status.md`; the positional form is what `prop: class` uses.

### `PropClass.lean` — Proposition 2.4 (main.tex lines 155–164), proof (main.tex lines 166–170)

The dichotomy for the ratio of a finite abelian $p$-group: either one of four
exceptional shapes holds with an explicit rational value, or the ratio is an integer
multiple of $p(p-1)^2$.

- `ratio_case_cyclic` (main.tex line 158): $Z_p$ gives $(p-1)/p$.
- `ratio_case_two_const` (main.tex line 159): $Z_p \times Z_p$ gives $(p-1)^2(p+1)/p$.
- `ratio_case_two_dist` (main.tex line 160): $Z_p \times Z_{p^i}$, $i>1$, gives $(p-1)^2$.
- `ratio_case_three_const` (main.tex line 161): $Z_p \times Z_p \times Z_p$ gives $(p-1)^3(p+1)(p^2+p+1)$.
- `prop_class_else` (main.tex lines 166–170): transcription of the dichotomy proof — in all other cases the numerator carries $p^{a+1}(p-1)^2$, so the ratio is an integer multiple of $p(p-1)^2$.
- `prop_class` (main.tex lines 155–164): five-way assembly.
- Corollaries `den_autRatio_dvd` (each denominator divides the prime $p$), `num_autRatio_dvd_pm1` (each numerator carries $(p-1)$): the bridge facts lifting to multi-prime groups.

Supporting helpers `autFormula_eq_pow_mul`, `prodOne_eq`, `prodTwo_eq`, `prodThree_eq`,
`rat_cross`, `cop_dvd_num_of_cross`, `num_den_of_repr_nat` factor the products and
rational reps.

### `PropReal.lean` + `MultiPrime.lean` — Proposition 2.2 (main.tex lines 139–147), Theorems 1 and 2 (main.tex lines 115–121, 172)

The four families realizing small ratios, then the multi-prime total-ratio machinery.

- `block_self_pair` / `block_self_triple` (main.tex lines 139–147): block indices of strictly increasing pairs/triples are the entries themselves.
- `prop_real_1_1` (main.tex line 142): item 1 — $Z_{2^{i}} \times Z_{2^{i+1}}$ has ratio $2^{2(i-1)}$, stated for `m ≥ 0` as `(2:ℚ)^(2*m)` for the sequence `![m+1, m+2]`.
- `prop_real_1_2` (main.tex line 143): item 2 — $Z_2 \times Z_{2^i} \times Z_{2^{i+1}}$ has ratio $2^{2i+1}$, stated for `m ≥ 0` as `(2:ℚ)^(2*m+5)` for `![1, m+2, m+3]`.
- **Delta:** items 3 and 4 (ratios 2 and 8 on $Z_2 \times Z_3 \times Z_9$, $Z_2 \times Z_5 \times Z_{25}$) are not stated as standalone declarations; they are realized inside `thm2_data` as explicit witnesses. Supply chains `sorted_pair_succ`, `pos_pair_succ`, `sorted_triple_inc`, `pos_triple_inc`, `injective_fin_one`.
- `Decomp` (main.tex line 172) and `listVec` (main.tex line 172): a $p$-group as a list `(p, es)` of a prime and exponent list, converted to a `Fin`-indexed sequence; `TotalRatioL` gives the ratio of such a decomposition.
- `thm2_data` (main.tex lines 119–121, 137): Theorem 2 — every power of $2$ is realized, combining the four Proposition 2.2 families over explicit list decompositions.
- `TotalRatio pp nn ff` (main.tex line 172): the product of per-component ratios $\prod_i |\mathrm{Aut}(G_i)|/|G_i|$; `prod_dvd_prod_of_pointwise`, `den_prod_dvd`, `squarefree_prod_distinct`, `coprime_primes_ne` support the squarefree-denominator argument.
- `thm1_data` (main.tex lines 115–117, 172): Theorem 1 — the reduced denominator of the total ratio over distinct-prime components is squarefree.

### `ComponentNeOddPrime.lean` — Per-component lemma for Theorem 3 (main.tex lines 158–170, 176–182)

Per-component contradiction `autRatio p f ≠ p` for odd prime `p`, used in Theorem 3.

- `component_ne_odd_prime` (main.tex lines 176–182): for odd prime $p$ and any sorted positive sequence, the ratio of a single $p$-group cannot equal $p$; assembled from the five `prop_class` cases via `comp_ne_odd_case1`…`comp_ne_odd_case5`, each using the polynomial inequalities `sq_lt_p`, `sq_pm1_gt_sq`, `cube_pm1_gt_p`.

*Standalone:* not imported by any other module (the main Theorem 3 proof re-derives
each branch); kept as an independent, self-contained proof of this component case.

### `TwoOddComponentsImpFourDvdNum.lean` — component lemma for Theorem 3 (main.tex line 181)

- `two_odd_components_imp_four_dvd_num` (main.tex line 181): if two distinct components carry odd primes, then $4 \mid a_i a_j$ where $a_i, a_j$ are the numerators of their ratios (since each numerator carries `(p_i - 1)` and `(p_j - 1)`, both even). Imported by `Thm3/Branch1`.

### `Thm3.lean` + `Thm3/{Helpers,Branch1,Branch2,Branch3}.lean` — Theorem 3 (main.tex lines 123–125, 176–182)

No odd prime can equal $|\mathrm{Aut}(G)|/|G|$ for a finite abelian group $G$.

- `Thm3/Helpers.lean`: shared cross-branch lemmas — denominator-bounds `TotalRatio_den_dvd_prod_pp`, `den_coprime_of_distinct_primes`, `not_four_dvd_prod_distinct_primes`, the cross-multiplication identity `totalRatio_eq_iff_cross` ($\prod a_i = p \prod b_i$ from the ratio equal $p$), and the cyclic-2-component numerator facts `autRatio_two_num_of_den_two` / `autRatio_two_num_of_den_two'`, `square_dvd_two_mul_odd_prime`.
- `Thm3/Branch1.lean` — `thm3_branch_two_odd_components` (main.tex line 181): ≥2 odd components forces $4 \mid \prod a_i$ while $4 \nmid \prod b_i$, contradicting $\prod a_i = p \prod b_i$.
- `Thm3/Branch2.lean` — `thm3_branch_one_odd_component` (main.tex lines 180–182): exactly one odd component; the paper's numerator/denominator bookkeeping `b_2 = p_2`, `a_2/b_2 = (p_2-1)/p_2`, forcing the 2-component to have `b_1 = 2` and `a_1 = 3`, then $p_2 - 1 = 2$ and $p_2 = 3$, a contradiction. Backup lemmas `odd_comp_num_cases`, `four_dvd_num_impossible`, `branch2_single_core`, `branch2_pair_core`.
- `Thm3/Branch3.lean` — `thm3_branch_no_odd_components` (main.tex lines 176–182): all components are 2-groups; the ratio is a power of 2, never an odd prime. Uses `injective_prime_const_le_one`, `TotalRatio_empty`, `TotalRatio_singleton`.
- `Thm3.lean` — `thm3` (main.tex lines 123–125, 176–182): the three-way case split on the number of odd-prime components assembling the branches.

**Delta:** as with Theorem 1, Theorem 3 is formalized at the data level over a
decomposition `(pp, nn, ff)` of existing modeled components; the bridge to a real
group $G$ is via the gap lemmas below.

### `Gaps.lean` — Gap lemmas (main.tex line 131)

The two facts the paper uses but does not prove, kept as explicit `Prop`-valued gap
statements so that every conditional bridge theorem records its dependence.

- `RheaFormula p f` (main.tex lines 131–135): gap **G1** — the Hillar-Rhea formula stating $\mathrm{Nat.card}(\mathrm{AddAut}(\prod_i \mathbb{Z}_{p^{f(i)}})) = \mathrm{AutFormula}\ p\ f$, cited in the paper to Hillar-Rhea, Amer. Math. Monthly 114 (2007), 917–923 (bibliography line 198). Statement only; proving it requires counting units of matrix rings over $\mathbb{Z}/p^k$.
- `CoprimeSplit A B` (main.tex line 131): gap **G2** — $\mathrm{Nat.card}(\mathrm{AddAut}(A \times B)) = \mathrm{Nat.card}(\mathrm{AddAut}\ A)\cdot\mathrm{Nat.card}(\mathrm{AddAut}\ B)$ for coprime finite additive abelian groups.
- Conditional bridges `rhea_card`, `group_ratio_of_rhea` (main.tex lines 131–135): under `RheaFormula` the modeled ratio computes the real group's ratio.

## Module dependency graph

```
McCulloch26_2.lean  (root: re-exports the library)
├─ Basic.lean       ─  exponent-sequence model, block indices, prod defs
│    └─ Formula.lean ─  valuations & (p-1)-divisibility; prop: dc
│         └─ PropClass.lean ─  prop: class dichotomy + ratio cases + corollaries
│              └─ PropReal.lean ─  prop 2.2 items 1; explicit-ratio helpers
│                   └─ MultiPrime.lean ─  TotalRatio, thm1_data, prop_real_1_2,
│                        thm2_data (items 3,4 witnesses)
│                        ├─ ComponentNeOddPrime.lean  (standalone, unimported)
│                        └─ Thm3/
│                             ├─ Helpers.lean
│                             ├─ Branch2.lean ← Helpers
│                             ├─ TwoOddComponentsImpFourDvdNum.lean ← MultiPrime
│                             │      └─ Branch1.lean ← Helpers + TwoOdd
│                             └─ Branch3.lean ← Helpers
│                                  └─ Thm3.lean ← Helpers + Branch1/2/3
└─ Gaps.lean         ─  gap lemmas G1/G2 + conditional bridges
```

Imports match `McCulloch26_2.lean` (in order): `Basic → Formula → PropClass →
PropReal → MultiPrime → Thm3`, with `Gaps` last; `ComponentNeOddPrime` is not
imported by the root module (standalone). Dependency order follows the paper's
derivation chain: `prop: form` → `prop: dc` → `prop: class` → the theorems.

## Mathlib / toolchain

- **Lean:** `leanprover/lean4:v4.24.0` (`lean-toolchain`).
- **Mathlib:** rev `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (tag `v4.24.0`), pinned in `lakefile.toml`.
- Principal namespaces: `Nat.factorization`, `Nat.Coprime`, `Rat.num`/`Rat.den`, `Finset.prod`, `Fin` sequences, `ZMod`/`AddAut` (in `Gaps`), `Nat.Prime`, `Odd`, `Squarefree`, and `linarith`/`omega`/`nlinarith` arithmetic tactics.

## Errata

None. All statements transcribed match the printed text at the data level; the noted
discrepancies are the encoding deltas above (positional vs. printed `prop: dc` form;
Proposition 2.2 items 3–4 realized inside `thm2_data` rather than as standalone
declarations), not corrections to the paper.

## Gap lemmas

The formalization proves every statement the paper derives, but it does **not** prove
two facts the paper itself cites from outside sources:

- **G1 `RheaFormula`** — Proposition `prop: form` (main.tex lines 133–135), the Hillar-Rhea formula for $|\mathrm{Aut}(\prod_i \mathbb{Z}_{p^{f_i}})|$. Open: requires counting units of matrix rings over $\mathbb{Z}/p^k$.
- **G2 `CoprimeSplit`** — the coprime-order splitting $\mathrm{Aut}(G\times H)=\mathrm{Aut}(G)\times\mathrm{Aut}(H)$ (main.tex line 131), used at line 172 (Theorem 1) and line 181 (Theorem 3) via the fundamental theorem. Open: candidate route is Hom-triviality between coprime finite abelian groups.

Because of these, the *group-level* statements (a real group $G$) are conditional on
the gaps; the *data-level* statements proved here are unconditional. Per the
formalization's gap protocol, no statement with a Lean proof depends on an unproved
`sorry`.

## Open problems

- **Project 1** (main.tex lines 186–188): completely classify all rational numbers that appear as $|\mathrm{Aut}(G)|/|G|$ for finite abelian $G$ — open research problem, out of scope. Tracked as `docs/proofs/open/Open/McCulloch26_2_P12/` in the open-problem registry (it imports `MultiPrime`).
- **Project 2** (main.tex lines 190–192): describe the rationals realized by finite nilpotent groups — open research problem, out of scope.