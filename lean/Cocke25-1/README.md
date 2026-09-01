# Cocke25-1 — A Möbius function on the Centralizer Lattice

**Paper:** William Cocke, Mark L. Lewis, Ryan McCulloch, *A Möbius function on the Centralizer Lattice*, arXiv:2512.13839v2.
**arXiv:** [https://arxiv.org/abs/2512.13839v2](https://arxiv.org/abs/2512.13839v2)
**Source:** Ryan McCulloch et al., *A Möbius function on the Centralizer Lattice*, arXiv:2512.13839v2 ([https://arxiv.org/abs/2512.13839v2](https://arxiv.org/abs/2512.13839v2)); main.tex lines cited throughout.
**Lean library:** `Cocke25_1`, root module `Cocke25_1.lean`, sources in `Cocke25_1/`.
**Verification:** `make` green, zero `sorry` (verified 2026-08-26).

## Overview

The paper defines a Möbius function on the poset of element centers $\mathcal{Z}(G) \cup \{\mathbf{Z}(G)\}$ of a finite group $G$, ordered by containment, and uses it to obtain congruence results about centralizers in $p$-groups. The main theorem (Theorem `thm: Mob`, main.tex lines 452--468) states that $\sum_{Z \in \mathcal{Z}(G),\, Z \subseteq H} \mu(\mathbf{Z}(Z)) \equiv -1 \bmod p$ for any proper subgroup $H$ of a nonabelian $p$-group $G$; a dual corollary (`intro: Mob`, main.tex lines 78--81) sums over centralizers containing $H$. The paper also characterizes $F$-groups (Corollary `cor: non_ab_F-Gp`, main.tex lines 476--487) and proves that every vertex of the centralizer graph $\Gamma_{\mathcal{Z}}(G)$ has degree divisible by $p$ (Corollary `cor: cent_graph_degree`, main.tex lines 517--523). The formalization covers every printed statement of the paper: the lattice theorem (Section `sec: op`), the element-center machinery (Section `sec: elems`), and the Möbius congruences (Section `sec: Moby`).

## File-to-paper mapping

The Lean source files live in `Cocke25_1/`. The module directory name is `Cocke25_1` (PAPER_REF `Cocke25-1` with `-` → `_`).

### `Cocke25_1/Galois.lean` — The centralizer Galois connection (main.tex lines 178--237)

Formalization of Section `sec: op` ("The map $\mathbf{C}_G(\cdot)$ and the centralizer lattice"), opening chain:

- `centralizer_galois_self_iff` (Proposition `prop: Galois`, main.tex lines 206--214): the pair $(\mathbf{C}_G(\cdot), \mathbf{C}_G(\cdot))$ is an order-reversing Galois connection, encoded as the plain iff $T \subseteq \mathbf{C}_G(S) \leftrightarrow S \subseteq \mathbf{C}_G(T)$ (mathlib's `GaloisConnection` would require `OrderDual` transport).
- `triple_g` (Proposition `prop: triple_g`, main.tex lines 219--221): for an order-reversing self-map $g$ of a poset such that $(g,g)$ is a Galois connection, $g(g(g(x))) = g(x)$.
- `triple_C_centralizer` (Corollary `cor: triple_C`, main.tex lines 229--231): $\mathbf{C}_G(\mathbf{C}_G(\mathbf{C}_G(S))) = \mathbf{C}_G(S)$, proved element-wise.

Standalone; nothing downstream consumes `triple_g` directly, but `triple_C` feeds the lattice theorem.

### `Cocke25_1/CentLattice.lean` — The centralizer lattice $\mathfrak{C}(G)$ (main.tex lines 178--263)

Builds on `Galois.lean` to establish that $\mathfrak{C}(G)$ (the fixed points of $\mathbf{C}_G^2$) is a lattice:

- `centralizerSet`, `cclosure`, `centralizers` (main.tex lines 180--183): the closure operator $\mathbf{C}_G(\mathbf{C}_G(\cdot))$, the set of centralizers $\mathfrak{C}(G)$.
- `centralizerSet_mono` (Lemma `lem: contain`, main.tex lines 105--107): $\mathbf{C}_G$ is order-reversing.
- `centralizerSet_union` (Gap lemma **G2**, main.tex line 263): $\mathbf{C}_G(S \cup T) = \mathbf{C}_G(S) \cap \mathbf{C}_G(T)$.
- `inter_mem_centralizers` / `join_mem_centralizers` / `instLatticeCentralizers` (Theorem part (1), main.tex line 185; meet/join formulas credited to Schmidt's lattice work at tex line 263, Gap lemma **G1**): $\mathfrak{C}(G)$ is a lattice with meet $= H \cap K$ and join $= \mathbf{C}_G(\mathbf{C}_G(H) \cap \mathbf{C}_G(K))$.
- `cclosure_eq_of_mem_centralizers` (Theorem part (3), main.tex line 187): $\mathbf{C}_G(\mathbf{C}_G(H)) = H$ for $H \in \mathfrak{C}(G)$.
- `mem_centralizers_iff` / `subset_comm_of_mem_centralizers` (Proposition `prop: cent_basic` items (1) and (3), main.tex lines 242--244).
- `centralizerSelfMap_map` / `centralizerSelfMap_antitone` / `centralizerSelfMap_bijective` (Corollary `cor: bij`, main.tex lines 259--261).

### `Cocke25_1/Basic.lean` — Element-center definitions (main.tex lines 371--373)

Definitions from Section `sec: elems`:

- `elementCenter` (main.tex line 371): $\mathbf{Z}(a) := \mathbf{C}_G(\mathbf{C}_G(a))$.
- `elementCenterClass` (main.tex line 373): $\mathbf{Z}^*(g) := \{x \in G \mid \mathbf{Z}(x) = \mathbf{Z}(g)\}$.

Depends on `CentLattice.lean` for `cclosure`.

### `Cocke25_1/Fibers.lean` — Fibers of the centralizer map (main.tex lines 114--294)

Formalization of Propositions `prop: cent_union_int_1`, `prop: equiv_C-CC`, `prop: unique_cent`, and `prop:join_nice`:

- `centralizerSet_sUnion` / `sUnion_centralizerSet_subset` (Proposition `prop: cent_union_int_1` items (1) and (2), main.tex lines 114--119): the centralizer of a union is the intersection of centralizers.
- `centralizerSet_eq_iff_cclosure_eq` (Proposition `prop: equiv_C-CC`, main.tex lines 310--312): equal element centralizers iff equal double centralizers.
- `centralizerFiber_sUnion_mem` / `sUnion_centralizerFiber_eq` (Proposition `prop: unique_cent`, main.tex lines 271--278): fibers $\mathfrak{F}_{\mathbf{C}_G(S)}$ are closed under arbitrary unions and their union is $\mathbf{C}_G(\mathbf{C}_G(S))$.
- `sup_eq_centralizerSet_inter` (Proposition `prop:join_nice`, main.tex lines 285--291): $H \vee K = \mathbf{C}_G(A \cap B)$ when $H = \mathbf{C}_G(A)$, $K = \mathbf{C}_G(B)$.

### `Cocke25_1/ElemCenters.lean` — Element centers and the $\mathbf{Z}^*$-decomposition (main.tex lines 298--419)

Formalization of Section `sec: elems` and the opening of Section `sec: Moby`:

- `cclosure_abelian_iff` (Proposition `prop: cent_ab`, main.tex lines 357--363): $\mathbf{C}_G^2(S)$ abelian iff $\langle S \rangle$ abelian.
- `elementCenter_abelian` (Corollary `cor: abelian_cent`, main.tex lines 367--371): $\mathbf{Z}(a) = \mathbf{C}_G^2(a)$ is abelian.
- `centralizerSet_upper` (+ `upperStars`, `starFiber`, `upperStars_subset_X`, etc.) (Proposition `prop: upper`, main.tex lines 322--334): $H = \mathbf{C}_G(U_H^*)$ for an abstract representative set.
- `starFiber_sUnion_mem` / `sUnion_starFiber_eq` / `upperStars_sup` (Proposition `prop: stars`, main.tex lines 339--353): fiber and upper-star closure properties mirroring `unique_cent`/`join_nice$ inside $X$.
- `elementCenterClass_subset_elementCenter` (Proposition `prop: g_in_Z`, main.tex lines 377--383): $\mathbf{Z}^*(g) \subseteq \mathbf{Z}(g)$.
- `zstars_eq` / `zstars_eq_centralizerForm` / `elementCenterClass_disjoint` (Theorem `thm: z_stars`, main.tex lines 387--399): $H = \bigsqcup_{\mathbf{Z}(x) \subseteq H} \mathbf{Z}^*(x)$, disjoint over distinct classes.
- `zstars_fin_eq` / `zstars_fin_disjoint` (Corollary `cor: z_stars_fin`, main.tex lines 403--405): finite decomposition into $\mathbf{Z}^*$-classes plus $\mathbf{Z}(G)$.
- `elementCenterClass_mul_center` / `natCard_elementCenterClass_eq` / `natCard_center_dvd_natCard_elementCenterClass` (Lemma `lem: cen_divides_stars`, main.tex lines 411--419): $|\mathbf{Z}(G)|$ divides $|\mathbf{Z}^*(g)|$ via cosets.
- `centralizerSet_mul_center` / `mem_elementCenterClass_mul_center` (the key algebraic step, main.tex line 416): multiplying by a central element preserves the $\mathbf{Z}^*$-class.
- `exists_zstars_reps` / `repProps` / `centralizerSet_closure` / `centralizerSet_eq_iInter_singletons` / `subset_singleton_centralizerSet_iff` (supporting infrastructure for representative sets and singleton centralizers).

### `Cocke25_1/Moebius.lean` — The Möbius function on the element-center poset (main.tex lines 407--451)

Formalization of Section `sec: Moby`: the poset $\mathcal{Z}(G) \cup \{\mathbf{Z}(G)\}$ under containment, mathlib's incidence-algebra Möbius function, and the counting machinery:

- `IsElementCenter` / `elementCenterSet` / `centerBot` / `centerFinset` (main.tex lines 421--427): the element-center poset as a subtype of `Set G`, with bottom $\hat{0} = \mathbf{Z}(G)$.
- `centerMoebius` (main.tex lines 421--427): the Möbius function $\mu$ on the poset, defined as mathlib's `IncidenceAlgebra.mu` seeded at `centerBot`.
- `starCosetCount` / `natCard_elementCenterClass_eq_mul` (main.tex line 412): the quotient $|\mathbf{Z}^*(g)|/|\mathbf{Z}(G)|$ encoded as the number of cosets of $\mathbf{Z}(G)$ meeting $\mathbf{Z}^*(g)$.
- `centerMoebius_center` (base case, main.tex line 424): $\mu(\mathbf{Z}(G)) = 1$.
- `centerMoebius_eq_neg_sum` (Möbius recurrence, main.tex lines 423--427): $\mu(X) = -\sum_{Y < X} \mu(Y)$, read off `IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne` via the `sum_mu_Ico_eq_centerProperInside` bridge.
- `centerMoebius_sum_eq_neg_one` (exact inversion, main.tex lines 452--456): $\sum_{x \in (\hat{0}, X]} \mu(\hat{0}, x) = -1$ as an equality of integers, from `IncidenceAlgebra.sum_Icc_mu_right`.
- `exists_pos_index_mul` (p-group index step, main.tex line 443): in a finite $p$-group, a proper subgroup inclusion divides the order by a factor divisible by $p$.
- `intSum_modEq` / `intModEq_of_add_eq_zero` (congruence machinery for Finset sums).
- `centerMoebius_sum_modEq` / `centerMoebius_sum_modEq_canon`: the canonical-center-Finset form of the congruence.

### `Cocke25_1/MoebiusP.lean` — The counting congruences of Proposition `prop: p-Mob` and the main theorem (main.tex lines 430--523)

Formalization of Proposition `prop: p-Mob`, Theorem `thm: Mob`, and its corollaries:

- `centerMoebius_sum_modEq` / `centerMoebius_sum_modEq_canon` (Theorem `thm: Mob` item (1), main.tex lines 452--468): $\sum_{Z \in \mathcal{Z}(G),\, Z \subseteq H} \mu(\mathbf{Z}(Z)) \equiv -1 \bmod p$; canonical center-Finset form with rep-set independence via `Finset.sum_bij`.
- `centerMoebius_dual_sum_modEq` (Theorem `intro: Mob` / `thm: Mob` item (2), main.tex lines 78--81): the dual congruence over centralizers; the bridge `elemCentralizer_ge_iff_center_le` reindexes the sum.
- `starCosetCount_modEq_moebius` (Proposition `prop: p-Mob`, main.tex lines 430--448): $|\mathbf{Z}^*(g)|/|\mathbf{Z}(G)| \equiv \mu(\mathbf{Z}(g)) \bmod p$; strong induction on $|\mathbf{Z}(g)|$ via `Nat.strongRecOn`, with `moebius_split` and `exists_pos_index_mul`.
- `IsFGroup` / `centerMoebius_eq_neg_one` / `card_canonCentersBelow_modEq` (Corollary `cor: non_ab_F-Gp`, main.tex lines 476--487): $F$-groups have $\mu(Z) = -1$ on every non-central center, forcing the count $\equiv 1 \bmod p$.
- `centralizerGraphNbrs` / `mem_centralizerGraphNbrs` / `card_centralizerGraphNbrs` / `card_commutingGraphNbrs` / `card_transversalGraphNbrs` / `centralizerGraphDegree_modEq` (Proposition `prop: cent_graph_degree` and its pieces, main.tex lines 501--523): neighbor-set cardinalities and the degree divisibility-by-$p$ result.

## Module dependency graph

```
Cocke25_1.lean  (root, imports everything)
├── Cocke25_1.Galois        (centralizer Galois connection; mathlib only)
├── Cocke25_1.CentLattice   → Galois  (centralizer lattice 𝔄(G); Gap lemmas G1/G2)
├── Cocke25_1.Basic         → CentLattice  (element centers Z(a), Z*(g))
├── Cocke25_1.Fibers        → CentLattice  (union/intersection formulas, fibers, join_nice)
├── Cocke25_1.ElemCenters   → Basic, Fibers  (element-center machinery, z_stars, cen_divides_stars)
├── Cocke25_1.Moebius       → ElemCenters  (Möbius function, recurrence, exact inversion)
└── Cocke25_1.MoebiusP      → Moebius  (prop: p-Mob, thm: Mob, cor: non_ab_F-Gp, cent_graph_degree)
```

## Mathlib dependencies

The project pins mathlib at tag `v4.24.0`, commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, and uses Lean 4.24.0. Principal mathlib namespaces used: `Mathlib.GroupTheory.Subgroup.Centralizer`, `Mathlib.Combinatorics.Enumerative.IncidenceAlgebra`, `Mathlib.GroupTheory.PGroup`, `Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Algebra.Group.Commute.Basic`, `Mathlib.Data.Finset.Max`, `Mathlib.Data.Fintype.EquivFin`, `Mathlib.GroupTheory.Coset.Card`, `Mathlib.Order.Interval.Finset`.

## Encoding deltas

1. **Galois connection**: the paper defines a Galois connection as a pair of order-*reversing* maps; mathlib's `GaloisConnection` assumes monotone maps. `prop: Galois` is encoded as the equivalent plain iff $T \subseteq \mathbf{C}_G(S) \leftrightarrow S \subseteq \mathbf{C}_G(T)$.
2. **`prop: triple_g` hypothesis**: the paper's "(g,g) is an order-reversing Galois connection" becomes `∀ a b, b ≤ g a ↔ a ≤ g b` on an antitone self-map of a `PartialOrder`.
3. **`cor: triple_C`**: proved element-wise rather than by transporting the abstract `triple_g` result, since the concrete proof is shorter.
4. **$\mathfrak{C}(G)$ encoding**: the centralizer lattice is encoded as `centralizers G := {T | cclosure T = T}` (fixed points of $\mathbf{C}_G^2$ on `Set G`), not as a subtype of `Subgroup G`; membership is definitionally the fixed-point equation.
5. **Möbius function**: mathlib's `IncidenceAlgebra.mu` on the element-center poset (hand-built `LocallyFiniteOrder` instance); the exact inversion identity `IncidenceAlgebra.sum_Icc_mu_right` makes `thm: Mob` an exact equality rather than a congruence.
6. **Nonempty hypotheses dropped**: where the paper assumes nonempty families, the element-wise argument works without it (e.g., `centralizerSet_sUnion`).
7. **`lem: cen_divides_stars` coset clause**: encoded as a product identity $\mathbf{Z}^*(g) \cdot \mathbf{Z}(G) = \mathbf{Z}^*(g)$ rather than via finiteness; the cardinality clause uses `Subgroup.card_mul_eq_card_subgroup_mul_card_quotient`.

## Gap lemmas (all discharged in-project)

| # | Statement | Disposition | File |
| --- | --- | --- | --- |
| G1 | Meet/join formulas on $\mathfrak{C}(G)$: $H \wedge K = H \cap K$, $H \vee K = \mathbf{C}_G(\mathbf{C}_G(H) \cap \mathbf{C}_G(K))$ (credited to Schmidt's lattice work at tex line 263) | `inter_mem_centralizers`, `join_mem_centralizers`, `instLatticeCentralizers` | `CentLattice.lean` |
| G2 | $\mathbf{C}_G(S \cup T) = \mathbf{C}_G(S) \cap \mathbf{C}_G(T)$ (mathlib has only the `Set.centralizer` version, not at carrier level) | `centralizerSet_union` | `CentLattice.lean` |

## Verified statements (complete)

| Paper statement | main.tex lines | Lean target | File |
| --- | --- | --- | --- |
| `prop: Galois` | 206--214 | `centralizer_galois_self_iff` | `Galois.lean` |
| `prop: triple_g` | 219--221 | `triple_g` | `Galois.lean` |
| `cor: triple_C` | 229--231 | `triple_C_centralizer` | `Galois.lean` |
| Thm part (1) ($\mathfrak{C}(G)$ lattice) | 182--189 | `instLatticeCentralizers` | `CentLattice.lean` |
| Thm part (2) (antitone bijection) | 186 | `centralizerSelfMap_antitone` / `centralizerSelfMap_bijective` | `CentLattice.lean` |
| Thm part (3) ($\mathbf{C}_G^2(H) = H$) | 187 | `cclosure_eq_of_mem_centralizers` | `CentLattice.lean` |
| `prop: cent_basic` items (1),(3) | 242--244 | `mem_centralizers_iff` / `subset_comm_of_mem_centralizers` | `CentLattice.lean` |
| `cor: bij` | 259--261 | `centralizerSelfMap_map` | `CentLattice.lean` |
| `prop: cent_union_int_1` items (1),(2) | 114--119 | `centralizerSet_sUnion` / `sUnion_centralizerSet_subset` | `Fibers.lean` |
| `prop: equiv_C-CC` | 310--312 | `centralizerSet_eq_iff_cclosure_eq` | `Fibers.lean` |
| `prop: unique_cent` | 271--278 | `centralizerFiber_sUnion_mem` / `sUnion_centralizerFiber_eq` | `Fibers.lean` |
| `prop:join_nice` | 285--291 | `sup_eq_centralizerSet_inter` | `Fibers.lean` |
| `prop: cent_ab` | 357--363 | `cclosure_abelian_iff` | `ElemCenters.lean` |
| `cor: abelian_cent` | 367--371 | `elementCenter_abelian` | `ElemCenters.lean` |
| `prop: g_in_Z` | 377--383 | `elementCenterClass_subset_elementCenter` | `ElemCenters.lean` |
| `thm: z_stars` | 387--399 | `zstars_eq` / `zstars_eq_centralizerForm` / `elementCenterClass_disjoint` | `ElemCenters.lean` |
| `cor: z_stars_fin` | 403--405 | `zstars_fin_eq` / `zstars_fin_disjoint` | `ElemCenters.lean` |
| `lem: cen_divides_stars` | 411--419 | `elementCenterClass_mul_center` / `natCard_elementCenterClass_eq` / `natCard_center_dvd_natCard_elementCenterClass` | `ElemCenters.lean` |
| `prop: p-Mob` | 430--448 | `starCosetCount_modEq_moebius` | `MoebiusP.lean` |
| `thm: Mob` item (1) | 452--468 | `centerMoebius_sum_modEq` / `centerMoebius_sum_modEq_canon` | `MoebiusP.lean` |
| `intro: Mob` / `thm: Mob` item (2) | 78--81 | `centerMoebius_dual_sum_modEq` | `MoebiusP.lean` |
| `cor: non_ab_F-Gp` | 476--487 | `card_canonCentersBelow_modEq` | `MoebiusP.lean` |
| `prop: cent_graph_degree` | 501--523 | `centralizerGraphNbrs` / `card_centralizerGraphNbrs` / `card_commutingGraphNbrs` / `centralizerGraphDegree_modEq` | `MoebiusP.lean` |
| `intro: cent_graph_degree` | 85--87 | `centralizerGraphDegree_modEq` (same statement) | `MoebiusP.lean` |

## Axiom footprint

All verified statements have `#print axioms` in `[propext, Classical.choice, Quot.sound]` or a subset thereof; `triple_g` is axiom-free. No `sorry` remains.
