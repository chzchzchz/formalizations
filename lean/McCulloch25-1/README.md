# McCulloch25-1 — Incidence Gain Graphs and Generalized Quadrangles

**Paper:** Ryan McCulloch, *Incidence Gain Graphs and Generalized Quadrangles*, arXiv:2502.01805.
**arXiv:** [https://arxiv.org/abs/2502.01805](https://arxiv.org/abs/2502.01805)
**Source:** Ryan McCulloch, *Incidence Gain Graphs and Generalized Quadrangles*, arXiv:2502.01805 ([https://arxiv.org/abs/2502.01805](https://arxiv.org/abs/2502.01805)); main.tex lines cited throughout.
**Lean library:** `McCulloch25_1`, root module `McCulloch25_1.lean`, sources in `McCulloch25_1/`.
**Verification:** `make` green, zero `sorry` (verified 2026-08-26).

## Overview

The paper introduces Construction $\mathfrak{M}$ (main.tex lines 89--99), which converts an incidence gain graph $(\Gamma,\varphi)$ — an incidence structure $(\mathscr{P},\mathscr{B},\mathrm{I})$ with a gain function $\varphi$ valued in a group $G$ acting on a nonempty set $\Lambda$ — into a new incidence structure $\mathfrak{M}(\Gamma,\varphi)$ whose points are $x_p\ (p\in\mathscr{P})$, $y_{b,\lambda}\ (b\in\mathscr{B},\lambda\in\Lambda)$ and whose lines are $z_{p,\mu}\ (p\in\mathscr{P},\mu\in\Lambda)$. The main theorem (Theorem 5, main.tex lines 193--199) states that $\mathfrak{M}(\Gamma,\varphi)$ is a generalized quadrangle iff every rho function $\rho_{b,p,\lambda}$ is bijective; when it is, the base structure is a Steiner system and $X=\{x_p\}$ is an ovoid. Theorem 7 (lines 264--274) produces an explicit family of generalized quadrangles from affine planes over arbitrary fields.

The formalization covers every printed statement environment of the paper: Proposition 1, Proposition 2 (whose proof the paper omits), Lemma 3 (all four items), Lemma 4 (per erratum E1), Theorem 5 (iff plus items 1--3 and the converse half), Proposition 6, and Theorem 7. The paper's two open problems (main.tex lines 383--389) are outside formalization scope.

## File-to-paper mapping

### `McCulloch25_1/Basic.lean` — Definitions (main.tex lines 40--85)

Transcribes the entire Definitions subsection of main.tex:

- `IncidenceStruct` (main.tex line 40): the triple $(\mathscr{P},\mathscr{B},\mathrm{I})$, with `Incident : P → B → Prop`.
- `Obj` (main.tex line 63): the sort tag `pt`/`ln` for points and lines, the objects of chains.
- `ObjInc` (main.tex line 40, symmetry folded): symmetric incidence between objects.
- `ChainSeq`, `Chain`, `Chain.refl`, `Chain.step1` (main.tex line 63): $k$-chains as data-carrying lists, with inversion lemmas `chainSeq_pair/triple/quad` and shape lemmas `zero_seq`/`one_seq`/`two_shape`.
- `IsLinearSpace` (main.tex lines 77--83): the three linear-space axioms.
- `IsSteinerSystem` (main.tex line 85): a linear space whose lines all carry exactly $k$ points, realized in `Item3.lean`.

Auxiliary lemmas live here and are used throughout: `objInc_symm`, `not_objInc_pt_pt`/`not_objInc_ln_ln`, `ChainSeq.cons`/`single`/`nil` inversion, `Chain.zero_seq`/`one_seq`/`two_shape`, `Chain.rev`, `distLe` bounds, `connLine`/`connLine_unique`, `exists_line_of`, `exists_pt_not_on_line`, `three_distinct_points`, `not_objInc_pt_pt`/`not_objInc_ln_ln`.

### `McCulloch25_1/Prop1.lean` — Proposition 1 (main.tex lines 103--126)

Switching by a function $f$ induces an incidence-structure isomorphism $\mathfrak{M}(\Gamma,\varphi)\cong\mathfrak{M}(\Gamma,{}^f\varphi)$.

- `switchPtMap` / `switchLnMap` (main.tex lines 107--108): the point-map $g_1$ and line-map $g_2$.
- `switch_key` (main.tex lines 121--123): the cancellation driving the incidence check.
- `switchIso_xz` / `switchIso_yz` (main.tex lines 114--125): the two incidence-clause equivalences.
- `switchIso` (main.tex lines 103--112): the assembled `IncidenceIso`.

Standalone; nothing downstream consumes it.

### `McCulloch25_1/Prop2.lean` — Proposition 2 (main.tex lines 130--134)

The paper omits the proof ("follows easily from Construction $\mathfrak{M}$"). This file proves it in full.

- `liftObj` (main.tex lines 130--134): base lines lift to $\mathfrak{M}$-points $y_{b,\lambda}$, base points lift to $\mathfrak{M}$-lines $z_{p,\lambda}$.
- `stepGain` (main.tex lines 52--54): per-step gain with the stored line-to-point orientation ($\delta=+1$ line-to-point, $-1$ point-to-line).
- `walkGain` (main.tex line 54): backwards walk gain, last edge leftmost.
- `stepParam` / `liftSeq` / `liftZip`: position-indexed lifting (base objects may repeat along a chain).
- `prop2_lift` / `prop2_base` / `prop2_gain` (main.tex lines 130--134): the iff split, with the furthermore clause $\lambda_k = \varphi_w\cdot\lambda_0$.

Standalone; unused by later results.

### `McCulloch25_1/Lem3.lean` — Lemma 3 (main.tex lines 153--171)

Distances and shortest-chain uniqueness for point--line pairs of $\mathfrak{M}$. All four items are proved as standalone `HasDist … ∧ unique` statements:

- `lem3_item1` (main.tex line 156): $d(x_p,z_{q,\mu})=1$, witnessed by the unique $1$-chain.
- `lem3_item2` (main.tex line 157): $d(x_p,z_{q,\lambda})=3$ with a unique $3$-chain for $p\ne q$.
- `lem3_item3` (main.tex line 158): $d(y_{b,\lambda},z_{p,\mu})=1$ when $b\ \mathrm{I}\ p$ and $\mu=\varphi(bp)\cdot\lambda$.
- `lem3_item4` (main.tex line 159): $d(y_{b,\lambda},z_{p,\mu})=3$ with a unique $3$-chain in the nonincident case.

Auxiliary definitions: `MX`/`MY`/`MZ` aliases for the $\mathfrak{M}$-point/line objects, and `MX_ne_MZ`/`MY_ne_MZ`. Uniqueness halves `unique_three_xz`, `unique_three_yz_incident` live here and feed `Thm5.lean`.

### `McCulloch25_1/Lem4.lean` — Lemma 4 (main.tex lines 173--189)

Same-sort pairs at genuine distance $2$ have a unique $2$-chain. Carries the explicit `hls : S.IsLinearSpace` hypothesis (the printed proof invokes it once, main.tex line 188) and uses the repaired hypothesis $d(u,v)=2$ exactly per erratum E1 (the printed $d\le2$ is false at $u=v=x_p$ when $|\Lambda|\ge2$). Case bash over endpoint shapes: $(x,x)$, $(x,y)$/$(y,x)$, $(y,y)$ with $b=b'$ vs $b\ne b'$, $(z,z)$.

### `McCulloch25_1/Thm5.lean` — Theorem 5 (main.tex lines 193--230)

The paper's hub: $\mathfrak{M}(\Gamma,\varphi)$ is a generalized quadrangle iff every $\rho_{b,p,\lambda}$ is bijective.

Forward machinery:

- `Chain.four_tag_eq` (main.tex line 63): parity of $4$-chains.
- `hasDist_three_of_gq`: $d(y_{b,\lambda},z_{p,\mu})=3$ for nonincident pairs inside a GQ (parity + diameter bound).
- `distLe_four`: same-sort pairs are at distance $\le 4$.
- `chain_three_missing` / `unique_three_missing`: the "missing case" of Lemma 3's forward direction.

Statements proved here:

- `thm5_converse` (main.tex lines 219--221): the GQ axioms force every $\rho_{b,p,\lambda}$ bijective; surjectivity reads $q$ off the unique $3$-chain, injectivity builds two canonical chains against the same endpoint.
- `thm5_item1` (main.tex line 196): $X=\{x_p\}$ is an ovoid, unconditional.
- `thm5_item2` (main.tex line 197): $|\mathscr{P}_b|=|\Lambda|$, stated as `Nonempty ({q // Incident q b} ≃ Λ)`.
- `thm5_item3` (main.tex line 198): finite-parameter counts ($s=\frac{v-1}{k-1}$, $t=k-1$), delegated to `Item3.lean`.
- `thm_gq_rho`: the full iff, assembled through Lemma 3 + Lemma 4 + the forward machinery.

### `McCulloch25_1/Item3.lean` — Theorem 5, item 3 (main.tex lines 198, 229, 85)

The Steiner-system parameter counts:

- `IsSteinerSystem` (main.tex line 85): $S(2,v,k)$.
- `steiner_of_gq` (main.tex lines 197, 227): under the $\rho$-hypotheses, the base space is a Steiner system.
- `thm5_item3`: assuming $\mathscr{P}$ finite, $v\ge3$, $k=|\Lambda|\ge2$, every line of $\mathfrak{M}(\Gamma,\varphi)$ carries exactly $1+s$ points and every point exactly $k$ lines.

Auxiliary counting chain: `three_distinct_points` → `finite_lines_through` (lines through $p$ inject into points $\ne p$) → `card_mem_sub_one` / `card_complement_pt` → `lines_through_count` (the double count, main.tex line 229); inside $\mathfrak{M}$, `card_line_z` ($r_p+1$), `card_point_y` ($|\mathscr{P}_b|$), `card_point_x` ($|\Lambda|$).

### `McCulloch25_1/Prop6.lean` — Proposition 6 (main.tex lines 236--258)

Under a regular action of $G$ on $\Lambda$, $\rho_{b,p,\lambda}$ is bijective iff $\rho_{b,p}$ is bijective. Injectivity transfers both ways by group-action bijections (freeness strips fixed points, transitivity moves targets). Standalone; feeds Theorem 7.

### `McCulloch25_1/Affine.lean` — Theorem 7 (main.tex lines 264--274, proof 276--379)

The affine-plane example over an arbitrary field $\mathbb{F}$:

- `AffineLn` (main.tex line 262): vertical lines $L_b$ and non-vertical lines $L_{m,b}$.
- `affIncident` / `affineStruct` (main.tex line 262): incidence of the affine plane.
- `affPhi` (main.tex lines 267--271): the gain function, values off incidence junk.
- `affConnLine_vert` / `affConnLine_slope` (main.tex line 262): connecting-line characterizations via `connLine_unique`.
- Two master computations (`rhoVal_affVert_toAdd`, `rhoVal_affSlope_toAdd`) collapse the printed proof's six walk-gain sub-cases (main.tex lines 287--350) into uniform per-line-type formulas: for $q\in L$ and $p=(x,y)$ off $L$, $L=L_v$ gives $\rho(q)=(x-v)y_q - v\,y$, and $L=L_{m,v}$ gives $\rho(q)=x\,y_q - x_q(y-v)$.
- Injectivity/surjectivity are single field cancellations (main.tex lines 304--306, 348--350, 354--360, 362--377).
- `thm_affine` assembled through `thm_gq_rho` + `prop_regular` per line 277.

## Module dependency graph

```
McCulloch25_1.lean  (root, imports everything)
├── McCulloch25_1.Basic        (definitions, no internal Lean deps beyond Mathlib)
├── McCulloch25_1.Prop1        → Basic
├── McCulloch25_1.Prop2        → Basic
├── McCulloch25_1.Lem3         → Basic
├── McCulloch25_1.Lem4         → Basic, Lem3
├── McCulloch25_1.Thm5         → Basic, Lem3, Lem4, Prop6
├── McCulloch25_1.Item3        → Thm5
├── McCulloch25_1.Prop6        → Basic
└── McCulloch25_1.Affine       → Thm5
```

## Mathlib dependencies

The project pins mathlib at `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` and uses Lean 4.24.0. Principal mathlib namespaces used: `Mathlib.Tactic`, `Mathlib.Multiplicative` (for the additive-group-as-`Multiplicative` trick in `Affine.lean`), `Mathlib.SetTheory`, and the `Equiv`, `MulAction`, `Finset`, and `Nat` libraries.

## Errata encountered during formalization

**E1 — Lemma 4 (main.tex line 174):** the printed hypothesis $d(u,v)\le2$ is false at $u=v=x_p$ when $|\Lambda|\ge2$; repaired to $d(u,v)=2$ exactly (see the paper's open problems, main.tex lines 383--389).

## Open problems (outside formalization scope)

The paper closes with two problems (main.tex lines 383--389): determine all gain functions on an affine plane yielding a GQ (and whether different gain functions give isomorphic GQs), and find other examples of gain functions on Steiner systems yielding GQs. Both are stated in the paper (main.tex lines 383--389).
