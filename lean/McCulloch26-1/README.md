# McCulloch26-1 — *Some answers regarding factorizations of finite groups*

**Paper.** Ryan McCulloch, *Some answers regarding factorizations of finite groups*
(Binghamton University). arXiv:2607.20569 (v3, 9 August 2026):
<https://arxiv.org/abs/2607.20569>. Cached source:
`docs/arxiv/2607.20569v3/Some_Answers_Factorization.tex`; citations of the form
"tex lines $a$–$b$" below refer to that file, whose line numbers were counted
directly.

**Formalization.** Lean library `McCulloch26_1`; sources in `McCulloch26_1/`,
root module `McCulloch26_1.lean`.

**Verification status.** `make` green (1834 jobs) on 2026-09-19; zero `sorry`
in the library; every declaration rests only on the axioms
`[propext, Classical.choice, Quot.sound]`. Every printed statement of the
paper is machine-checked — Lemma 2.1, Lemma 2.2, Theorem 2.3 (generalized, the
$k = 3$ instance over $A_4$, and the general $k \geq 3$ instance over the
Frobenius groups), Theorem 3.1, Corollary 3.2, and Corollary 3.3 with all its
clauses, including the excluded $(2,3,2)$ case.

## Overview

A $k$-fold factorization of a group $G$ is a product $G = A_1 \cdots A_k$ of
subsets whose multiplication map $A_1 \times \cdots \times A_k \to G$ is
bijective (tex lines 98–100); for finite $G$ this is equivalent to
$G = A_1 \cdots A_k$ together with $|G| = |A_1| \cdots |A_k|$ (tex line 102).
Hooshmand's Kourovka Notebook Question 19.35 asked whether such subsets exist
for every factorization $|G| = n_1 \cdots n_k$ (tex line 87). The paper
answers questions of G. M. Bergman around this problem. Negatively, Theorem
2.3 (`thm1`, tex lines 132–142) re-proves Kabenyuk's counterexamples in
Bergman's style: the Frobenius group of order $2^{k-1}(2^{k-1}-1)$ with kernel
the additive group of $\mathbb{F}_{2^{k-1}}$ and complement the multiplicative
group acting by field multiplication (tex line 128; the $k = 3$ case is
$A_4$, tex line 130) admits no $k$-fold factorization for
$(2, \dots, 2, 2^{k-1}-1, 2)$. Positively, Theorem 3.1 (`thm2`, tex lines
148–166) gives a sufficient condition: a subgroup chain
$\{e\} = G_0 < \cdots < G_n = G$ whose edge indices $\{1, \dots, n\}$ are
partitioned into blocks $s_1, \dots, s_k$ satisfying a one-sidedness
condition realizes every factorization $|G| = a_1 \cdots a_k$ compatible with
the block products $\prod_{i \in s_t} |G_i : G_{i-1}| = a_t$; this recovers
Bergman's unpublished 2-factorization theorem and yields that every solvable
finite group realizes all its 2-factorizations (Corollary 3.2, tex lines
213–219) and the full classification for $A_4$: every factorization of
$|A_4| = 12$ is realized except $(2,3,2)$, for which no 3-factorization
exists (Corollary 3.3, tex lines 223–229).

All printed statement environments of the paper are covered (Lemma 2.1,
Lemma 2.2, Theorem 2.3, Theorem 3.1, Corollary 3.2, Corollary 3.3). The only
statement deliberately outside scope is the remark that the $k = 2$ case of
Hooshmand's question remains open (tex line 104); see *Open problems* below.

## File-to-paper mapping

Modules are listed in the dependency order of the root module
`McCulloch26_1.lean` (definitions first). All module sources live in
`McCulloch26_1/`.

### `McCulloch26_1/Basic.lean` — the definition of $k$-fold factorization (tex lines 98–102)

Encodes the paper's Definition — bijectivity of the multiplication map
(tex lines 98–100) — as a unique-representation property, plus the
ordered-product API used by every later module.

- `setSeqProd` (tex lines 98–100): the ordered product set
  $\{a_0 \cdots a_{k-1} \mid a_i \in A_i\}$, i.e. the "$G = A_1 \cdots A_k$"
  half of the definition.
- `IsFactorization` (tex lines 98–100): the bijectivity half, as "every
  $x \in G$ has exactly one representation $x = a_0 \cdots a_{k-1}$ with
  $a_i \in A_i$".
- `prod_first_mid_last`, `setSeqProd_decomp` (used at tex line 139): split an
  ordered product over $\mathrm{Fin}(n+2)$ into first, middle, and last
  factors — the reading of $G = A_1 \cdot S \cdot A_k$ behind the printed
  proof of Theorem 2.3.

Encoding delta: bijectivity is stated as unique representation, equivalent
for finite groups (tex line 102); ordered products are
`List.prod (List.ofFn …)` because `Finset.prod` requires commutativity.
Feeds every other module.

### `McCulloch26_1/Lem_2_2_EndTranslate.lean` — Lemma 2.2, `lem: e` (tex lines 122–126)

Translating the two end sets preserves factorization, so a factorization may
be assumed to have identity-containing end sets (tex line 125). The paper
cites `[berg, sands]` for this lemma (tex line 120); the Lean proof
transcribes the two-line printed argument directly.

- `endTranslateL`, `endTranslateR`, `endTranslate` (tex line 123): the
  translated families $(gA_1) \cdot A_2 \cdots A_{k-1} \cdot (A_k h)$ — left
  end, right end, and both.
- `isFactorization_endTranslateL`, `isFactorization_endTranslateR`,
  `isFactorization_endTranslate` (tex lines 122–126): translation invariance
  of factorization. (The same lemma is Bergman20's `L.e_in`,
  `docs/arxiv/2003.12866/main.tex` lines 132–143.)
- `endTranslate_apply_zero`, `endTranslate_apply_last`,
  `card_endTranslate_zero`, `card_endTranslate_last` (tex lines 123–125):
  the translated ends are set-images under left/right multiplication, so
  their cardinalities are unchanged.

Feeds `Gaps.lean` (normalizing an end set) and `Thm_2_3_TwoEnds.lean` (the
wrapper discharging "we can assume $A_1$ and $A_k$ contain $e$" in the proof
of Theorem 2.3, tex line 137).

### `McCulloch26_1/Gaps.lean` — Lemma 2.1, `lem: first_last` (tex lines 112–118)

The paper leans on Lemma 2.1 without proof (tex line 110 defers to `[berg]`
= Bergman20-1); the proof is transcribed here from Bergman20
(`docs/arxiv/2003.12866/main.tex`), closing the gap. Scope: the two end
factors only — the paper itself omits Bergman's part (iii) for middle
factors (tex line 110), Bergman20 conjectures the middle-factor analogue
with "subgroup" in place of "normal subgroup" fails
(`docs/arxiv/2003.12866/main.tex` lines 305–315), and Theorem 2.3 only ever
applies the lemma at the ends (tex line 137).

- `diffSet` (tex line 115): the difference set
  $A^{-1}A = \{g^{-1}h \mid g, h \in A\}$.
- `diffSetR` (tex lines 115–116): the right difference set
  $AA^{-1} = \{gh^{-1} \mid g, h \in A\}$ (Bergman20 `L.div2` (ii) shape,
  `docs/arxiv/2003.12866/main.tex` lines 227–233).
- `nat_card_dvd_of_first_subset`, `nat_card_dvd_of_last_subset` (Bergman20
  `L.div`, statement `docs/arxiv/2003.12866/main.tex` lines 113–119, proof
  lines 121–128): in a factorization $A_0 \cdots A_n$, the cardinality of the
  first resp. last factor divides the order of any subgroup containing it.
  The printed coset count is realized as an explicit bijection between $P$
  and (chosen factor) × (tails whose product lands in $P$), injective by
  uniqueness of representations; the last-factor form mirrors it with left
  cosets ("The statement about $B$ is seen in the same way", line 127).
- `isFactorization_nonempty` (tex lines 98–102): factors of a factorization
  are nonempty.
- `card_dvd_card_closure_diffSet_first` (tex line 115): **Lemma 2.1(i)** —
  $|A_1|$ divides the order of $\langle A_1^{-1}A_1\rangle$. Route: translate
  some $g_0 \in A_1$ to the identity via Lemma 2.2, apply
  `nat_card_dvd_of_first_subset`, and identify
  $\langle g_0^{-1}A_1\rangle = \langle A_1^{-1}A_1\rangle$
  (`docs/arxiv/2003.12866/main.tex` lines 243–255).
- `card_dvd_card_closure_diffSet_last` (tex line 116): **Lemma 2.1(ii)** —
  $|A_k|$ divides the order of $\langle A_k A_k^{-1}\rangle$, by the
  mirrored argument ("(ii) holds by the same reasoning",
  `docs/arxiv/2003.12866/main.tex` line 266).
- Product-splitting infrastructure (`list_prod_split_first`,
  `list_prod_split_last`, `consFn`/`snocFn` and their product lemmas): the
  informal grouping steps of Bergman20's `L.div` and `L.div2` proofs,
  packaged for a noncommutative monoid.

Feeds `Thm_2_3_TwoEnds.lean` (used at both ends, tex line 137).

### `McCulloch26_1/Thm_2_3_TwoEnds.lean` — Theorem 2.3, `thm1`, generalized (tex lines 132–142)

The headline negative result, stated more generally than printed.

- `exists_complement_of_card_two` (tex line 137): a two-element set
  containing $e$ has the form $\{e, a\}$ with $a \neq e$.
- `mem_zpowers_of_cases`, `mem_zpowers_of_casesR` (tex line 137): all
  difference-set shapes of a two-point end land in the cyclic subgroup
  $\langle a \rangle$ — realizing "$|\langle A_1^{-1}A_1\rangle| = |\langle a\rangle|$".
- `no_factorization_with_small_ends_core` (tex lines 136–141): the printed
  proof under the normalization $e \in A_1, A_k$: Lemma 2.1 divisibility
  forces $a$ and $b$ to have even order, hence $a, b \in N$ (tex line 137);
  the middle product $S = A_2 \cdots A_{k-1}$ must meet every coset of $N$
  (tex line 139); transitivity supplies a conjugator, and writing it as
  $s\nu$ with $s \in S$, $\nu \in N$ gives $s^{-1}as = b$, i.e. $as = sb$;
  then $(a, s, 1)$ and $(1, s, b)$ are two distinct representations of the
  same element $as$ (tex line 141: "the multiplication map … is not
  one-to-one").
- `no_factorization_with_small_ends` (tex lines 132–142): the full theorem —
  no factorization into at least two sets whose two end sets have
  cardinality $2$ — after the Lemma 2.2 wrapper removes the
  identity-in-ends assumption.

Formalization deltas vs. the printed statement:

1. Only the two abstract properties set up at tex line 128 are hypothesized:
   a normal subgroup $N$ (normality used at tex line 139) that contains all
   even-order elements, with conjugation transitive on
   $N \smallsetminus \{e\}$. Mathlib has no Frobenius-group API, so the
   paper's concrete group is instantiated separately in
   `Thm_2_3_A4_Instance.lean` ($k = 3$) and `Thm_2_3_GeneralK.lean`
   (all $k \geq 3$).
2. Pointwise commutativity of $N$ is an explicit hypothesis (`hab`): the
   printed argument uses it implicitly when sliding the conjugator across
   the $N$-component of a coset representative (tex line 139); it holds in
   the paper's instance because the kernel is elementary abelian (tex line
   128). The clause that all elements of $N$ have order $2$ (tex lines 128,
   137) is dropped — the proof needs only $a, b \in N$, and the "in fact
   subgroups of $N$" remark of tex line 137 is not reproduced.
3. The middle-factor size $2^{k-1}-1$ is dropped: the printed proof never
   reads it, so the statement quantifies over arbitrary middle sets; the
   sizes appear only in the two instance modules.

Standalone in this generalized form; both instance modules below apply it.

### `McCulloch26_1/Thm_3_1_SufficientCondition.lean` — Theorem 3.1, `thm2` (tex lines 148–166, proof 168–201)

The sufficient condition: a subgroup chain with one-sidedly partitioned edge
indices realizes every compatible factorization, by induction on the chain.

- `reprProd`, `UFac` (tex lines 171–174, invariant (d.A1jA2j)): the
  maintained invariant — globally unique representations whose product set is
  exactly $G_j$; at the top of the chain it upgrades to `IsFactorization`
  because $G_n = G$.
- `cosetSec`, `leftReps`, `leftReps_sep`, `leftReps_cover`, `natCard_leftReps`,
  `leftReps_subset` (tex line 192): the transversal $C_{j+1}$ — "a full set
  of representatives of the left cosets" of $G_j$ in $G_{j+1}$ — with
  $|C_{j+1}| = [G_{j+1} : G_j]$.
- `normFamilyL`, `normShift`, `stripNorm`, `insertNorm`, `ufac_normL`,
  `prod_update_lt`, `prod_ofFn_one` (tex lines 187–190, (d.i_in_s1)): the
  "we may assume $S = \{e\}$" normalization of tex line 189 (via Lemma 2.2),
  realized at the level of representations.
- `extFamilyL`, `reprProd_extFamilyL_decomp`, `mulTransMap`,
  `natCard_mul_leftReps`, `extFamilyL_subset`, `ufac_extL` (tex lines
  192–196): the extension step $A_{t,j+1} = C_{j+1}A_{t,j}$ keeping all other
  factors (tex line 193), its size step
  $|A_{t,j+1}| = |C_{j+1}| \cdot |A_{t,j}|$ (tex line 195), and the transfer
  of unique factorization from $G_j$ to $G_{j+1}$
  ("$C_{j+1}G_j = G_{j+1}$", tex line 196).
- `finRev`, `prod_mirror_inv`, `mirrorFam`, `mirrorTupleOf`, `unMirrorTuple`,
  `ufac_mirrorFam`, `natCard_mirrorFam` (tex lines 181–185): order-reversal
  with inversion, reducing the "for all $a > t$" branch of the one-sidedness
  condition (tex lines 161–163) to the left-handed case.
- `exists_stage_ufac` (tex lines 168–200): the chain induction on $j$,
  maintaining block sizes $\prod_{i \in s_t \cap \{0,\dots,j-1\}} [G_i : G_{i+1}]$.
- `theorem_3_1` (tex lines 148–166): the theorem — blocks
  $s_1, \dots, s_k \subseteq \{0, \dots, n-1\}$ that partition the edges,
  satisfy the one-sidedness condition, and have products
  $\prod_{i \in s_t} [G_i : G_{i+1}] = a_t$ (tex lines 159–165) yield a
  factorization with $|A_t| = a_t$.

Encoding deltas: chain steps are stated non-strictly ($G_j \leq G_{j+1}$;
strictness is never used); edges are 0-based (edge $i$ connects $G_i$ and
$G_{i+1}$, paper edge $i{+}1$); the side conditions "$a_1 \cdots a_k = |G|$"
and positivity of the $a_t$ are dropped (both follow from the block-product
hypotheses in any application, and the proof does not read them); blocks are
`Finset ℕ`.

Feeds `Cor_3_2_Solvable.lean` and `Cor_3_3_A4.lean`.

### `McCulloch26_1/Cor_3_2_Solvable.lean` — Corollary 3.2, `solv` (tex lines 213–219)

Namespace `McCulloch26_1.Cor32`. Every solvable finite group realizes a
2-factorization $G = A_1 A_2$ with prescribed sizes for every factorization
$(a, b)$ of $|G|$, via Theorem 3.1.

- `exists_coatom_index_prime` (+ the commutator calculus of
  `normal_of_pointwiseComm`, `coe_commutator_mem`, `mulInv_mem_subgroupOf`,
  `quotient_pointwiseComm`, `normal_subgroupOf_of_commutator_le`)
  (tex line 218, "each factor group is cyclic of prime order"): a finite
  nontrivial pointwise-commutative group has a maximal proper subgroup of
  prime index. Primality: a proper prime divisor of the index would, by
  Cauchy's theorem in the quotient, give an intermediate subgroup
  strictly between the maximal subgroup and the top — a contradiction.
- `chain_splice`, `exists_seg`, `exists_chain_aux`,
  `exists_chain_of_solvable` (tex line 218): the composition series with
  prime successive indices. Built directly from the derived series (via
  `IsSolvable.commutator_lt_top_of_nontrivial`), refining each
  abelian-quotient segment $[H, K]$ through `exists_coatom_index_prime` and
  transporting the prime index through the third isomorphism theorem —
  mathlib has no composition-series API used here.
- `le_of_mono_chain`, `prod_relIndex_chain` (tex line 218): the edge
  indices of a monotone chain multiply to the total relative index.
- `exists_finset_prod_eq` (tex line 218, "$a$ is a product of prime indices
  in its composition series, and so is $b$"): a divisor of a product of
  primes is a subproduct over some subset of the indices.
- `exists_two_of_chain`: the chain-level assembly shared by Corollaries 3.2
  and 3.3 — any finite group with a prime-index chain realizes a
  2-factorization for every $(a,b)$ with $ab = |G|$, feeding Theorem 3.1 the
  two complementary blocks $s_1$ and
  $\{0, \dots, n-1\} \smallsetminus s_1$; the one-sidedness condition is
  vacuous at $k = 2$ (tex lines 203–209).
- `corollary_3_2` (tex lines 213–215): the corollary itself, a three-line
  application of `exists_two_of_chain` to the chain of
  `exists_chain_of_solvable`.

Encoding delta vs. the printed proof (tex lines 217–219): the paper invokes
a composition series with cyclic prime-order factors; the Lean proof
constructs one explicitly (derived-series descent + coatom refinement)
rather than citing a composition-series API. Feeds `Cor_3_3_A4.lean` (via
`exists_two_of_chain`).

### `McCulloch26_1/Cor_3_3_A4.lean` — Corollary 3.3 (tex lines 223–229), realizability clauses

Namespace `McCulloch26_1.Cor33`. Realizes every factorization of
$|A_4| = 12$ via Theorem 3.1 except $(2,3,2)$; the excluded case is completed
by `Thm_2_3_A4_Instance.lean` below.

- `dt1`, `dt2`, `dt3`, `v4Carrier`, `V4`, `Z2` (+ membership and cardinality
  lemmas `mem_V4`, `mem_Z2`, `natCard_V4`, `natCard_Z2`, `Z2_le_V4`,
  `V4_le_alternating`, `card_alternating4`, `perm_ext4`): the three double
  transpositions $(0\,1)(2\,3)$, $(0\,2)(1\,3)$, $(0\,3)(1\,2)$, the Klein
  four group $V_4 \cong \mathbb{Z}_2 \times \mathbb{Z}_2$, and its order-2
  subgroup $\mathbb{Z}_2$, all inside `Equiv.Perm (Fin 4)` — the members of
  the paper's composition series (tex line 228).
- `chainA4` (+ `chainA4_zero/one/two/three`, `chainA4_mono`, `edgeA4_0`,
  `edgeA4_1`, `edgeA4_2`, `chainA4_prime`): the chain
  $\{e\} = G_0 < \mathbb{Z}_2 < \mathbb{Z}_2 \times \mathbb{Z}_2 < A_4$ of
  tex line 228, transported into subgroups of `alternatingGroup (Fin 4)` via
  `.subgroupOf`, with edge indices $2, 2, 3$.
- `exists_two_factorization_a4` (tex lines 223–225): every 2-factorization
  $(a,b)$ with $ab = 12$ is realized through `exists_two_of_chain` —
  subsuming the paper's route through Corollary `solv` (tex line 228).
- `blocks223`, `sizes223`, `exists_factorization_a4_two_two_three`
  (tex line 228): the $(2,2,3)$ case with singleton blocks
  $s_1 = \{0\}$, $s_2 = \{1\}$, $s_3 = \{2\}$ (0-based; the paper's
  $s_1 = \{1\}$, $s_2 = \{2\}$, $s_3 = \{3\}$).
- `blocks322`, `sizes322`, `exists_factorization_a4_three_two_two`
  (tex line 228): the $(3,2,2)$ case with singleton blocks $s_1 = \{2\}$,
  $s_2 = \{1\}$, $s_3 = \{0\}$.

Feeds `Thm_2_3_A4_Instance.lean` (the $V_4$/$A_4$ permutation API).

### `McCulloch26_1/Thm_2_3_A4_Instance.lean` — Theorem 2.3 at $k = 3$: $A_4$ has no $(2,3,2)$ factorization (tex lines 132–142, 223–229)

Namespace `McCulloch26_1.Cor33` (continued). Completes the excluded case of
Corollary 3.3 — "except for $(2,3,2)$, for which no $3$-factorization
exists" (tex line 224), derived from `thm1` at tex line 228 — i.e. Bergman's
original counterexample (tex line 106). Instantiates
`no_factorization_with_small_ends` with $G = A_4$ (as
`alternatingGroup (Fin 4)`) and $N = V_4$.

- `cyc` (+ `cyc_mul_dt1/2/3`, `conj_cyc_dt1/2/3`, `conj_cyc_inv_dt1/2/3`):
  the 3-cycle $(0\,1\,2)$ conjugates the three double transpositions
  cyclically — the transitivity witnesses of tex line 139 (the $k = 3$
  instance is identified as $A_4$ at tex line 130).
- `involution_mem_V4` (tex line 137): every involution of $A_4$ is one of
  the three double transpositions — an involution moving a point pairs up
  all four points (double transposition) rather than fixing two
  (transposition, of odd sign).
- `mem_V4_of_commute` (+ `mem_V4_of_commute_aux`) (tex line 137): an element
  of $A_4$ commuting with a nontrivial element of $V_4$ lies in $V_4$ —
  preserving or swapping the paired transposition structure keeps $z$ in the
  $V_4$ cases, while crossing the pairs makes $z$ a 4-cycle of odd sign.
  This kills even orders $2, 4, 6, 12$ uniformly.
- `heven_a4` (tex line 137): even-order elements of $A_4$ lie in $V_4$ — a
  suitable power is an involution, and powers commute with the element.
- `hab_N` (tex line 128), `normal_N` (tex line 139): $V_4$ is abelian and
  normal in $A_4$ (conjugates of nontrivial $V_4$ elements are again even
  involutions, hence double transpositions).
- `hconj_N` (tex line 139): powers of $(0\,1\,2)$ conjugate any nontrivial
  $V_4$ element to any other.
- `sizes232`, `no_factorization_a4_two_three_two` (tex lines 223–225):
  $A_4$ admits no factorization with sizes $(2,3,2)$.

Standalone: completes Corollary 3.3; nothing downstream consumes it.

### `McCulloch26_1/Thm_2_3_GeneralK.lean` — Theorem 2.3 for all $k \geq 3$: the Frobenius groups (tex lines 128–142)

Namespace `McCulloch26_1.Cor23GK`. The printed theorem itself: with
$m = k - 1 \geq 2$, the Frobenius group of order $2^m(2^m - 1)$ — kernel the
additive group of $\mathbb{F}_{2^m}$, complement its multiplicative group
acting by field multiplication (tex line 128) — admits no $k$-fold
factorization for $(2, \dots, 2, 2^m - 1, 2)$ (tex line 133). The group is
built as `Multiplicative (GaloisField 2 m) ⋊[unitsMulAut] (GaloisField 2 m)ˣ`:
mathlib's `GaloisField 2 m` is the field with $2^m$ elements
(`GaloisField.card`), so no irreducible-polynomial or primitive-element
construction is needed.

- `unitMulAut`, `unitsMulAut` (tex line 128): the unit group acts on the
  additive group by field multiplication, as a monoid homomorphism
  $K^\times \to \mathrm{MulAut}(\mathrm{Multiplicative}\ K)$.
- `F2m`, `Frobenius`, `frobKernel`, `mem_frobKernel` (tex line 128): the
  semidirect product and its embedded elementary abelian kernel.
- `frob_pow_right`, `frob_pow_left` (tex line 128): powers in the semidirect
  product — the complement component is $u^r$, the kernel component the
  geometric sum $(\sum_{i<r} u^i) a$.
- `odd_order_of_outside` (tex line 128): an element outside the kernel has
  odd order. Fermat gives $u^{2^m - 1} = 1$ for the unit component
  (`FiniteField.pow_card_sub_one_eq_one` with `GaloisField.card`), and the
  geometric-sum identity
  $\sum_{i<2^m-1} u^i = (u^{2^m-1} - 1)/(u - 1)$ collapses to $0$ in
  characteristic $2$ (the denominator is a unit), so the whole element
  satisfies $x^{2^m-1} = 1$ with $2^m - 1$ odd.
- `heven_frobenius` (tex line 128): even-order elements lie in the kernel —
  the `heven` hypothesis of the generalized theorem.
- `frobKernel_normal` (tex line 139), `frobKernel_comm` (tex line 128):
  normality and pointwise commutativity of the kernel — the `hN` and `hab`
  hypotheses.
- `conj_inl_inr`, `frobKernel_conj` (tex line 128): conjugation is
  transitive on the nonidentity kernel elements; the conjugating unit is
  $ab^{-1}$, directly from field multiplication.
- `sizesFrob` (tex line 133): the size tuple $(2, \dots, 2, 2^m - 1, 2)$
  over the $k = m + 1$ factors: $m - 1$ entries $2$, then $2^m - 1$, then
  $2$.
- `no_factorization_frobenius` (tex lines 132–142): the theorem,
  parametrized by $k = m' + 3 \geq 3$ (so $m = m' + 2$) so that the
  `Fin (k)` index type of the generalized theorem unifies definitionally.

Formalization delta: the complement is the full unit group
$(\mathbb{F}_{2^m})^\times$ rather than the cyclic group generated by a
primitive element (tex line 128) — the proof never uses cyclicity of the
multiplicative group. At $k = 3$ ($m = 2$) this group is isomorphic to
$A_4$ (tex line 130); the concrete instance over `alternatingGroup (Fin 4)`
is `Thm_2_3_A4_Instance.lean`. Standalone: nothing downstream consumes it.

## Module dependency graph

```
McCulloch26_1.lean (root module: imports all nine modules below)
│
├── Basic.lean ───────────────────────── factorization definition, ordered-product API
│     ├── Lem_2_2_EndTranslate.lean ──── Lemma 2.2: end translations preserve factorization
│     │     └── Gaps.lean ────────────── Lemma 2.1: end-factor divisibility (transcribed from Bergman20)
│     │           └── Thm_2_3_TwoEnds.lean ─ generalized Theorem 2.3 (abstract two-property form)
│     │                 ├── Thm_2_3_A4_Instance.lean ─ Theorem 2.3 at k = 3: A_4 has no (2,3,2)
│     │                 └── Thm_2_3_GeneralK.lean ──── Theorem 2.3 for all k ≥ 3: Frobenius groups
│     └── Thm_3_1_SufficientCondition.lean ── Theorem 3.1: one-sided chain condition ⇒ factorization
│           └── Cor_3_2_Solvable.lean ── Corollary 3.2: solvable ⇒ all 2-factorizations
│                 └── Cor_3_3_A4.lean ── Corollary 3.3: all A_4 realizations except (2,3,2)
│                       └── Thm_2_3_A4_Instance.lean (also imports Thm_2_3_TwoEnds.lean)
```

Two independent proof trees grow out of `Basic.lean`: the negative track
(Lemma 2.1 → Lemma 2.2 → generalized Theorem 2.3 → its two instances) and
the positive track (Theorem 3.1 → Corollary 3.2 → Corollary 3.3). They meet
only in `Thm_2_3_A4_Instance.lean`, which instantiates the generalized
Theorem 2.3 inside the $A_4$ permutation API of `Cor_3_3_A4.lean` to
complete the final corollary's excluded case.

## Mathlib / toolchain

- Lean: `leanprover/lean4:v4.24.0` (`lean-toolchain`).
- mathlib: revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (`lakefile.toml`).
- Build: `make` at the project root (stamp-gated mathlib cache).

Principal mathlib namespaces used:

- `GaloisField` — the field with $2^m$ elements (`GaloisField 2 m`,
  `GaloisField.card`), carrying both the kernel and the complement of the
  Frobenius groups (`Thm_2_3_GeneralK.lean`);
- `SemidirectProduct`, `Multiplicative`, `MulAut` — the semidirect-product
  realization $\mathbb{F}_{2^m}^{+} \rtimes (\mathbb{F}_{2^m})^\times$ with
  the units acting by multiplication;
- `Subgroup` — `relIndex` (chain edge indices), `subgroupOf` (transporting
  chains into $A_4$), `zpowers` (the cyclic subgroup $\langle a \rangle$ of
  the divisibility step), `closure`, and the commutator calculus
  (`Subgroup.commutator`) behind the solvable-group chain;
- `QuotientGroup` — left-coset sections for Theorem 3.1's transversals and
  the third-isomorphism transport of the prime index in Corollary 3.2;
- `Equiv.Perm`, `alternatingGroup`, `Equiv.Perm.sign` — the concrete $A_4$,
  $V_4$, double transpositions, and sign arguments of
  `Cor_3_3_A4.lean` / `Thm_2_3_A4_Instance.lean`;
- `IsSolvable` — the derived-series descent
  (`IsSolvable.commutator_lt_top_of_nontrivial`) building the prime-index
  chain of a solvable group;
- `FiniteField.pow_card_sub_one_eq_one`, `geom_sum_eq` — Fermat's little
  theorem for the unit group and the characteristic-2 geometric-sum
  collapse giving odd order outside the kernel;
- `Nat.card` / `Fintype.card` — cardinality bookkeeping throughout.

## Errata encountered

None. No printed statement or proof step of the paper disagreed with the
formalization. All divergences are deliberate encoding decisions, recorded
with the corresponding modules in the mapping above:

- bijectivity of the multiplication map is encoded as unique representation
  (`Basic.lean`, tex lines 98–102);
- Theorem 2.3 is stated in a generalized abstract form (normal subgroup
  with transitive conjugation and even-order capture, plus pointwise
  commutativity; middle sizes dropped) that the paper's Frobenius groups
  instantiate (`Thm_2_3_TwoEnds.lean`, tex lines 128–142);
- Theorem 3.1 is stated with non-strict chain steps, 0-based edges, and
  without the derivable side conditions on the sizes
  (`Thm_3_1_SufficientCondition.lean`, tex lines 148–166).

## Open problems

- **The $k = 2$ case of Hooshmand's question** (Kourovka Notebook Question
  20.37, tex line 104): whether every finite group $G$ admits a 2-fold
  factorization for every factorization $(a, b)$ of $|G|$. The paper states
  it is "still open" and reduced to simple groups; it is not addressed by
  this formalization. Tracked, with the paper's other (answered) questions,
  in `docs/papers/open/McCulloch26-1/open_questions.md` — item 1 there is
  the only genuinely open one.

