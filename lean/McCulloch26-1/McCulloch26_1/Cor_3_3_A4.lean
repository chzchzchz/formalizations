import McCulloch26_1.Cor_3_2_Solvable

import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.FinCases

/-!
# Corollary 3.3 of McCulloch26-1: the alternating group $A_4$

A $k$-factorization of $A_4$ is realizable via Theorem 3.1 (`thm2`) for every
factorization of $|A_4| = 12$ except $(2,3,2)$ (tex lines 223-229).

This module builds the concrete chain $\{e\} < \mathbb{Z}_2 < V_4 < A_4$
(tex lines 227-228) inside `Equiv.Perm (Fin 4)`, transports it into the
subgroup $A_4$, and realizes:
- every 2-factorization $(a,b)$ with $a \cdot b = 12$ (via
  `exists_two_of_chain`, subsuming the paper's route through Corollary
  `solv`);
- the two 3-block cases $(2,2,3)$ and $(3,2,2)$ with explicit partitions
  (tex lines 227-229).

The impossibility of $(2,3,2)$ is not yet formalized here; it reduces to the
generalized Theorem 2.3 applied to $A_4$ (see sumplan.md).

Source:
/home/chz/src/gamskil/docs/arxiv/2607.20569v3/Some_Answers_Factorization.tex
lines 223-229 (statement and printed proof).
-/

open Equiv Equiv.Perm Subgroup Finset

namespace McCulloch26_1.Cor33

noncomputable local instance : DecidableEq (Perm (Fin 4)) := Classical.decEq _

/-! ### The three double transpositions of `Perm (Fin 4)` -/

/-- $(0\,1)(2\,3)$. -/
def dt1 : Perm (Fin 4) := swap 0 1 * swap 2 3

/-- $(0\,2)(1\,3)$. -/
def dt2 : Perm (Fin 4) := swap 0 2 * swap 1 3

/-- $(0\,3)(1\,2)$. -/
def dt3 : Perm (Fin 4) := swap 0 3 * swap 1 2

/-- Pointwise determination of permutations of `Fin 4`. -/
theorem perm_ext4 {σ τ : Perm (Fin 4)} (h0 : σ 0 = τ 0) (h1 : σ 1 = τ 1)
    (h2 : σ 2 = τ 2) (h3 : σ 3 = τ 3) : σ = τ :=
  Perm.ext fun i => by
    have hval := i.isLt
    rcases Nat.lt_or_ge i.val 1 with h | h
    · have hi : i = 0 := Fin.ext (by omega)
      rw [hi]; exact h0
    · rcases Nat.lt_or_ge i.val 2 with h2' | h2'
      · have hi : i = 1 := Fin.ext (by omega)
        rw [hi]; exact h1
      · rcases Nat.lt_or_ge i.val 3 with h3' | h3'
        · have hi : i = 2 := Fin.ext (by omega)
          rw [hi]; exact h2
        · have hi : i = 3 := Fin.ext (by omega)
          rw [hi]; exact h3

theorem dt1_ne_one : dt1 ≠ 1 := by
  intro heq
  have h0 : dt1 0 = 1 := rfl
  rw [heq] at h0
  have h1 : (0 : Fin 4) = 1 := h0
  exact absurd (congrArg Fin.val h1) (by decide)

theorem dt2_ne_one : dt2 ≠ 1 := by
  intro heq
  have h0 : dt2 0 = 2 := rfl
  rw [heq] at h0
  have h1 : (0 : Fin 4) = 2 := h0
  exact absurd (congrArg Fin.val h1) (by decide)

theorem dt3_ne_one : dt3 ≠ 1 := by
  intro heq
  have h0 : dt3 0 = 3 := rfl
  rw [heq] at h0
  have h1 : (0 : Fin 4) = 3 := h0
  exact absurd (congrArg Fin.val h1) (by decide)

theorem dt1_ne_dt2 : dt1 ≠ dt2 := by
  intro heq
  have h : dt1 0 = dt2 0 := by rw [heq]
  have h1 : (1 : Fin 4) = 2 := h
  exact absurd (congrArg Fin.val h1) (by decide)

theorem dt1_ne_dt3 : dt1 ≠ dt3 := by
  intro heq
  have h : dt1 0 = dt3 0 := by rw [heq]
  have h1 : (1 : Fin 4) = 3 := h
  exact absurd (congrArg Fin.val h1) (by decide)

theorem dt2_ne_dt3 : dt2 ≠ dt3 := by
  intro heq
  have h : dt2 0 = dt3 0 := by rw [heq]
  have h1 : (2 : Fin 4) = 3 := h
  exact absurd (congrArg Fin.val h1) (by decide)

theorem dt1_sq : dt1 * dt1 = 1 := perm_ext4 rfl rfl rfl rfl
theorem dt2_sq : dt2 * dt2 = 1 := perm_ext4 rfl rfl rfl rfl
theorem dt3_sq : dt3 * dt3 = 1 := perm_ext4 rfl rfl rfl rfl

theorem dt1_mul_dt2 : dt1 * dt2 = dt3 := perm_ext4 rfl rfl rfl rfl
theorem dt2_mul_dt1 : dt2 * dt1 = dt3 := perm_ext4 rfl rfl rfl rfl
theorem dt2_mul_dt3 : dt2 * dt3 = dt1 := perm_ext4 rfl rfl rfl rfl
theorem dt3_mul_dt2 : dt3 * dt2 = dt1 := perm_ext4 rfl rfl rfl rfl
theorem dt3_mul_dt1 : dt3 * dt1 = dt2 := perm_ext4 rfl rfl rfl rfl
theorem dt1_mul_dt3 : dt1 * dt3 = dt2 := perm_ext4 rfl rfl rfl rfl

theorem dt1_inv : dt1⁻¹ = dt1 := by
  calc dt1⁻¹ = dt1⁻¹ * (dt1 * dt1) := by rw [dt1_sq, mul_one]
    _ = dt1 := inv_mul_cancel_left _ _

theorem dt2_inv : dt2⁻¹ = dt2 := by
  calc dt2⁻¹ = dt2⁻¹ * (dt2 * dt2) := by rw [dt2_sq, mul_one]
    _ = dt2 := inv_mul_cancel_left _ _

theorem dt3_inv : dt3⁻¹ = dt3 := by
  calc dt3⁻¹ = dt3⁻¹ * (dt3 * dt3) := by rw [dt3_sq, mul_one]
    _ = dt3 := inv_mul_cancel_left _ _

/-! ### The Klein four group $V_4$ -/

/-- The carrier $\{e,\ (0\,1)(2\,3),\ (0\,2)(1\,3),\ (0\,3)(1\,2)\}$ of $V_4$. -/
def v4Carrier : Set (Perm (Fin 4)) :=
  insert 1 (insert dt1 (insert dt2 {dt3}))

theorem one_mem_v4Carrier : (1 : Perm (Fin 4)) ∈ v4Carrier := Set.mem_insert _ _

theorem dt1_mem_v4Carrier : dt1 ∈ v4Carrier :=
  Set.mem_insert_of_mem 1 (Set.mem_insert dt1 (insert dt2 {dt3}))

theorem dt2_mem_v4Carrier : dt2 ∈ v4Carrier :=
  Set.mem_insert_of_mem 1 (Set.mem_insert_of_mem dt1 (Set.mem_insert dt2 {dt3}))

theorem dt3_mem_v4Carrier : dt3 ∈ v4Carrier :=
  Set.mem_insert_of_mem 1 (Set.mem_insert_of_mem dt1 (Set.mem_insert_of_mem dt2
    (Set.mem_singleton dt3)))

theorem mem_v4Carrier_cases {x : Perm (Fin 4)} (hx : x ∈ v4Carrier) :
    x = 1 ∨ x = dt1 ∨ x = dt2 ∨ x = dt3 := by
  simp only [v4Carrier, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  exact hx

theorem mul_mem_v4Carrier {x y : Perm (Fin 4)}
    (hx : x ∈ v4Carrier) (hy : y ∈ v4Carrier) : x * y ∈ v4Carrier := by
  rcases mem_v4Carrier_cases hx with rfl | rfl | rfl | rfl <;>
    rcases mem_v4Carrier_cases hy with rfl | rfl | rfl | rfl
  · exact one_mem_v4Carrier
  · exact dt1_mem_v4Carrier
  · exact dt2_mem_v4Carrier
  · exact dt3_mem_v4Carrier
  · rw [mul_one]; exact dt1_mem_v4Carrier
  · rw [dt1_sq]; exact one_mem_v4Carrier
  · rw [dt1_mul_dt2]; exact dt3_mem_v4Carrier
  · rw [dt1_mul_dt3]; exact dt2_mem_v4Carrier
  · rw [mul_one]; exact dt2_mem_v4Carrier
  · rw [dt2_mul_dt1]; exact dt3_mem_v4Carrier
  · rw [dt2_sq]; exact one_mem_v4Carrier
  · rw [dt2_mul_dt3]; exact dt1_mem_v4Carrier
  · rw [mul_one]; exact dt3_mem_v4Carrier
  · rw [dt3_mul_dt1]; exact dt2_mem_v4Carrier
  · rw [dt3_mul_dt2]; exact dt1_mem_v4Carrier
  · rw [dt3_sq]; exact one_mem_v4Carrier

theorem inv_mem_v4Carrier {x : Perm (Fin 4)} (hx : x ∈ v4Carrier) :
    x⁻¹ ∈ v4Carrier := by
  rcases mem_v4Carrier_cases hx with rfl | rfl | rfl | rfl
  · rw [inv_one]; exact one_mem_v4Carrier
  · rw [dt1_inv]; exact dt1_mem_v4Carrier
  · rw [dt2_inv]; exact dt2_mem_v4Carrier
  · rw [dt3_inv]; exact dt3_mem_v4Carrier

/-- $V_4$: the Klein four group of the three double transpositions and $e$. -/
def V4 : Subgroup (Perm (Fin 4)) where
  carrier := v4Carrier
  mul_mem' := mul_mem_v4Carrier
  one_mem' := one_mem_v4Carrier
  inv_mem' := inv_mem_v4Carrier

theorem mem_V4 {x : Perm (Fin 4)} :
    x ∈ V4 ↔ x = 1 ∨ x = dt1 ∨ x = dt2 ∨ x = dt3 :=
  ⟨mem_v4Carrier_cases, fun h => h⟩

/-- The four elements of $V_4$, as members of the subgroup. -/
noncomputable def v4List : Fin 4 → ↥V4 :=
  ![⟨(1 : Perm (Fin 4)), mem_V4.2 (Or.inl rfl)⟩,
    ⟨dt1, mem_V4.2 (Or.inr (Or.inl rfl))⟩,
    ⟨dt2, mem_V4.2 (Or.inr (Or.inr (Or.inl rfl)))⟩,
    ⟨dt3, mem_V4.2 (Or.inr (Or.inr (Or.inr rfl)))⟩]

theorem eval_v4List_0 (i : Fin 4) :
    Subtype.val (v4List i) 0 = i := by
  fin_cases i <;> simp [v4List] <;> rfl

theorem natCard_V4 : Nat.card ↥V4 = 4 := by
  have h4 : Nat.card (Fin 4) = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  refine le_antisymm ?_ ?_
  · -- upper bound: `v4List` enumerates all of `V4`
    have hsurrL : Function.Surjective v4List := by
      rintro ⟨x, hx⟩
      rcases mem_V4.mp hx with rfl | rfl | rfl | rfl
      · exact ⟨0, Subtype.ext rfl⟩
      · exact ⟨1, Subtype.ext rfl⟩
      · exact ⟨2, Subtype.ext rfl⟩
      · exact ⟨3, Subtype.ext rfl⟩
    have hle := Nat.card_le_card_of_surjective _ hsurrL
    exact le_trans hle (by rw [h4])
  · -- lower bound: point 0 takes four distinct values on the listed elements
    have hinj : Function.Injective v4List := by
      intro i j hij
      have h0 : Subtype.val (v4List i) 0 = Subtype.val (v4List j) 0 :=
        congrArg (fun σ : Perm (Fin 4) => σ 0) (congrArg Subtype.val hij)
      rw [eval_v4List_0, eval_v4List_0] at h0
      exact h0
    have hinj' : Nat.card (Fin 4) ≤ Nat.card ↥V4 :=
      Nat.card_le_card_of_injective v4List hinj
    rw [h4] at hinj'
    exact hinj'

/-! ### $\mathbb{Z}_2$ inside $V_4$ -/

/-- $\mathbb{Z}_2$: the order-$2$ subgroup generated by $(0\,1)(2\,3)$. -/
def Z2 : Subgroup (Perm (Fin 4)) where
  carrier := insert 1 {dt1}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · rw [dt1_sq]; exact Or.inl rfl
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · rw [inv_one]; exact Or.inl rfl
    · rw [dt1_inv]; exact Or.inr rfl

theorem mem_Z2 {x : Perm (Fin 4)} : x ∈ Z2 ↔ x = 1 ∨ x = dt1 := by
  constructor
  · intro hx
    have hx' : x ∈ (↑Z2 : Set (Perm (Fin 4))) := hx
    simpa using hx'
  · rintro (rfl | rfl)
    · exact SetLike.mem_coe.2 (Set.mem_insert _ _)
    · exact SetLike.mem_coe.2 (Set.mem_insert_iff.2
        (Or.inr (Set.mem_singleton dt1)))

theorem natCard_Z2 : Nat.card ↥Z2 = 2 := by
  have h2 : Nat.card (Fin 2) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  have hsurrL : Function.Surjective
      (fun i : Fin 2 =>
        (![⟨(1 : Perm (Fin 4)), mem_Z2.2 (Or.inl rfl)⟩,
          ⟨dt1, mem_Z2.2 (Or.inr rfl)⟩] : Fin 2 → ↥Z2) i) := by
    rintro ⟨x, hx⟩
    rcases mem_Z2.mp hx with rfl | rfl
    · exact ⟨0, Subtype.ext rfl⟩
    · exact ⟨1, Subtype.ext rfl⟩
  haveI : Finite ↥Z2 := Finite.of_surjective _ hsurrL
  have hnT : Nontrivial ↥Z2 := by
    refine ⟨⟨1, mem_Z2.2 (Or.inl rfl)⟩, ⟨dt1, mem_Z2.2 (Or.inr rfl)⟩, ?_⟩
    intro hc
    exact dt1_ne_one (congrArg Subtype.val hc).symm
  refine le_antisymm ?_ ?_
  · have hle := Nat.card_le_card_of_surjective _ hsurrL
    exact le_trans hle (by rw [h2])
  · exact Finite.one_lt_card (α := ↥Z2)

/-! ### The subgroups sit inside the alternating group -/

theorem Z2_le_V4 : Z2 ≤ V4 := by
  intro x hx
  rcases mem_Z2.mp hx with rfl | rfl
  · exact mem_V4.2 (Or.inl rfl)
  · exact mem_V4.2 (Or.inr (Or.inl rfl))

theorem V4_le_alternating : V4 ≤ alternatingGroup (Fin 4) := by
  intro x hx
  rw [mem_alternatingGroup]
  rcases mem_V4.mp hx with rfl | rfl | rfl | rfl
  · exact Eq.refl 1
  · show sign (swap 0 1 * swap 2 3) = 1
    rw [sign_mul, sign_swap (show (0 : Fin 4) ≠ 1 by decide),
      sign_swap (show (2 : Fin 4) ≠ 3 by decide)]; norm_num
  · show sign (swap 0 2 * swap 1 3) = 1
    rw [sign_mul, sign_swap (show (0 : Fin 4) ≠ 2 by decide),
      sign_swap (show (1 : Fin 4) ≠ 3 by decide)]; norm_num
  · show sign (swap 0 3 * swap 1 2) = 1
    rw [sign_mul, sign_swap (show (0 : Fin 4) ≠ 3 by decide),
      sign_swap (show (1 : Fin 4) ≠ 2 by decide)]; norm_num

/-! ### Ambient index arithmetic -/

theorem card_alternating4 :
    Nat.card ↥(alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem relIndex_bot_Z2 :
    (⊥ : Subgroup (Perm (Fin 4))).relIndex Z2 = 2 := by
  rw [Subgroup.relIndex_bot_left, natCard_Z2]

theorem card_mul_relIndex {H K : Subgroup (Perm (Fin 4))} (hHK : H ≤ K) :
    Nat.card ↥K = Nat.card ↥H * H.relIndex K := by
  calc Nat.card ↥K = (⊥ : Subgroup (Perm (Fin 4))).relIndex K :=
        (Subgroup.relIndex_bot_left K).symm
    _ = (⊥ : Subgroup (Perm (Fin 4))).relIndex H * H.relIndex K :=
        (Subgroup.relIndex_mul_relIndex _ _ _ bot_le hHK).symm
    _ = Nat.card ↥H * H.relIndex K := by rw [Subgroup.relIndex_bot_left]

theorem relIndex_Z2_V4 : Z2.relIndex V4 = 2 := by
  have hc := card_mul_relIndex (H := Z2) (K := V4) Z2_le_V4
  rw [natCard_V4, natCard_Z2] at hc
  omega

theorem relIndex_V4_A4 : V4.relIndex (alternatingGroup (Fin 4)) = 3 := by
  have hV4A4 : V4 ≤ alternatingGroup (Fin 4) := V4_le_alternating
  have h := card_mul_relIndex (H := V4) (K := alternatingGroup (Fin 4)) hV4A4
  rw [card_alternating4, natCard_V4] at h
  omega

/-! ### The chain $\{e\} < \mathbb{Z}_2 < V_4 < A_4$ -/

/-- The chain $\{e\} < \mathbb{Z}_2 < V_4 < A_4$ (tex lines 227-228),
transported into subgroups of $A_4$. -/
def chainA4 : ℕ → Subgroup ↥(alternatingGroup (Fin 4)) :=
  fun i => if i = 0 then ⊥
           else if i = 1 then Z2.subgroupOf (alternatingGroup (Fin 4))
           else if i = 2 then V4.subgroupOf (alternatingGroup (Fin 4))
           else ⊤

theorem chainA4_zero : chainA4 0 = ⊥ := by
  unfold chainA4
  rfl

theorem chainA4_one :
    chainA4 1 = Z2.subgroupOf (alternatingGroup (Fin 4)) := by
  unfold chainA4
  rw [if_neg (by omega), if_pos rfl]

theorem chainA4_two :
    chainA4 2 = V4.subgroupOf (alternatingGroup (Fin 4)) := by
  unfold chainA4
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem chainA4_three : chainA4 3 = ⊤ := by
  unfold chainA4
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem chainA4_top_of_le {j : ℕ} (hj : 3 ≤ j) : chainA4 j = ⊤ := by
  by_cases h0 : j = 0
  · exact absurd h0 (by omega)
  · by_cases h1 : j = 1
    · exact absurd h1 (by omega)
    · by_cases h2 : j = 2
      · exact absurd h2 (by omega)
      · unfold chainA4
        rw [if_neg h0, if_neg h1, if_neg h2]

theorem chainA4_mono : ∀ j, chainA4 j ≤ chainA4 (j + 1) := by
  intro j
  by_cases hj0 : j = 0
  · subst hj0
    rw [chainA4_zero]
    exact bot_le
  · by_cases hj1 : j = 1
    · have hje : j = 1 := hj1
      subst hje
      rw [chainA4_one, chainA4_two]
      intro z hz
      exact Subgroup.mem_subgroupOf.mpr (Z2_le_V4 (Subgroup.mem_subgroupOf.mp hz))
    · by_cases hj2 : j = 2
      · have hje : j = 2 := hj2
        subst hje
        rw [chainA4_two, chainA4_three]
        exact le_top
      · have hj3 : 3 ≤ j := by omega
        rw [chainA4_top_of_le hj3, chainA4_top_of_le (by omega)]

theorem edgeA4_0 : (chainA4 0).relIndex (chainA4 1) = 2 := by
  rw [chainA4_zero, chainA4_one, ← Subgroup.bot_subgroupOf,
    Subgroup.relIndex_subgroupOf (hKL := Z2_le_V4.trans V4_le_alternating),
    relIndex_bot_Z2]

theorem edgeA4_1 : (chainA4 1).relIndex (chainA4 2) = 2 := by
  rw [chainA4_one, chainA4_two,
    Subgroup.relIndex_subgroupOf (hKL := V4_le_alternating)]
  exact relIndex_Z2_V4

theorem edgeA4_2 : (chainA4 2).relIndex (chainA4 3) = 3 := by
  rw [chainA4_two, chainA4_three, ← Subgroup.subgroupOf_self,
    Subgroup.relIndex_subgroupOf (H := V4) (K := alternatingGroup (Fin 4))
      (L := alternatingGroup (Fin 4)) le_rfl]
  exact relIndex_V4_A4

theorem chainA4_prime : ∀ j < 3, ((chainA4 j).relIndex (chainA4 (j + 1))).Prime := by
  intro j hj
  rcases Nat.lt_or_ge j 1 with h | h
  · have hje : j = 0 := by omega
    subst hje
    rw [edgeA4_0]
    exact Nat.prime_two
  · rcases Nat.lt_or_ge j 2 with h2 | h2
    · have hje : j = 1 := by omega
      subst hje
      rw [edgeA4_1]
      exact Nat.prime_two
    · have hje : j = 2 := by omega
      subst hje
      rw [edgeA4_2]
      exact Nat.prime_three

theorem prod_edges_chainA4 :
    ∏ i ∈ Finset.range 3, (chainA4 i).relIndex (chainA4 (i + 1)) =
      Nat.card ↥(alternatingGroup (Fin 4)) := by
  rw [Cor32.prod_relIndex_chain 3 chainA4_mono, chainA4_zero, chainA4_three,
    Subgroup.relIndex_bot_left, Cor32.natCard_top, card_alternating4]

/-! ### Realized factorizations of $A_4$ -/

/-- Every factorization `(a, b)` of $|A_4| = 12$ is realized by a
2-factorization (tex lines 223-225, via Corollary `solv`). -/
theorem exists_two_factorization_a4 (a b : ℕ) (hab : a * b = 12) :
    ∃ A₀ A₁ : Set ↥(alternatingGroup (Fin 4)),
      IsFactorization ![A₀, A₁] ∧ Nat.card A₀ = a ∧ Nat.card A₁ = b :=
  Cor32.exists_two_of_chain chainA4_zero chainA4_three chainA4_mono chainA4_prime
    a b (by rw [card_alternating4]; exact hab)

private theorem sing_inter_ne {x y : ℕ} (h : x ≠ y) :
    ({x} ∩ {y} : Finset ℕ) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [Finset.mem_inter, Finset.mem_singleton] at hw
  exact h (hw.1.symm.trans hw.2)

private theorem exists_three_a4_of_blocks (sB : Fin 3 → Finset ℕ)
    (aval : Fin 3 → ℕ)
    (hsub : ∀ t, sB t ⊆ Finset.Iio 3)
    (hdisj : ∀ t t' : Fin 3, t ≠ t' → sB t ∩ sB t' = ∅)
    (hcov : ∀ j, j < 3 → ∃ t, j ∈ sB t)
    (hone : ∀ j, j < 3 → ∀ t, j ∈ sB t →
      (∀ a' : Fin 3, a' < t → sB a' ∩ Finset.Iio (j + 1) = ∅) ∨
      (∀ a' : Fin 3, a' > t → sB a' ∩ Finset.Iio (j + 1) = ∅))
    (hcard : ∀ t, ∏ i ∈ sB t, (chainA4 i).relIndex (chainA4 (i + 1)) = aval t) :
    ∃ A : Fin 3 → Set ↥(alternatingGroup (Fin 4)),
      IsFactorization A ∧ ∀ t, Nat.card (A t) = aval t :=
  theorem_3_1 (k := 3) chainA4_zero chainA4_three chainA4_mono aval sB hsub hdisj
    hcov hone hcard

/-- Blocks for $(2,2,3)$: $s_1 = \{0\}$, $s_2 = \{1\}$, $s_3 = \{2\}$
(tex line 227, 0-based). -/
def blocks223 : Fin 3 → Finset ℕ :=
  fun t => if (t : ℕ) = 0 then {0} else if (t : ℕ) = 1 then {1} else {2}

/-- Sizes $(2,2,3)$. -/
def sizes223 : Fin 3 → ℕ :=
  fun t => if (t : ℕ) = 0 then 2 else if (t : ℕ) = 1 then 2 else 3

/-- Blocks for $(3,2,2)$: $s_1 = \{2\}$, $s_2 = \{1\}$, $s_3 = \{0\}$
(tex line 228, 0-based). -/
def blocks322 : Fin 3 → Finset ℕ :=
  fun t => if (t : ℕ) = 0 then {2} else if (t : ℕ) = 1 then {1} else {0}

/-- Sizes $(3,2,2)$. -/
def sizes322 : Fin 3 → ℕ :=
  fun t => if (t : ℕ) = 0 then 3 else if (t : ℕ) = 1 then 2 else 2

private theorem coe_fin3 (a : Fin 3) : (a:ℕ) = 0 ∨ (a:ℕ) = 1 ∨ (a:ℕ) = 2 := by
  have hilt := a.isLt
  revert hilt
  omega

private theorem mem_blocks223_eq {a : Fin 3} {w : ℕ} (hw : w ∈ blocks223 a) :
    w = (a:ℕ) := by
  rcases coe_fin3 a with h | h | h
  · unfold blocks223 at hw
    rw [h] at hw
    rw [if_pos rfl] at hw
    simp only [Finset.mem_singleton] at hw
    rw [h]
    exact hw
  · unfold blocks223 at hw
    rw [h] at hw
    rw [if_neg (by omega), if_pos rfl] at hw
    simp only [Finset.mem_singleton] at hw
    rw [h]
    exact hw
  · unfold blocks223 at hw
    rw [h] at hw
    rw [if_neg (by omega), if_neg (by omega)] at hw
    simp only [Finset.mem_singleton] at hw
    rw [h]
    exact hw

private theorem mem_blocks322_eq {a : Fin 3} {w : ℕ} (hw : w ∈ blocks322 a) :
    w + (a:ℕ) = 2 := by
  rcases coe_fin3 a with h | h | h
  · unfold blocks322 at hw
    rw [h] at hw
    rw [if_pos rfl] at hw
    simp only [Finset.mem_singleton] at hw
    rw [h]
    omega
  · unfold blocks322 at hw
    rw [h] at hw
    rw [if_neg (by omega), if_pos rfl] at hw
    simp only [Finset.mem_singleton] at hw
    rw [h]
    omega
  · unfold blocks322 at hw
    rw [h] at hw
    rw [if_neg (by omega), if_neg (by omega)] at hw
    simp only [Finset.mem_singleton] at hw
    rw [h]
    omega

theorem exists_factorization_a4_two_two_three :
    ∃ A : Fin 3 → Set ↥(alternatingGroup (Fin 4)),
      IsFactorization A ∧ ∀ t, Nat.card (A t) = sizes223 t := by
  refine exists_three_a4_of_blocks blocks223 sizes223 ?_ ?_ ?_ ?_ ?_
  · intro t
    fin_cases t <;> simp [blocks223]
  · intro t t' htt'
    fin_cases t <;> fin_cases t' <;> simp [blocks223] at *
  · intro j hj
    rcases Nat.lt_or_ge j 1 with h | h
    · refine ⟨⟨0, by omega⟩, ?_⟩
      simp [blocks223]
      omega
    · rcases Nat.lt_or_ge j 2 with h' | h'
      · refine ⟨⟨1, by omega⟩, ?_⟩
        simp [blocks223]
        omega
      · refine ⟨⟨2, by omega⟩, ?_⟩
        simp [blocks223]
        omega
  · intro j hj t ht
    fin_cases t
    · simp [blocks223, Finset.mem_singleton] at ht
      refine Or.inr fun a' ha' => ?_
      have hv : (0:ℕ) < (a':ℕ) := Fin.lt_iff_val_lt_val.mp ha'
      refine Finset.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
      rw [Finset.mem_inter] at hw
      obtain ⟨hB, hI⟩ := hw
      have hwe := mem_blocks223_eq hB
      simp only [Finset.mem_Iio] at hI
      omega
    · simp [blocks223, Finset.mem_singleton] at ht
      refine Or.inr fun a' ha' => ?_
      have hv : (1:ℕ) < (a':ℕ) := Fin.lt_iff_val_lt_val.mp ha'
      refine Finset.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
      rw [Finset.mem_inter] at hw
      obtain ⟨hB, hI⟩ := hw
      have hwe := mem_blocks223_eq hB
      simp only [Finset.mem_Iio] at hI
      omega
    · simp [blocks223, Finset.mem_singleton] at ht
      refine Or.inr fun a' ha' => ?_
      exfalso
      have hv : (2:ℕ) < (a':ℕ) := Fin.lt_iff_val_lt_val.mp ha'
      have hilt := a'.isLt
      omega
  · intro t
    fin_cases t <;>
      simp [blocks223, sizes223, edgeA4_0, edgeA4_1, edgeA4_2,
        Finset.prod_singleton]

theorem exists_factorization_a4_three_two_two :
    ∃ A : Fin 3 → Set ↥(alternatingGroup (Fin 4)),
      IsFactorization A ∧ ∀ t, Nat.card (A t) = sizes322 t := by
  refine exists_three_a4_of_blocks blocks322 sizes322 ?_ ?_ ?_ ?_ ?_
  · intro t
    fin_cases t <;> simp [blocks322]
  · intro t t' htt'
    fin_cases t <;> fin_cases t' <;> simp [blocks322] at *
  · intro j hj
    rcases Nat.lt_or_ge j 1 with h | h
    · refine ⟨⟨2, by omega⟩, ?_⟩
      simp [blocks322]
      omega
    · rcases Nat.lt_or_ge j 2 with h' | h'
      · refine ⟨⟨1, by omega⟩, ?_⟩
        simp [blocks322]
        omega
      · refine ⟨⟨0, by omega⟩, ?_⟩
        simp [blocks322]
        omega
  · intro j hj t ht
    fin_cases t
    · simp [blocks322, Finset.mem_singleton] at ht
      refine Or.inl fun a' ha' => ?_
      exfalso
      have hv : (a':ℕ) < (0:ℕ) := Fin.lt_iff_val_lt_val.mp ha'
      omega
    · simp [blocks322, Finset.mem_singleton] at ht
      refine Or.inl fun a' ha' => ?_
      have hv : (a':ℕ) < (1:ℕ) := Fin.lt_iff_val_lt_val.mp ha'
      refine Finset.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
      rw [Finset.mem_inter] at hw
      obtain ⟨hB, hI⟩ := hw
      have hwe := mem_blocks322_eq hB
      simp only [Finset.mem_Iio] at hI
      omega
    · simp [blocks322, Finset.mem_singleton] at ht
      refine Or.inl fun a' ha' => ?_
      have hv : (a':ℕ) < (2:ℕ) := Fin.lt_iff_val_lt_val.mp ha'
      refine Finset.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
      rw [Finset.mem_inter] at hw
      obtain ⟨hB, hI⟩ := hw
      have hwe := mem_blocks322_eq hB
      simp only [Finset.mem_Iio] at hI
      omega
  · intro t
    fin_cases t <;>
      simp [blocks322, sizes322, edgeA4_0, edgeA4_1, edgeA4_2,
        Finset.prod_singleton]

end McCulloch26_1.Cor33
