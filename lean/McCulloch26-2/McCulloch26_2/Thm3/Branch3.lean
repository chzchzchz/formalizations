import McCulloch26_2.Thm3.Helpers
import McCulloch26_2.PropClass
import McCulloch26_2.Basic

/-!
# Branch 3: no odd components

If every prime component is a 2-group, then the total ratio cannot equal
an odd prime `p`.

Paper lines 176-182; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 176-182.
-/

namespace McCulloch26_2

open scoped Nat

variable {N : ℕ}

/-! ### Branch 3: no odd components (already proved) -/

lemma injective_prime_const_le_one (pp : Fin N → ℕ) (hd : Function.Injective pp)
    (p₀ : ℕ) (hpp : ∀ i, pp i = p₀) : N ≤ 1 := by
  by_contra hNge
  push_neg at hNge
  have hex : ∃ i j : Fin N, i ≠ j :=
    ⟨⟨0, Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hNge⟩,
     ⟨1, Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hNge⟩, by simp⟩
  obtain ⟨i, j, hij⟩ := hex
  have h_eq : pp i = pp j := by simp [hpp]
  exact hd.ne hij h_eq

lemma TotalRatio_empty (pp : Fin 0 → ℕ) (nn : Fin 0 → ℕ) (ff : ∀ i, Fin (nn i) → ℕ) :
    TotalRatio pp nn ff = (1 : ℚ) := by
  simp [TotalRatio]

lemma TotalRatio_singleton (pp : Fin 1 → ℕ) (nn : Fin 1 → ℕ)
    (ff : ∀ i, Fin (nn i) → ℕ) :
    TotalRatio pp nn ff = autRatio (pp 0) (ff 0) := by
  simp [TotalRatio]

theorem thm3_branch_no_odd_components (pp : Fin N → ℕ) (nn : Fin N → ℕ)
    (ff : ∀ i, Fin (nn i) → ℕ)
    (hpp : ∀ i, (pp i).Prime) (hs : ∀ i, Sorted (ff i))
    (hpos : ∀ i, Pos (ff i)) (hN : ∀ i, 0 < nn i)
    (hd : Function.Injective pp) (p : ℕ) (hp : p.Prime)
    (hodd : Odd p)
    (h_no_odd : ∀ i, pp i = 2)
    (hEq : TotalRatio pp nn ff = (p : ℚ)) : False := by
  have hN_le_1 : N ≤ 1 := injective_prime_const_le_one pp hd 2 h_no_odd
  rcases Nat.lt_or_ge N 1 with hN0 | hN1
  · have hN0_eq : N = 0 := by omega
    subst hN0_eq
    rw [TotalRatio_empty] at hEq
    have hp_eq_1 : p = 1 := by
      have h : (1 : ℚ) = (p : ℚ) := hEq
      exact_mod_cast h.symm
    exact absurd hp.ne_one (by omega)
  · have hN_eq : N = 1 := by omega
    subst hN_eq
    rw [TotalRatio_singleton] at hEq
    have hp0 : pp 0 = 2 := h_no_odd 0
    have h_eq2 : (autRatio (pp 0) (ff 0) : ℚ) = (autRatio 2 (ff 0) : ℚ) := by rw [hp0]
    rw [h_eq2] at hEq
    rcases prop_class Nat.prime_two (hs 0) (hpos 0) (hN 0) with
      (⟨_, hr⟩ | ⟨_, _, hr⟩ | ⟨_, _, _, hr⟩ | ⟨_, _, hr⟩ | hdvd)
    · -- hr : autRatio 2 (ff 0) = (1 : ℚ) / (2 : ℚ)
      rw [hr] at hEq
      have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
      have hfrac : (1 : ℚ) / 2 < 1 := by norm_num
      linarith
    · -- hr : autRatio 2 (ff 0) = (3 : ℚ) / (2 : ℚ)
      rw [hr] at hEq
      have hp3 : (3 : ℚ) ≤ (p : ℚ) := by
        have hp3_nat : (3 : ℕ) ≤ p := by
          rcases Nat.lt_or_ge p 3 with hp3 | hp3
          · have hp2 : p = 2 := by
              have hp_ge2 : 2 ≤ p := hp.two_le; omega
            rw [hp2] at hodd; simp [Odd] at hodd
          · exact hp3
        exact_mod_cast hp3_nat
      have hfrac : (3 : ℚ) / 2 < 3 := by norm_num
      linarith
    · -- hr : autRatio 2 (ff 0) = (1 : ℚ)
      rw [hr] at hEq
      have hp_eq_1 : p = 1 := by
        have h : (1 : ℚ) = (p : ℚ) := hEq
        exact_mod_cast h.symm
      exact absurd hp.ne_one (by omega)
    · -- hr : autRatio 2 (ff 0) = (21 : ℚ)
      rw [hr] at hEq
      have hp_eq_21 : p = 21 := by
        have h : (21 : ℚ) = (p : ℚ) := hEq
        exact_mod_cast h.symm
      rw [hp_eq_21] at hp; exact absurd hp (by decide)
    · -- hdvd: 2^((sum ff0)+1) * (2-1)^2 ∣ AutFormula 2 (ff 0)
      obtain ⟨w, hw⟩ := hdvd
      have hw' : autRatio 2 (ff 0) = ((2 * w : ℕ) : ℚ) := by
        unfold autRatio GroupCard
        rw [hw, Nat.pow_succ']
        have hden : (((2 ^ (∑ i : Fin (nn 0), ff 0 i) : ℕ) : ℚ)) ≠ 0 := by
          exact_mod_cast (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
        rw [div_eq_iff hden]; push_cast; ring
      rw [hw'] at hEq
      have hp_even : p = 2 * w := by
        have h : ((2 * w : ℕ) : ℚ) = (p : ℚ) := hEq
        exact_mod_cast h.symm
      rw [hp_even] at hodd; rcases hodd with ⟨k, hk⟩; omega

end McCulloch26_2
