import McCulloch26_2.Thm3.Helpers
import McCulloch26_2.TwoOddComponentsImpFourDvdNum

/-!
# Branch 1: at least two odd components

If the decomposition has two distinct components with odd prime exponents,
then the total ratio cannot equal an odd prime `p`.

Paper lines 176-182; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 176-182.
-/

namespace McCulloch26_2

open scoped Nat

variable {N : ℕ}

/-! ### Branch 1: at least two odd components -/

theorem thm3_branch_two_odd_components (pp : Fin N → ℕ) (nn : Fin N → ℕ)
    (ff : ∀ i, Fin (nn i) → ℕ)
    (hpp : ∀ i, (pp i).Prime) (hs : ∀ i, Sorted (ff i))
    (hpos : ∀ i, Pos (ff i)) (hN : ∀ i, 0 < nn i)
    (hd : Function.Injective pp) (p : ℕ) (hp : p.Prime)
    (hodd : Odd p)
    {a b : Fin N} (hij : a ≠ b)
    (hodd_a : Odd (pp a)) (hodd_b : Odd (pp b))
    (hEq : TotalRatio pp nn ff = (p : ℚ)) : False := by
  have h_cross := totalRatio_eq_iff_cross pp nn ff hpp hs hpos hN p hp hEq
  -- h_cross : (∏ k, (num.natAbs : ℕ)) = p * (∏ k, (den : ℕ))
  have h4_dvd_prod : 4 ∣ (autRatio (pp a) (ff a)).num * (autRatio (pp b) (ff b)).num :=
    two_odd_components_imp_four_dvd_num pp nn ff hpp hs hpos hN hodd_a hodd_b
  -- Convert to ℕ: since numerators are nonnegative, natAbs preserves divisibility
  have h_num_nonneg_a : 0 ≤ (autRatio (pp a) (ff a)).num := by
    have h_ratio_nonneg : 0 ≤ (autRatio (pp a) (ff a) : ℚ) := by
      unfold autRatio
      refine div_nonneg ?_ ?_
      · apply Nat.cast_nonneg
      · apply Nat.cast_nonneg
    exact (Rat.num_nonneg.mpr h_ratio_nonneg)
  have h_num_nonneg_b : 0 ≤ (autRatio (pp b) (ff b)).num := by
    have h_ratio_nonneg : 0 ≤ (autRatio (pp b) (ff b) : ℚ) := by
      unfold autRatio
      refine div_nonneg ?_ ?_
      · apply Nat.cast_nonneg
      · apply Nat.cast_nonneg
    exact (Rat.num_nonneg.mpr h_ratio_nonneg)
  have h4_dvd_nat : 4 ∣ ((autRatio (pp a) (ff a)).num.natAbs : ℕ) *
      ((autRatio (pp b) (ff b)).num.natAbs : ℕ) := by
    have ha : ((autRatio (pp a) (ff a)).num.natAbs : ℤ) = (autRatio (pp a) (ff a)).num :=
      Int.natAbs_of_nonneg h_num_nonneg_a
    have hb : ((autRatio (pp b) (ff b)).num.natAbs : ℤ) = (autRatio (pp b) (ff b)).num :=
      Int.natAbs_of_nonneg h_num_nonneg_b
    have htemp : (4 : ℤ) ∣ ((autRatio (pp a) (ff a)).num.natAbs : ℤ) *
        ((autRatio (pp b) (ff b)).num.natAbs : ℤ) := by
      rw [ha, hb]; exact h4_dvd_prod
    -- mod_cast from ℤ to ℕ: all values are nonnegative integers
    have h_nonneg_prod : 0 ≤ ((autRatio (pp a) (ff a)).num.natAbs : ℤ) *
        ((autRatio (pp b) (ff b)).num.natAbs : ℤ) := by
      apply mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact mod_cast htemp
  have h4_dvd_num_prod_nat : 4 ∣ ∏ k, ((autRatio (pp k) (ff k)).num.natAbs) := by
    have h_pair_prod : ((autRatio (pp a) (ff a)).num.natAbs : ℕ) *
        ((autRatio (pp b) (ff b)).num.natAbs : ℕ) ∣
        ∏ k, ((autRatio (pp k) (ff k)).num.natAbs : ℕ) := by
      have h_sub : ({a, b} : Finset (Fin N)) ⊆ Finset.univ := by simp
      have h_prod_pair : (∏ k ∈ ({a, b} : Finset (Fin N)), ((autRatio (pp k) (ff k)).num.natAbs : ℕ)) =
          ((autRatio (pp a) (ff a)).num.natAbs : ℕ) * ((autRatio (pp b) (ff b)).num.natAbs : ℕ) := by
        simp [hij]
      rw [← h_prod_pair]
      exact Finset.prod_dvd_prod_of_subset _ _ (fun k => ((autRatio (pp k) (ff k)).num.natAbs : ℕ)) h_sub
    exact Nat.dvd_trans h4_dvd_nat h_pair_prod
  rw [h_cross] at h4_dvd_num_prod_nat
  -- h4_dvd_num_prod_nat : 4 ∣ p * (∏ k, (autRatio (pp k) (ff k)).den)
  have h4_not_dvd_p : ¬ 4 ∣ p := by
    have h2_not_dvd_p : ¬ 2 ∣ p := by
      rcases hodd with ⟨k, hk⟩
      intro h2
      have : 2 ∣ 2 * k + 1 := by rw [← hk]; exact h2
      omega
    intro h4
    have : 2 ∣ p := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4
    exact h2_not_dvd_p this
  have h4_not_dvd_den_prod : ¬ 4 ∣ ∏ k, (autRatio (pp k) (ff k)).den := by
    have h_den_dvd_pp : ∀ k, (autRatio (pp k) (ff k)).den ∣ pp k := fun k =>
      den_autRatio_dvd (hpp k) (hs k) (hpos k) (hN k)
    have h_den_prod_dvd : (∏ k, (autRatio (pp k) (ff k)).den) ∣ ∏ k, pp k :=
      prod_dvd_prod_of_pointwise Finset.univ
        (fun k => (autRatio (pp k) (ff k)).den) pp
        fun i _ => h_den_dvd_pp i
    intro h4
    have h4_dvd_prod_pp : 4 ∣ ∏ k, pp k := Nat.dvd_trans h4 h_den_prod_dvd
    exact not_four_dvd_prod_distinct_primes pp hpp hd h4_dvd_prod_pp
  -- From 4 ∣ p * den_prod, derive contradiction via 2-adic valuation
  have h2_dvd_den_prod : 2 ∣ ∏ k, (autRatio (pp k) (ff k)).den := by
    have h2_dvd_mul : 2 ∣ p * (∏ k, (autRatio (pp k) (ff k)).den) :=
      Nat.dvd_trans (by norm_num : 2 ∣ 4) h4_dvd_num_prod_nat
    have h2_not_dvd_p : ¬ 2 ∣ p := by
      rcases hodd with ⟨k, hk⟩
      intro h2
      have : 2 ∣ 2 * k + 1 := by rw [← hk]; exact h2
      omega
    rcases Nat.prime_two.dvd_mul.mp h2_dvd_mul with (h | h)
    · exact absurd h h2_not_dvd_p
    · exact h
  obtain ⟨m, hm⟩ := h2_dvd_den_prod
  -- hm : ∏ k, (autRatio (pp k) (ff k)).den = 2 * m
  rw [hm] at h4_dvd_num_prod_nat
  -- h4_dvd_num_prod_nat : 4 ∣ p * (2 * m)
  -- Rewrite: p * (2 * m) = 2 * (p * m)
  have h_eq : p * (2 * m) = 2 * (p * m) := by ring
  rw [h_eq] at h4_dvd_num_prod_nat
  -- h4_dvd_num_prod_nat : 4 ∣ 2 * (p * m)
  -- Since 4 = 2*2, we have 2 ∣ p*m
  have h2_dvd_pm : 2 ∣ p * m :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h4_dvd_num_prod_nat
  have h2_not_dvd_p : ¬ 2 ∣ p := by
    rcases hodd with ⟨k, hk⟩
    intro h2
    have : 2 ∣ 2 * k + 1 := by rw [← hk]; exact h2
    omega
  rcases Nat.prime_two.dvd_mul.mp h2_dvd_pm with (h | h)
  · exact absurd h h2_not_dvd_p
  · -- h : 2 ∣ m, so 4 ∣ 2*m, hence 4 ∣ den_prod
    have h4_dvd_den_prod : 4 ∣ ∏ k, (autRatio (pp k) (ff k)).den := by
      rw [hm]
      obtain ⟨m', hm'⟩ := h
      rw [hm']
      -- 4 ∣ 2 * (2 * m') = 4 * m'
      use m'
      ring
    exact absurd h4_dvd_den_prod h4_not_dvd_den_prod

end McCulloch26_2
