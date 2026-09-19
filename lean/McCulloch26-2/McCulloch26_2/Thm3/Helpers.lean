import McCulloch26_2.MultiPrime
import McCulloch26_2.PropClass
import McCulloch26_2.Basic

/-!
# Shared helper lemmas for Theorem 3

Lemmas used across multiple branches of the proof that no odd prime
can equal `|Aut(G)|/|G|` for a finite abelian group `G`.
-/

namespace McCulloch26_2

open scoped Nat

variable {N : ℕ}

/-! ### Helper lemmas -/

lemma TotalRatio_den_dvd_prod_pp (pp : Fin N → ℕ) (nn : Fin N → ℕ)
    (ff : ∀ i, Fin (nn i) → ℕ)
    (hpp : ∀ i, (pp i).Prime) (hs : ∀ i, Sorted (ff i))
    (hpos : ∀ i, Pos (ff i)) (hN : ∀ i, 0 < nn i) :
    (TotalRatio pp nn ff).den ∣ ∏ i, pp i := by
  have hcomp : ∀ i, (autRatio (pp i) (ff i)).den ∣ pp i := fun i =>
    den_autRatio_dvd (hpp i) (hs i) (hpos i) (hN i)
  have hd1 : (TotalRatio pp nn ff).den ∣ ∏ i, (autRatio (pp i) (ff i)).den :=
    den_prod_dvd _ (fun i => autRatio (pp i) (ff i))
  exact hd1.trans (prod_dvd_prod_of_pointwise Finset.univ
    (fun i => (autRatio (pp i) (ff i)).den) pp
    fun i _ => hcomp i)

lemma coprime_of_prime_dvd {a b p q : ℕ} (ha : a ∣ p) (hb : b ∣ q)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) : Nat.Coprime a b := by
  rcases (hp.eq_one_or_self_of_dvd a ha) with (rfl | rfl)
  · exact Nat.coprime_one_left _
  · rcases (hq.eq_one_or_self_of_dvd b hb) with (rfl | rfl)
    · exact Nat.coprime_one_right _
    · exact coprime_primes_ne hp hq hne

lemma den_coprime_of_distinct_primes (pp : Fin N → ℕ) (nn : Fin N → ℕ)
    (ff : ∀ i, Fin (nn i) → ℕ)
    (hpp : ∀ i, (pp i).Prime) (hs : ∀ i, Sorted (ff i))
    (hpos : ∀ i, Pos (ff i)) (hN : ∀ i, 0 < nn i)
    (hd : Function.Injective pp) {a b : Fin N} (hne : a ≠ b) :
    Nat.Coprime (autRatio (pp a) (ff a)).den (autRatio (pp b) (ff b)).den := by
  have hda : (autRatio (pp a) (ff a)).den ∣ pp a :=
    den_autRatio_dvd (hpp a) (hs a) (hpos a) (hN a)
  have hdb : (autRatio (pp b) (ff b)).den ∣ pp b :=
    den_autRatio_dvd (hpp b) (hs b) (hpos b) (hN b)
  have hne' : pp a ≠ pp b := by
    intro heq; apply hne; exact hd heq
  exact coprime_of_prime_dvd hda hdb (hpp a) (hpp b) hne'

lemma not_four_dvd_prod_distinct_primes (pp : Fin N → ℕ) (hpp : ∀ i, (pp i).Prime)
    (hd : Function.Injective pp) : ¬ 4 ∣ ∏ i, pp i := by
  by_cases h2 : ∃ i, pp i = 2
  · obtain ⟨i, hi⟩ := h2
    have h_others_odd : ∀ j, j ≠ i → Odd (pp j) := by
      intro j hjne
      rcases (Nat.Prime.eq_two_or_odd' (hpp j)) with (h | h)
      · exfalso; apply hjne; exact hd (h.trans hi.symm)
      · exact h
    have h_prod_eq : (∏ j : Fin N, pp j) = 2 * (∏ j ∈ (Finset.univ.erase i), pp j) := by
      calc
        (∏ j : Fin N, pp j) = (∏ j ∈ (Finset.univ.erase i), pp j) * pp i := by
          rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
        _ = (∏ j ∈ (Finset.univ.erase i), pp j) * 2 := by rw [hi]
        _ = 2 * (∏ j ∈ (Finset.univ.erase i), pp j) := by ring
    rw [h_prod_eq]
    intro h4
    have h2_dvd_rest : 2 ∣ ∏ j ∈ (Finset.univ.erase i), pp j :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h4
    have h_rest_odd : Odd (∏ j ∈ (Finset.univ.erase i), pp j) :=
      Finset.prod_induction pp (fun x => Odd x)
        (fun a b ha hb => ha.mul hb) (by simp) (fun j hj => h_others_odd j (Finset.ne_of_mem_erase hj))
    exact h_rest_odd.not_two_dvd_nat h2_dvd_rest
  · have h_all_odd : ∀ i, Odd (pp i) := by
      intro i
      rcases (Nat.Prime.eq_two_or_odd' (hpp i)) with (h | h)
      · exfalso; exact h2 ⟨i, h⟩
      · exact h
    have h_prod_odd : Odd (∏ i, pp i) :=
      Finset.prod_induction pp (fun x => Odd x)
        (fun a b ha hb => ha.mul hb) (by simp) (fun i _ => h_all_odd i)
    intro h4
    have h2_dvd : 2 ∣ ∏ i, pp i := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4
    exact h_prod_odd.not_two_dvd_nat h2_dvd

lemma totalRatio_eq_iff_cross (pp : Fin N → ℕ) (nn : Fin N → ℕ)
    (ff : ∀ i, Fin (nn i) → ℕ)
    (hpp : ∀ i, (pp i).Prime) (hs : ∀ i, Sorted (ff i))
    (hpos : ∀ i, Pos (ff i)) (hN : ∀ i, 0 < nn i)
    (p : ℕ) (hp : p.Prime) (hEq : TotalRatio pp nn ff = (p : ℚ)) :
    (∏ k, ((autRatio (pp k) (ff k)).num.natAbs : ℕ)) = p * (∏ k, (autRatio (pp k) (ff k)).den) := by
  have h_total_div : TotalRatio pp nn ff =
      (∏ k, ((autRatio (pp k) (ff k)).num : ℚ)) / (∏ k, ((autRatio (pp k) (ff k)).den : ℚ)) := by
    rw [TotalRatio]
    calc
      (∏ i, autRatio (pp i) (ff i)) = (∏ i, (((autRatio (pp i) (ff i)).num : ℚ) / ((autRatio (pp i) (ff i)).den : ℚ))) := by
        refine Finset.prod_congr rfl (fun i hi => ?_)
        rw [Rat.num_div_den]
      _ = (∏ i, ((autRatio (pp i) (ff i)).num : ℚ)) / (∏ i, ((autRatio (pp i) (ff i)).den : ℚ)) := by
        rw [Finset.prod_div_distrib]
  rw [h_total_div] at hEq
  have h_den_pos : 0 < ∏ k, ((autRatio (pp k) (ff k)).den : ℚ) :=
    Finset.prod_pos (fun k hk => by
      have := (autRatio (pp k) (ff k)).den_pos
      exact_mod_cast this)
  field_simp [h_den_pos.ne'] at hEq
  -- hEq: (∏ k, (num : ℚ)) = (∏ k, (den : ℚ)) * (p : ℚ)
  -- All numerators are nonnegative, so (num : ℚ) = ((num.natAbs : ℕ) : ℚ)
  have h_num_nonneg : ∀ k, 0 ≤ (autRatio (pp k) (ff k)).num := by
    intro k
    have h_ratio_nonneg : 0 ≤ (autRatio (pp k) (ff k) : ℚ) := by
      unfold autRatio
      positivity
    exact (Rat.num_nonneg.mpr h_ratio_nonneg)
  have h_rewrite : (∏ k, ((autRatio (pp k) (ff k)).num : ℚ)) =
      (∏ k, (((autRatio (pp k) (ff k)).num.natAbs : ℕ) : ℚ)) := by
    refine Finset.prod_congr rfl (fun k hk => ?_)
    have hn := h_num_nonneg k
    have hn' : 0 ≤ ((autRatio (pp k) (ff k)).num : ℚ) := by exact_mod_cast hn
    simp [Nat.cast_natAbs, abs_of_nonneg hn']
  rw [h_rewrite] at hEq
  -- Now hEq: (∏ k, (natAbs num : ℚ)) = (∏ k, (den : ℚ)) * (p : ℚ)
  -- Both sides are natural numbers cast to ℚ, so exact_mod_cast works
  have h_nat : (∏ k, ((autRatio (pp k) (ff k)).num.natAbs : ℕ)) =
      (∏ k, (autRatio (pp k) (ff k)).den) * p := by
    exact_mod_cast hEq
  simpa [mul_comm] using h_nat

lemma num_den_of_nat_div {a b : ℕ} (h_cop : Nat.Coprime a b) (hb_pos : 0 < b) :
    (((a : ℚ) / (b : ℚ)).num.natAbs : ℕ) = a ∧ ((a : ℚ) / (b : ℚ)).den = b := by
  have hb_pos_int : 0 < (b : ℤ) := by exact_mod_cast hb_pos
  have h_cop_int : Nat.Coprime ((a : ℤ).natAbs) ((b : ℤ).natAbs) := by
    simpa [Int.natAbs_natCast] using h_cop
  have h_num := Rat.num_div_eq_of_coprime hb_pos_int h_cop_int
  have h_den := Rat.den_div_eq_of_coprime hb_pos_int h_cop_int
  have h_nonneg : 0 ≤ ((a : ℚ) / (b : ℚ)).num := by
    have h_ratio_nonneg : 0 ≤ ((a : ℚ) / (b : ℚ)) :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact Rat.num_nonneg.mpr h_ratio_nonneg
  refine ⟨?_, ?_⟩
  · simpa [Int.natAbs_of_nonneg h_nonneg] using congrArg (fun x : ℤ => x.natAbs) h_num
  · simpa using h_den

lemma autRatio_two_num_of_den_two {n : ℕ} {f : Fin n → ℕ} (hf : Sorted f)
    (hpos : Pos f) (hn : 0 < n) (hden : (autRatio 2 f).den = 2) :
    (autRatio 2 f).num.natAbs = 1 ∨ (autRatio 2 f).num.natAbs = 3 := by
  rcases prop_class (by norm_num : Nat.Prime 2) hf hpos hn with
    (⟨hn1, hr⟩ | ⟨hn2, hall, hr⟩ | ⟨hn2', hf0, hnotall, hr⟩
     | ⟨hn3, hall3, hr⟩ | hd)
  · -- n = 1: autRatio = 1/2, num = 1
    have h := num_den_of_nat_div (by norm_num : Nat.Coprime (2 - 1) 2) (by norm_num : 0 < 2)
    have hnum : (autRatio 2 f).num.natAbs = 1 := by
      rw [hr]; simpa using h.1
    left; exact hnum
  · -- n = 2, all = 1: autRatio = 3/2, num = 3
    have h_cop : Nat.Coprime ((2 - 1) ^ 2 * (2 + 1)) 2 := by
      norm_num [Nat.coprime_iff_gcd_eq_one]
    have h := num_den_of_nat_div h_cop (by norm_num : 0 < 2)
    have hnum : (autRatio 2 f).num.natAbs = 3 := by
      rw [hr]; simpa using h.1
    right; exact hnum
  · -- n = 2, f 0 = 1, not all = 1: autRatio = 1, den = 1, contradicts hden
    rw [hr] at hden; norm_num at hden
  · -- n = 3, all = 1: autRatio = 21, den = 1, contradicts hden
    rw [hr] at hden; norm_num at hden
  · -- else: den = 1, contradicts hden
    obtain ⟨w, hw⟩ := hd
    have hrepr : autRatio 2 f = (((2 - 1) ^ 2 * 2 * w : ℕ) : ℚ) := by
      unfold autRatio GroupCard; rw [hw, Nat.pow_succ']
      have hdz : (((2 ^ (∑ i : Fin n, f i) : ℕ) : ℚ)) ≠ 0 := by
        exact_mod_cast (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
      rw [div_eq_iff hdz]; push_cast; ring
    have h_den := (num_den_of_repr_nat hrepr).2
    rw [h_den] at hden; norm_num at hden

lemma autRatio_two_num_of_den_two' {n : ℕ} {f : Fin n → ℕ} (hf : Sorted f)
    (hpos : Pos f) (hn : 0 < n) (hden : (autRatio 2 f).den = 2)
    (h_not_all_sorted : ¬ (∀ i, f i = 1)) :
    (autRatio 2 f).num.natAbs = 1 := by
  rcases prop_class (by norm_num : Nat.Prime 2) hf hpos hn with
    (⟨hn1, hr⟩ | ⟨hn2, hall, hr⟩ | ⟨hn2', hf0, hnotall, hr⟩
     | ⟨hn3, hall3, hr⟩ | hd)
  · -- n = 1: autRatio = 1/2, num = 1
    have h := num_den_of_nat_div (by norm_num : Nat.Coprime (2 - 1) 2) (by norm_num : 0 < 2)
    rw [hr]; simpa using h.1
  · -- n = 2, all = 1: contradicts h_not_all_sorted
    exfalso; exact h_not_all_sorted hall
  · -- n = 2, f 0 = 1, not all = 1: autRatio = 1, num = 1
    have h := num_den_of_repr_nat hr
    simpa [Int.natAbs_of_nonneg (pow_two_nonneg _)] using congrArg Int.natAbs h.1
  · -- n = 3, all = 1: den = 1, contradicts hden
    rw [hr] at hden; norm_num at hden
  · -- else: den = 1, contradicts hden
    obtain ⟨w, hw⟩ := hd
    have hrepr : autRatio 2 f = (((2 - 1) ^ 2 * 2 * w : ℕ) : ℚ) := by
      unfold autRatio GroupCard; rw [hw, Nat.pow_succ']
      have hdz : (((2 ^ (∑ i : Fin n, f i) : ℕ) : ℚ)) ≠ 0 := by
        exact_mod_cast (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
      rw [div_eq_iff hdz]; push_cast; ring
    have h_den := (num_den_of_repr_nat hrepr).2
    rw [h_den] at hden; norm_num at hden

lemma square_dvd_two_mul_odd_prime {m p : ℕ} (hp : p.Prime) (hodd : Odd p) (h : m ^ 2 ∣ 2 * p) :
    m = 1 ∨ m = 2 := by
  have hm_pos : 0 < m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    rw [hm0', pow_two] at h
    have : (0 : ℕ) ^ 2 = 0 := by norm_num
    simp [this] at h
    have hp0 : p = 0 := by
      have := hp.pos
      omega
    exact hp.ne_zero hp0
  have hm_ge_1 : 1 ≤ m := hm_pos
  by_cases hm_le_2 : m ≤ 2
  · omega
  · -- m > 2: then m has a prime factor q ≥ 3
    have hm_gt_2 : 2 < m := by omega
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    have hq_sq_dvd : q ^ 2 ∣ m ^ 2 := by
      rw [sq, sq]
      exact mul_dvd_mul hq_dvd hq_dvd
    have hq_sq_dvd_2p : q ^ 2 ∣ 2 * p := Nat.dvd_trans hq_sq_dvd h
    by_cases hq2 : q = 2
    · -- q = 2: then 4 ∣ 2p, so 2 ∣ p, contradiction (p is odd)
      rw [hq2] at hq_sq_dvd_2p
      have h4_dvd_2p : 4 ∣ 2 * p := hq_sq_dvd_2p
      -- 4 = 2*2, so 2*2 ∣ 2*p → 2 ∣ p
      have h2_dvd_p : 2 ∣ p := by
        have htemp : 2 * 2 ∣ 2 * p := by rwa [show (4 : ℕ) = 2 * 2 by norm_num] at h4_dvd_2p
        -- 2*2 ∣ 2*p → 2 ∣ p
        rcases htemp with ⟨k, hk⟩
        use k
        omega
      have hp_eq_2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 2) hp).mp h2_dvd_p).symm
      rw [hp_eq_2] at hodd; simp [Odd] at hodd
    · -- q is odd prime, so q ∣ p (since q^2 ∣ 2p and q ≠ 2)
      have hq_dvd_q2 : q ∣ q ^ 2 := by
        rw [sq]; exact dvd_mul_right q q
      have hq_dvd_2p : q ∣ 2 * p := Nat.dvd_trans hq_dvd_q2 hq_sq_dvd_2p
      -- q is prime ≠ 2, so coprime to 2
      have h_cop : Nat.Coprime q 2 :=
        (hq_prime.coprime_iff_not_dvd).mpr fun hq_dvd_2 =>
          hq2 ((Nat.prime_dvd_prime_iff_eq hq_prime (by norm_num : Nat.Prime 2)).mp hq_dvd_2)
      have hq_dvd_p : q ∣ p := h_cop.dvd_of_dvd_mul_left hq_dvd_2p
      have hq_eq_p : q = p := ((Nat.prime_dvd_prime_iff_eq hq_prime hp).mp hq_dvd_p)
      rw [hq_eq_p] at hq_sq_dvd_2p
      -- p^2 ∣ 2p → p ∣ 2 → p = 2, contradiction
      have hp_sq_dvd_2p : p ^ 2 ∣ 2 * p := hq_sq_dvd_2p
      rw [show p ^ 2 = p * p by ring] at hp_sq_dvd_2p
      have hp_dvd_2 : p ∣ 2 := by
        rcases hp_sq_dvd_2p with ⟨k, hk⟩
        -- hk: 2*p = (p*p)*k
        have h_eq : p * 2 = p * (p * k) := by
          calc
            p * 2 = 2 * p := mul_comm _ _
            _ = (p * p) * k := hk
            _ = p * (p * k) := by ring
        have h_cancel : 2 = p * k :=
          Nat.eq_of_mul_eq_mul_left hp.pos h_eq
        exact ⟨k, h_cancel⟩
      have hp_eq_2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2)).mp hp_dvd_2
      rw [hp_eq_2] at hodd; simp [Odd] at hodd

end McCulloch26_2
