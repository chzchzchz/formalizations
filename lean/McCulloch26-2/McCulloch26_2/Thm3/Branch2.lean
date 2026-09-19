import McCulloch26_2.Thm3.Helpers
import Mathlib.Algebra.BigOperators.Fin

/-!
# Branch 2: exactly one odd component

If the decomposition has exactly one odd-prime component (all others are
2-groups), then the total ratio cannot equal an odd prime `p`.

## Paper reference

`/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex` lines 180-182.

## Proof structure (transcribed from the paper)

Write each per-component ratio as `a_i / b_i` in lowest terms.  By
`prop_class` (via `den_autRatio_dvd`) each `b_i` is `1` or the component's
prime, and the cross equation `∏ num = p * ∏ den` holds
(`totalRatio_eq_iff_cross`).

* Step 1 (`odd_comp_num_cases`): for an odd-prime component with prime `q`,
  either `4 ∣ num` (every `prop_class` case except the cyclic one has
  `(q-1)^2 ∣ num`, and `2 ∣ q-1` since `q` is odd), or the component is
  cyclic with `num = q-1` and `den = q`.
* Step 2 (paper: "we conclude that `p = 2`, a contradiction"): if `4 ∣ num`
  of the odd component, then `4 ∣ p * den_odd * den_two` by the cross
  equation; `p`, `den_odd` are odd and `den_two ∣ 2`, so `den_two = 2` and
  cancelling one factor 2 leaves `2 ∣ p * den_odd`, impossible.
* Step 3 (paper: "since `2` divides `a_2`, we must have `b_1 = 2`"): in the
  cyclic case `2 ∣ q - 1 = num_odd`, so `2 ∣ p * q * den_two` by the cross
  equation, forcing `den_two = 2`.
* Step 4 (paper: "we cannot have `a_1 = 1`, and ... `a_1 = 3`"): a 2-group
  component with denominator 2 is cyclic (`num = 1`) or `(Z/2)^2`
  (`num = 3`, `autRatio_two_num_of_den_two`).
  - `num_two = 1`: `q - 1 = 2 p q` is impossible since `q ≤ 2 p q`.
  - `num_two = 3`: `3 (q - 1) = 2 p q` is impossible since `p ≥ 3` gives
    `3 q ≤ p q ≤ 2 p q`, i.e. `3(q-1) < 2 p q`.

The `N = 1` degenerate (single odd component) is the same argument with an
empty product for the 2-group side.
-/

namespace McCulloch26_2

open scoped Nat

variable {N : ℕ}

/-! ### Small arithmetic helpers -/

/-- An odd prime is at least `3`. -/
lemma prime_odd_ge_three {p : ℕ} (hp : p.Prime) (hodd : Odd p) : 3 ≤ p := by
  rcases hodd with ⟨k, hk⟩
  have h2 := hp.two_le
  omega

/-- A divisor of an odd natural number is odd: otherwise the divisor's
factor 2 would divide the (odd) number. -/
lemma odd_of_dvd_odd {d q : ℕ} (hodd : Odd q) (hd : d ∣ q) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · exfalso
    obtain ⟨k, hk⟩ := he
    obtain ⟨m, hm⟩ := hd
    exact hodd.not_two_dvd_nat (by rw [hm, hk]; exact ⟨k * m, by ring⟩)
  · exact ho

/-- `q - 1` is even for odd `q`. -/
lemma two_dvd_sub_one_of_odd {q : ℕ} (hodd : Odd q) : 2 ∣ q - 1 := by
  obtain ⟨k, hk⟩ := hodd
  exact ⟨k, by omega⟩

/-- `(q - 1)^2` is divisible by `4` for odd `q` (write `q - 1 = 2k`). -/
lemma four_dvd_sq_sub_one {q : ℕ} (hodd : Odd q) : 4 ∣ (q - 1) ^ 2 := by
  obtain ⟨k, hk⟩ := two_dvd_sub_one_of_odd hodd
  rw [pow_two, hk]
  exact ⟨k * k, by ring⟩

/-! ### Step 1: numerator shape of an odd-prime component -/

/-- Paper lines 180-181: for an odd-prime component with prime `q`, either
`4` divides its numerator (all `prop_class` shapes except the cyclic one
carry a factor `(q-1)^2`, and `4 ∣ (q-1)^2`), or the component is cyclic
with ratio `(q-1)/q` in lowest terms. -/
lemma odd_comp_num_cases {n : ℕ} {q : ℕ} {f : Fin n → ℕ} (hq : q.Prime)
    (hodd : Odd q) (hf : Sorted f) (hpos : Pos f) (hn : 0 < n) :
    4 ∣ (autRatio q f).num.natAbs ∨
    ((autRatio q f).num.natAbs = q - 1 ∧ (autRatio q f).den = q) := by
  have h4sq : 4 ∣ (q - 1) ^ 2 := four_dvd_sq_sub_one hodd
  rcases prop_class hq hf hpos hn with
    (⟨hn1, hr⟩ | ⟨hn2, hall, hr⟩ | ⟨hn2', hf0, hnotall, hr⟩
     | ⟨hn3, hall3, hr⟩ | hd)
  · -- case 1 (cyclic): ratio = (q-1)/q, already in lowest terms
    right
    have h_cop : Nat.Coprime (q - 1) q := nat_coprime_pred_self hq.one_lt
    have hnd := num_den_of_nat_div h_cop hq.pos
    rw [hr]
    exact ⟨hnd.1, hnd.2⟩
  · -- case 2 (Z_q × Z_q): num = (q-1)^2 (q+1), den = q
    left
    have h_cop1 : Nat.Coprime (q - 1) q := nat_coprime_pred_self hq.one_lt
    have h_cop_sq : Nat.Coprime ((q - 1) ^ 2) q := by
      rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]; exact h_cop1
    have h_cop_add : Nat.Coprime (q + 1) q := by
      rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
      calc
        Nat.gcd q (q + 1) = Nat.gcd q 1 := by
          rw [add_comm, Nat.gcd_add_self_right q 1]
        _ = 1 := Nat.gcd_one_right _
    have h_cop : Nat.Coprime ((q - 1) ^ 2 * (q + 1)) q := by
      rw [Nat.coprime_mul_iff_left]; exact ⟨h_cop_sq, h_cop_add⟩
    have hnd := num_den_of_nat_div h_cop hq.pos
    rw [hr, hnd.1]
    exact Nat.dvd_trans h4sq ⟨q + 1, by ring⟩
  · -- case 3 (Z_q × Z_{q^i}): integer ratio (q-1)^2, num = (q-1)^2
    left
    have hnd := num_den_of_repr_nat hr
    rw [hnd.1]
    rw [Int.natAbs_natCast]
    exact h4sq
  · -- case 4 (Z_q^3): integer ratio, num divisible by (q-1)^2
    left
    have hnd := num_den_of_repr_nat hr
    rw [hnd.1]
    rw [Int.natAbs_natCast]
    exact Nat.dvd_trans h4sq ⟨(q - 1) * (q + 1) * (q ^ 2 + q + 1), by ring⟩
  · -- case 5 (generic): integer ratio divisible by q (q-1)^2
    obtain ⟨w, hw⟩ := hd
    have hrepr : autRatio q f = (((q - 1) ^ 2 * q * w : ℕ) : ℚ) := by
      unfold autRatio GroupCard; rw [hw, Nat.pow_succ']
      have hdz : (((q ^ (∑ i : Fin n, f i) : ℕ) : ℚ)) ≠ 0 := by
        exact_mod_cast (pow_ne_zero _ hq.ne_zero)
      rw [div_eq_iff hdz]; push_cast; ring
    have hnd := num_den_of_repr_nat hrepr
    left
    rw [hnd.1]
    rw [Int.natAbs_natCast]
    exact Nat.dvd_trans h4sq ⟨q * w, by ring⟩

/-! ### Step 2: `4 ∣` odd numerator is impossible -/

/-- Paper line 180: if `4` divides the odd component's numerator, the cross
equation forces `4 ∣ p * den_odd * den_two`; since `p` and `den_odd` are odd
and `den_two ∣ 2`, this would give `2 ∣ p * den_odd` after cancelling. -/
lemma four_dvd_num_impossible (p q : ℕ)
    (hodd_p : Odd p) (hodd_q : Odd q)
    {den_odd den_two : ℕ} (hden_odd_dvd : den_odd ∣ q) (hden_two_dvd : den_two ∣ 2)
    (hden_two_pos : 0 < den_two)
    (h4 : 4 ∣ p * (den_odd * den_two)) : False := by
  have hden_odd : Odd den_odd := odd_of_dvd_odd hodd_q hden_odd_dvd
  have h2 : 2 ∣ p * (den_odd * den_two) := Nat.dvd_trans (by norm_num : 2 ∣ 4) h4
  have h2dt : 2 ∣ den_two := by
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact absurd h hodd_p.not_two_dvd_nat
    · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
      · exact absurd h' hden_odd.not_two_dvd_nat
      · exact h'
  have hdt_eq : den_two = 2 := by
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hden_two_dvd
    omega
  rw [hdt_eq] at h4
  -- 4 ∣ p * (den_odd * 2); rearrange to 2 * (p * den_odd) and cancel one 2
  have hre : p * (den_odd * 2) = 2 * (p * den_odd) := by ring
  rw [hre] at h4
  exact (hodd_p.mul hden_odd).not_two_dvd_nat
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h4)

/-! ### N = 1 core: single odd component -/

/-- Degenerate case: the decomposition is a single odd-prime component.
Cross equation: `num = p * den`; Step 2 kills `4 ∣ num`, and the cyclic
case gives `q - 1 = p * q`, impossible since `q ≤ p * q`. -/
lemma branch2_single_core (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hodd_p : Odd p) (hodd_q : Odd q) {n : ℕ} {f : Fin n → ℕ}
    (hf : Sorted f) (hpos : Pos f) (hn : 0 < n)
    (h_cross : (autRatio q f).num.natAbs = p * (autRatio q f).den) : False := by
  have hden_dvd : (autRatio q f).den ∣ q := den_autRatio_dvd hq hf hpos hn
  rcases odd_comp_num_cases hq hodd_q hf hpos hn with h4 | ⟨hnum, hdenq⟩
  · have h4' : 4 ∣ p * (autRatio q f).den := by rw [← h_cross]; exact h4
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp
      (Nat.dvd_trans (by norm_num : 2 ∣ 4) h4') with h | h
    · exact hodd_p.not_two_dvd_nat h
    · exact (odd_of_dvd_odd hodd_q hden_dvd).not_two_dvd_nat h
  · rw [hnum, hdenq] at h_cross
    -- h_cross : q - 1 = p * q; but q ≤ p * q
    have hp1 : 1 ≤ p := hp.one_lt.le
    have hq_le : q ≤ p * q := by
      have := Nat.mul_le_mul_right q hp1
      simpa [one_mul] using this
    have hq1 : 1 ≤ q := hq.pos
    omega

/-! ### N = 2 core: one odd component and one 2-group -/

/-- Paper lines 180-182, the heart of Branch 2.  Components: odd-prime group
with prime `q` (numerator `num₁`, denominator `den₁`) and 2-group
(numerator `num₂`, denominator `den₂`), cross equation
`num₁ * num₂ = p * (den₁ * den₂)`. -/
lemma branch2_pair_core (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hodd_p : Odd p) (hodd_q : Odd q)
    {n₁ n₂ : ℕ} {f₁ : Fin n₁ → ℕ} {f₂ : Fin n₂ → ℕ}
    (hs₁ : Sorted f₁) (hpos₁ : Pos f₁) (hn₁ : 0 < n₁)
    (hs₂ : Sorted f₂) (hpos₂ : Pos f₂) (hn₂ : 0 < n₂)
    (h_cross : (autRatio q f₁).num.natAbs * (autRatio 2 f₂).num.natAbs
      = p * ((autRatio q f₁).den * (autRatio 2 f₂).den)) : False := by
  have hden1_dvd : (autRatio q f₁).den ∣ q := den_autRatio_dvd hq hs₁ hpos₁ hn₁
  have hden2_dvd : (autRatio 2 f₂).den ∣ 2 :=
    den_autRatio_dvd Nat.prime_two hs₂ hpos₂ hn₂
  have hden2_pos : 0 < (autRatio 2 f₂).den := Rat.den_pos _
  rcases odd_comp_num_cases hq hodd_q hs₁ hpos₁ hn₁ with h4 | ⟨hnum, hdenq⟩
  · -- Step 2: 4 ∣ num₁ contradicts the cross equation
    have h4' : 4 ∣ (autRatio q f₁).num.natAbs * (autRatio 2 f₂).num.natAbs := by
      obtain ⟨k, hk⟩ := h4
      exact ⟨k * (autRatio 2 f₂).num.natAbs, by rw [hk]; ring⟩
    rw [h_cross] at h4'
    exact four_dvd_num_impossible p q hodd_p hodd_q hden1_dvd hden2_dvd
      hden2_pos h4'
  · -- Step 3: cyclic odd component, so den₁ = q and 2 ∣ num₁ = q - 1
    rw [hnum, hdenq] at h_cross
    -- h_cross : (q - 1) * num₂ = p * (q * den₂)
    have h2qm1 : 2 ∣ q - 1 := two_dvd_sub_one_of_odd hodd_q
    have h2 : 2 ∣ p * (q * (autRatio 2 f₂).den) := by
      rw [← h_cross]
      obtain ⟨k, hk⟩ := h2qm1
      rw [hk]
      exact ⟨k * (autRatio 2 f₂).num.natAbs, by ring⟩
    -- 2 ∣ p * q * den₂ with p, q odd forces 2 ∣ den₂; with den₂ ∣ 2: den₂ = 2
    have h2d2 : 2 ∣ (autRatio 2 f₂).den := by
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
      · exact absurd h hodd_p.not_two_dvd_nat
      · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
        · exact absurd h' hodd_q.not_two_dvd_nat
        · exact h'
    have hden2_eq : (autRatio 2 f₂).den = 2 := by
      have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hden2_dvd
      omega
    rw [hden2_eq] at h_cross
    -- h_cross : (q - 1) * num₂ = p * (q * 2)
    -- Step 4: the 2-group has num₂ ∈ {1, 3}
    rcases autRatio_two_num_of_den_two hs₂ hpos₂ hn₂ hden2_eq with hnum2 | hnum2
    · -- num₂ = 1: q - 1 = p * (q * 2), impossible since q ≤ p * (q * 2)
      rw [hnum2, Nat.mul_one] at h_cross
      have hp1 : 1 ≤ p := hp.one_lt.le
      have hq_le : q ≤ p * (q * 2) := by
        calc
          q = q * 1 := (mul_one q).symm
          _ ≤ q * (p * 2) := Nat.mul_le_mul_left q (by omega)
          _ = p * (q * 2) := by ring
      have hq1 : 1 ≤ q := hq.pos
      omega
    · -- num₂ = 3: q * 3 - 3 = p * (q * 2); p ≥ 3 gives 3 * q ≤ p * q,
      --   so 3 * (q - 1) < 3 * q ≤ p * q ≤ 2 * (p * q), contradiction.
      rw [hnum2, Nat.sub_mul, Nat.one_mul] at h_cross
      have hp3 : 3 ≤ p := prime_odd_ge_three hp hodd_p
      have hq3 : 3 ≤ q := prime_odd_ge_three hq hodd_q
      have h1 : 3 * q ≤ p * q := Nat.mul_le_mul_right q hp3
      have hqm : q ≤ q * 2 := Nat.le_mul_of_pos_right q (by norm_num)
      have h2le : p * q ≤ p * (q * 2) := Nat.mul_le_mul_left p hqm
      omega

/-! ### Shell -/

/-- Branch 2 of Theorem 3 (paper lines 176-182): assuming exactly one
odd-prime component (all others 2-groups), `TotalRatio = p` is impossible.

`N ≤ 2`: any index other than the odd one carries prime `2`, and
injectivity of `pp` allows at most one `2`-component.
- `N = 1`: `branch2_single_core`.
- `N = 2`: one odd and one 2-component, `branch2_pair_core` (both index
  orders, since the odd component may be `0` or `1`). -/
theorem thm3_branch_one_odd_component (pp : Fin N → ℕ) (nn : Fin N → ℕ)
    (ff : ∀ i, Fin (nn i) → ℕ)
    (hpp : ∀ i, (pp i).Prime) (hs : ∀ i, Sorted (ff i))
    (hpos : ∀ i, Pos (ff i)) (hN : ∀ i, 0 < nn i)
    (hd : Function.Injective pp) (p : ℕ) (hp : p.Prime)
    (hodd : Odd p)
    (h_single : ∃ j : Fin N, Odd (pp j) ∧ ∀ i, Odd (pp i) → i = j)
    (hEq : TotalRatio pp nn ff = (p : ℚ)) : False := by
  obtain ⟨j, hj_odd, hj_unique⟩ := h_single
  have h_others_two : ∀ k, k ≠ j → pp k = 2 := by
    intro k hk_ne
    rcases (Nat.Prime.eq_two_or_odd' (hpp k)) with (h | h)
    · exact h
    · exfalso; apply hk_ne; exact hj_unique k h
  have hN_le_2 : N ≤ 2 := by
    by_contra hNgt
    have h0 : 0 < N := by omega
    have h1 : 1 < N := by omega
    have h2 : 2 < N := by omega
    have h_exists_three : ∃ a b c : Fin N, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
      refine ⟨⟨0, h0⟩, ⟨1, h1⟩, ⟨2, h2⟩, ?_, ?_, ?_⟩
      · intro h; simpa using congrArg Fin.val h
      · intro h; simpa using congrArg Fin.val h
      · intro h; simpa using congrArg Fin.val h
    rcases h_exists_three with ⟨a, b, c, ha_ne_b, ha_ne_c, hb_ne_c⟩
    -- among three distinct indices, at least two differ from `j`
    have h_not_j : (a ≠ j ∧ b ≠ j) ∨ (a ≠ j ∧ c ≠ j) ∨ (b ≠ j ∧ c ≠ j) := by
      by_cases haj : a = j
      · subst haj; exact Or.inr (Or.inr ⟨ha_ne_b.symm, ha_ne_c.symm⟩)
      · by_cases hbj : b = j
        · subst hbj; exact Or.inr (Or.inl ⟨haj, Ne.symm hb_ne_c⟩)
        · exact Or.inl ⟨haj, hbj⟩
    rcases h_not_j with (⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩)
    · -- two non-j indices both carry prime 2: injectivity fails
      have hpa : pp a = 2 := h_others_two a ha
      have hpb : pp b = 2 := h_others_two b hb
      exact hd.ne ha_ne_b (by rw [hpa, hpb])
    · have hpa : pp a = 2 := h_others_two a ha
      have hpc : pp c = 2 := h_others_two c hc
      exact hd.ne ha_ne_c (by rw [hpa, hpc])
    · have hpb : pp b = 2 := h_others_two b hb
      have hpc : pp c = 2 := h_others_two c hc
      exact hd.ne hb_ne_c (by rw [hpb, hpc])
  have hN_cases : N = 0 ∨ N = 1 ∨ N = 2 := by omega
  rcases hN_cases with (hN0 | hN1 | hN2)
  · -- N = 0: empty product is 1, but p is a prime
    subst hN0
    have h_total : TotalRatio pp nn ff = (1 : ℚ) := by simp [TotalRatio]
    rw [h_total] at hEq
    exact hp.ne_one (by exact_mod_cast hEq.symm)
  · -- N = 1: the single component is the odd one
    subst hN1
    have hj0 : j = (0 : Fin 1) := Fin.ext (by have := j.2; omega)
    subst hj0
    have h_cross := totalRatio_eq_iff_cross pp nn ff hpp hs hpos hN p hp hEq
    rw [Fin.prod_univ_one, Fin.prod_univ_one] at h_cross
    exact branch2_single_core p (pp 0) hp (hpp 0) hodd hj_odd
      (hs 0) (hpos 0) (hN 0) h_cross
  · -- N = 2: one odd component, one 2-component; both index orders
    subst hN2
    have h_cross := totalRatio_eq_iff_cross pp nn ff hpp hs hpos hN p hp hEq
    rw [Fin.prod_univ_two, Fin.prod_univ_two] at h_cross
    have hj_cases : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by
      have := j.2; omega
    rcases hj_cases with (hj0 | hj1)
    · -- odd component at index 0, 2-group at index 1
      have hj0' : j = (0 : Fin 2) := Fin.ext hj0
      subst hj0'
      have hpp1 : pp 1 = 2 := h_others_two 1 (by decide)
      rw [hpp1] at h_cross
      exact branch2_pair_core p (pp 0) hp (hpp 0) hodd hj_odd
        (hs 0) (hpos 0) (hN 0) (hs 1) (hpos 1) (hN 1) h_cross
    · -- odd component at index 1, 2-group at index 0
      have hj1' : j = (1 : Fin 2) := Fin.ext hj1
      subst hj1'
      have hpp0 : pp 0 = 2 := h_others_two 0 (by decide)
      rw [hpp0] at h_cross
      rw [mul_comm ((autRatio 2 (ff 0)).num.natAbs)] at h_cross
      rw [mul_comm ((autRatio 2 (ff 0)).den)] at h_cross
      exact branch2_pair_core p (pp 1) hp (hpp 1) hodd hj_odd
        (hs 1) (hpos 1) (hN 1) (hs 0) (hpos 0) (hN 0) h_cross

end McCulloch26_2
