import McCulloch26_2.MultiPrime
import McCulloch26_2.PropClass
import McCulloch26_2.Basic

/-!
# Component-level contradiction `autRatio p f ≠ p` for odd `p`

Per-component lemma used in the proof of Theorem 3 (paper lines 176-182):
for an odd prime `p` and any finite abelian `p`-group, the ratio
`|Aut(G)|/|G|` cannot itself equal `p`.

## Paper reference

`/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex` lines 158-170
(statement of `prop: class` and its proof).

## Proof strategy

By `prop_class` we have a five-way disjunction on the value of
`autRatio p f`:

1. `n = 1`:  `autRatio p f = (p-1)/p < 1 < p` for `p ≥ 3`.
2. `n = 2`, `f = (1,1)`:  `autRatio p f = (p-1)^2 (p+1) / p > p`.
3. `n = 2`, `f = (1, e)` with `e > 1`:  `autRatio p f = (p-1)^2 > p`.
4. `n = 3`, `f = (1,1,1)`:  `autRatio p f = (p-1)^3 (p+1)(p^2+p+1) > p`.
5. else:  `autRatio p f = p (p-1)^2 * w` with `w ≥ 1`, so `≥ 4p > p`.

Each case uses `linarith` on the resulting ℚ inequality.
-/

namespace McCulloch26_2

open scoped Nat

variable {n : ℕ} {p : ℕ}

set_option maxHeartbeats 800000

/-! ### Polynomial inequalities for odd primes -/

/-- For odd prime `p ≥ 3`, `(p-1)² > p`. -/
lemma sq_lt_p (hp : p.Prime) (hodd : Odd p) :
    ((p - 1 : ℕ)^2 : ℕ) > p := by
  obtain ⟨k, hk⟩ := hodd
  -- p = 2k + 1, so (p - 1)² = (2k)² = 4k². We need 4k² > 2k + 1 for k ≥ 1.
  have hk1 : (1 : ℕ) ≤ k := by rw [hk] at hp; have := hp.two_le; omega
  have hpow_eq : ((2 * k + 1 - 1 : ℕ) ^ 2 : ℕ) = 4 * k * k := by
    rw [show (2 * k + 1 - 1 : ℕ) = 2 * k from by omega]
    rw [pow_two]; ring
  rw [hk, hpow_eq]
  -- 4 k k > 2 k + 1 for k ≥ 1
  nlinarith [sq_nonneg (k : ℕ), sq_nonneg (k - 1), hk1]

/-- For odd prime `p ≥ 3`, `(p-1)² (p+1) > p²`. -/
lemma sq_pm1_gt_sq (hp : p.Prime) (hodd : Odd p) :
    ((p - 1 : ℕ)^2 * (p + 1) : ℕ) > p * p := by
  obtain ⟨k, hk⟩ := hodd
  have hk1 : (1 : ℕ) ≤ k := by rw [hk] at hp; have := hp.two_le; omega
  have hpow_eq : ((2 * k + 1 - 1 : ℕ) ^ 2 : ℕ) = 4 * k * k := by
    rw [show (2 * k + 1 - 1 : ℕ) = 2 * k from by omega]
    rw [pow_two]; ring
  have hsum_eq : ((2 * k + 1 : ℕ) + 1 : ℕ) = 2 * (k + 1) := by ring
  rw [hk, hpow_eq, hsum_eq]
  -- 4 * k * k * (2 * (k + 1)) > (2 * k + 1) * (2 * k + 1)
  nlinarith [sq_nonneg (k : ℕ), sq_nonneg (k - 1), sq_nonneg ((k + 1 : ℕ)), hk1]

/-- For odd prime `p ≥ 3`, `(p-1)³ (p+1)(p²+p+1) > p`. -/
lemma cube_pm1_gt_p (hp : p.Prime) (hodd : Odd p) :
    ((p - 1 : ℕ)^3 * (p + 1) * (p ^ 2 + p + 1) : ℕ) > p := by
  obtain ⟨k, hk⟩ := hodd
  have hk1 : (1 : ℕ) ≤ k := by rw [hk] at hp; have := hp.two_le; omega
  -- We use a coarse bound: each factor is ≥ 1 (in fact ≥ 2 for k ≥ 1),
  -- so LHS ≥ 8 * 1 * 4 * 7 = 224 > 2k+1 for all k.
  have hpow_eq : ((2 * k + 1 - 1 : ℕ) ^ 3 : ℕ) = 8 * k ^ 3 := by
    rw [show (2 * k + 1 - 1 : ℕ) = 2 * k from by omega]
    ring
  have hsum_eq : ((2 * k + 1 : ℕ) + 1 : ℕ) = 2 * (k + 1) := by ring
  rw [hk, hpow_eq, hsum_eq]
  -- Goal: 8 * k³ * 2(k+1) * ((2k+1)² + (2k+1) + 1) > 2k + 1
  -- For k = 1: 8 * 1 * 4 * 13 = 416 > 3 ✓
  -- For k ≥ 2: each factor ≥ k, so LHS ≥ 8k³ * 2k * k² ≥ 16k^6 ≥ 16 * 64 = 1024 > 2k+1.
  rcases Nat.eq_or_lt_of_le hk1 with hk1' | hk1'
  · -- k = 1
    subst hk1'
    norm_num
  · -- k ≥ 2: 16k^6 ≥ 16*64 = 1024 > 2k+1
    have h1 : (2 : ℕ) ≤ k := hk1'
    -- Factor: 8 k³ · 2(k+1) · X = 16 k³ (k+1) X, with X = (2k+1)² + (2k+1) + 1 ≥ k² for k ≥ 2
    have hX : (2 * k + 1 : ℕ) ^ 2 + (2 * k + 1) + 1 ≥ k ^ 2 := by
      nlinarith [sq_nonneg (k : ℕ), sq_nonneg (k - 1), h1]
    -- 16 k³ (k+1) X ≥ 16 k³ · k³ = 16 k^6 (using (k+1) X ≥ k³).
    have hk_le_kk1 : k ≤ k + 1 := Nat.le_succ _
    have hkX : (k + 1 : ℕ) * ((2 * k + 1) ^ 2 + (2 * k + 1) + 1) ≥ k ^ 3 := by
      have h1' : k * k ^ 2 = k ^ 3 := by ring
      nlinarith [sq_nonneg (k : ℕ), hX, hk_le_kk1, h1']
    have hkey : 16 * k ^ 6 ≤ 8 * k ^ 3 * (2 * (k + 1)) *
        ((2 * k + 1) ^ 2 + (2 * k + 1) + 1) := by
      -- Equivalent to k^6 ≤ k^3 (k+1) X. Since k^6 = k^3 * k^3 and (k+1) X ≥ k^3,
      -- we have k^3 * (k+1) X ≥ k^3 * k^3 = k^6. Use Nat.mul_le_mul_left.
      rw [show 8 * k ^ 3 * (2 * (k + 1)) *
          ((2 * k + 1) ^ 2 + (2 * k + 1) + 1) =
          16 * (k ^ 3 * ((k + 1) * ((2 * k + 1) ^ 2 + (2 * k + 1) + 1))) from by ring]
      rw [show k ^ 6 = k ^ 3 * k ^ 3 from by rw [← pow_add]]
      -- Goal: 16 * k^3 * Y ≥ 16 * k^3 * k^3, with Y = (k+1) * X ≥ k^3.
      have hmul : k ^ 3 * k ^ 3 ≤ k ^ 3 * ((k + 1) *
          ((2 * k + 1) ^ 2 + (2 * k + 1) + 1)) :=
        Nat.mul_le_mul_left _ hkX
      linarith
    have h5 : (2 * k + 1 : ℕ) ≤ 16 * k ^ 6 := by
      nlinarith [pow_two (k : ℕ), h1]
    omega

/-! ### Case lemmas -/

/-- **Case 1**: `n = 1`. `autRatio p f = (p-1)/p < 1 < p` for `p ≥ 3`. -/
lemma comp_ne_odd_case1 (hp : p.Prime) (f : Fin 1 → ℕ) (hpos : Pos f)
    (_hodd : Odd p) : autRatio p f ≠ (p : ℚ) := by
  intro h_eq
  have hr : autRatio p f = ((p - 1 : ℕ) : ℚ) / (p : ℚ) := ratio_case_cyclic hp hpos
  rw [hr] at h_eq
  -- (p-1)/p = p in ℚ, but (p-1)/p < 1 < p (since 0 < p-1 < p for p ≥ 3).
  have hlt1 : ((p - 1 : ℕ) : ℚ) < (p : ℚ) := by
    rw [Nat.cast_sub hp.one_lt.le]
    simp
  have hp_pos : (0 : ℚ) < (p : ℚ) := Nat.cast_pos.mpr hp.pos
  have hlt2 : ((p - 1 : ℕ) : ℚ) / (p : ℚ) < (1 : ℚ) := by
    rw [div_lt_one₀]
    · exact hlt1
    · exact hp_pos
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
  linarith

/-- **Case 2**: `n = 2`, `f = (1,1)`. `autRatio p f = (p-1)^2 (p+1) / p > p`. -/
lemma comp_ne_odd_case2 (hp : p.Prime) (f : Fin 2 → ℕ)
    (hv : f 0 = 1 ∧ f 1 = 1) (hodd : Odd p) :
    autRatio p f ≠ (p : ℚ) := by
  intro h_eq
  have hr : autRatio p f = (((p - 1) ^ 2 * (p + 1) : ℕ) : ℚ) / (p : ℚ) :=
    ratio_case_two_const hp hv
  rw [hr] at h_eq
  -- (p-1)²(p+1)/p = p. But (p-1)²(p+1) > p², so LHS > p²/p = p. Contradiction.
  have hgt : (((p - 1) ^ 2 * (p + 1) : ℕ) : ℚ) > (p * p : ℕ) := by
    rw [Nat.cast_mul]
    exact_mod_cast sq_pm1_gt_sq hp hodd
  have hp_pos : (0 : ℚ) < (p : ℚ) := Nat.cast_pos.mpr hp.pos
  -- LHS / p > p² / p = p. We want ↑p < ((p-1)²(p+1))/↑p, equivalent to ↑p * ↑p < ((p-1)²(p+1))
  -- After `lt_div_iff₀` we have ↑p * ↑p < ↑((p-1)²(p+1)). Use hgt directly:
  have hkey : (p : ℚ) < (((p - 1) ^ 2 * (p + 1) : ℕ) : ℚ) / (p : ℚ) := by
    rw [lt_div_iff₀ hp_pos]
    have : ((p * p : ℕ) : ℚ) = ↑p * ↑p := by rw [Nat.cast_mul]
    linarith [hgt, this]
  linarith

/-- **Case 3**: `n = 2`, `f = (1, e)` with `e > 1`. `autRatio p f = (p-1)^2 > p`. -/
lemma comp_ne_odd_case3 (hp : p.Prime) (f : Fin 2 → ℕ)
    (h0 : f 0 = 1) (h1 : 1 < f 1) (hodd : Odd p) :
    autRatio p f ≠ (p : ℚ) := by
  intro h_eq
  have hr : autRatio p f = (((p - 1) ^ 2 : ℕ) : ℚ) := ratio_case_two_dist hp h0 h1
  rw [hr] at h_eq
  have hcontra : (((p - 1) ^ 2 : ℕ) : ℚ) > (p : ℚ) := by
    exact_mod_cast sq_lt_p hp hodd
  linarith

/-- **Case 4**: `n = 3`, `f = (1,1,1)`. `autRatio p f` is a positive integer
strictly larger than `p`. -/
lemma comp_ne_odd_case4 (hp : p.Prime) (f : Fin 3 → ℕ)
    (hall : ∀ i, f i = 1) (hodd : Odd p) :
    autRatio p f ≠ (p : ℚ) := by
  intro h_eq
  have hr : autRatio p f = (((p - 1) ^ 3 * (p + 1) * (p ^ 2 + p + 1) : ℕ) : ℚ) :=
    ratio_case_three_const hp hall
  rw [hr] at h_eq
  have hcontra : (((p - 1) ^ 3 * (p + 1) * (p ^ 2 + p + 1) : ℕ) : ℚ) > (p : ℚ) := by
    exact_mod_cast cube_pm1_gt_p hp hodd
  linarith

/-- **Case 5**: else-branch of `prop_class`. `autRatio p f = (p-1)^2 * p * w`
with `w ≥ 1`, so `autRatio p f ≥ 4p > p`. -/
lemma comp_ne_odd_case5 (hp : p.Prime) {f : Fin n → ℕ}
    (_hf : Sorted f) (_hpos : Pos f) (_hn : 0 < n)
    (hcase : p ^ ((∑ i : Fin n, f i) + 1) * (p - 1) ^ 2 ∣ AutFormula p f)
    (hodd : Odd p) :
    autRatio p f ≠ (p : ℚ) := by
  intro h_eq
  obtain ⟨w, hw⟩ := hcase
  -- AutFormula = p^(sum+1) * (p-1)^2 * w; autRatio = ((p-1)² * p * w) / p^(sum)
  -- after division: autRatio = (p-1)² * p * w / p^(sum) = (p-1)² * w when... wait
  -- the cleaner form: autRatio = ((p-1)² * p * w : ℕ) / p^sum, then divide by p gives w * (p-1)²
  -- Actually: hw says AutFormula = p^(sum+1) * (p-1)^2 * w. So AutFormula / p^sum = p * (p-1)^2 * w.
  have hrepr : autRatio p f = (((p - 1) ^ 2 * p * w : ℕ) : ℚ) := by
    unfold autRatio GroupCard
    rw [hw, Nat.pow_succ']
    have hdz : (((p ^ (∑ i : Fin n, f i) : ℕ) : ℚ)) ≠ 0 := by
      have : (p ^ (∑ i : Fin n, f i) : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
      exact_mod_cast this
    rw [div_eq_iff hdz]
    push_cast
    ring
  rw [hrepr] at h_eq
  -- Now h_eq : ((p-1)² * p * w : ℕ) = p  in ℚ.  Both sides are ℕ-coerced.
  -- LHS ≥ 4 * 1 * 1 = 4 for p ≥ 3 (since (p-1)² ≥ 4) and w ≥ 1.
  -- RHS = p ≥ 3. So LHS > RHS, contradiction.
  have hw_pos : w ≥ 1 := by
    by_contra hw0
    push_neg at hw0
    interval_cases w
    -- After interval_cases w = 0, hw is `AutFormula p f = p^(sum+1) * (p-1)^2 * 0`
    -- Show AutFormula p f > 0, then rw hw to get 0 = 0 < ... but contradiction since 0 < ... 0 = 0
    have hAF_pos : 0 < AutFormula p f := by
      unfold AutFormula ProdOne ProdTwo ProdThree
      have hp_pos : 0 < p := hp.pos
      have hP1 : 0 < ProdOne p f := by
        unfold ProdOne
        apply Finset.prod_pos
        intro k _
        have hgt : (k : ℕ) < (BlockTop f k).val + 1 := by
          have := Fin.le_iff_val_le_val.mp (le_block_top f (rfl : f k = f k))
          omega
        have hpow_pos : 0 < p ^ (k : ℕ) := pow_pos hp_pos _
        have hkey : p ^ (k : ℕ) < p ^ ((BlockTop f k).val + 1) := by
          exact Nat.pow_lt_pow_right hp.two_le hgt
        exact Nat.sub_pos_of_lt hkey
      have hP2 : 0 < ProdTwo p f := by
        unfold ProdTwo
        apply Finset.prod_pos
        intro k _
        exact pow_pos hp_pos _
      have hP3 : 0 < ProdThree p f := by
        unfold ProdThree
        apply Finset.prod_pos
        intro k _
        -- p^anything is positive (even when f k = 1 and exponent is 0)
        exact pow_pos hp_pos _
      exact Nat.mul_pos (Nat.mul_pos hP1 hP2) hP3
    rw [hw] at hAF_pos
    simp at hAF_pos
  have hp3 : p ≥ 3 := by
    rcases hodd with ⟨k, hk⟩
    rw [hk]
    have hk1 : 1 ≤ k := by rw [hk] at hp; have := hp.two_le; omega
    omega
  -- LHS = (p-1)² * p * w ≥ 4 * 3 * 1 = 12 > p for p ≥ 3.
  -- The contradiction comes from h_eq + this inequality.
  have hp4 : (4 : ℕ) ≤ (p - 1 : ℕ) ^ 2 := by
    rcases hodd with ⟨k, hk⟩
    rw [hk]
    have hk1 : 1 ≤ k := by rw [hk] at hp; have := hp.two_le; omega
    rw [show (2 * k + 1 - 1 : ℕ) = 2 * k from by omega, pow_two]
    -- 4 ≤ (2k)² = 4k² for k ≥ 1
    nlinarith [sq_nonneg (k : ℕ), hk1]
  have hcontra : ((p - 1 : ℕ)^2 * p * w : ℕ) > p := by
    -- (p-1)² ≥ 4 and 4p > p. So (p-1)² * p ≥ 4p > p. Then w ≥ 1 gives ≥.
    have h4p : (4 : ℕ) * p > p := by nlinarith [hp3]
    have h4p_pos : (0 : ℕ) < 4 * p := by positivity
    have hp_4p : ((p - 1 : ℕ)^2 * p : ℕ) ≥ 4 * p :=
      Nat.mul_le_mul_right _ hp4
    have hp_4p_gt : ((p - 1 : ℕ)^2 * p : ℕ) > p := by
      linarith [hp_4p, h4p]
    -- (p-1)² * p * w ≥ (p-1)² * p > p (since w ≥ 1).
    exact lt_of_lt_of_le hp_4p_gt (Nat.le_mul_of_pos_right _ hw_pos)
  -- h_eq : ↑((p-1)² * p * w) = ↑p. Use Nat.cast_injective to get Nat equality.
  have h_eq_nat : ((p - 1 : ℕ)^2 * p * w : ℕ) = p := by
    exact_mod_cast h_eq
  omega

/-! ### Assembly -/

/-- The complete component-level lemma: for odd `p` and any sorted
positive exponent sequence `f`, the per-component ratio cannot equal `p`. -/
theorem component_ne_odd_prime (hp : p.Prime) {f : Fin n → ℕ}
    (hpos : Pos f) (hs : Sorted f) (hn : 0 < n) (hodd : Odd p) :
    autRatio p f ≠ (p : ℚ) := by
  intro h_eq
  rcases prop_class hp hs hpos hn with
    ⟨hn1, hr⟩ | ⟨hn2, hall, hr⟩ | ⟨hn2', hf0, hnotall, hr⟩ | ⟨hn3, hall, hr⟩ | hd
  · -- Case 1: n = 1
    subst hn1
    exact (comp_ne_odd_case1 hp f hpos hodd) h_eq
  · -- Case 2: n = 2, f = (1,1)
    subst hn2
    have hv01 : f 0 = 1 ∧ f 1 = 1 := ⟨hall 0, hall 1⟩
    exact (comp_ne_odd_case2 hp f hv01 hodd) h_eq
  · -- Case 3: n = 2, f 0 = 1, ¬(∀ i, f i = 1), autRatio = (p-1)^2
    subst hn2'
    have hf0' : f 0 = 1 := by
      have h0_eq : (⟨0, hn⟩ : Fin 2) = 0 := by
        apply Fin.ext; simp
      rw [h0_eq] at hf0; exact hf0
    have hf1_gt : 1 < f 1 := by
      have hf1_ne : f 1 ≠ 1 := by
        intro hf1eq
        apply hnotall
        intro i
        fin_cases i
        · exact hf0'
        · exact hf1eq
      have hf0_le : f 0 ≤ f 1 := by
        show f 0 ≤ f 1
        exact hs (0 : Fin 2) 1 (by norm_num)
      omega
    exact (comp_ne_odd_case3 hp f hf0' hf1_gt hodd) h_eq
  · -- Case 4: n = 3, f = (1,1,1)
    subst hn3
    exact (comp_ne_odd_case4 hp f hall hodd) h_eq
  · -- Case 5: else
    exact (comp_ne_odd_case5 hp hs hpos hn hd hodd) h_eq
