import McCulloch26_2.Formula

/-!
# Proposition 2.4 (`prop: class`) of McCulloch26-2

The dichotomy for the ratio `|Aut(G)|/|G|` of a finite abelian `p`-group:
either one of the four exceptional shapes holds with an explicit rational
value (items (1)-(4)), or else the whole numerator carries the factor
`p^{a+1} * (p-1)^2`, where `a` is the exponent sum — which says exactly that
the ratio is an integral multiple of `p * (p-1)^2`.

## References

Source: /home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 155-170
(statement `prop: class`, items (1)-(4), dichotomy sentence; the proof lines
166-170 is transcribed by `prop_class_else`).
-/

namespace McCulloch26_2

variable {n : ℕ} {p : ℕ}

/-! ### Decomposition separating the power of `p` -/

/-- The first product is the power `p^{Σk}` times its unit part. -/
theorem prodOne_eq (p : ℕ) (f : Fin n → ℕ) :
    ProdOne p f
      = p ^ (∑ k : Fin n, (k : ℕ))
        * ∏ k : Fin n, (p ^ ((BlockTop f k).val + 1 - (k : ℕ)) - 1) := by
  have hfac : ∀ k : Fin n, (p ^ ((BlockTop f k).val + 1) - p ^ (k : ℕ))
      = p ^ (k : ℕ) * (p ^ ((BlockTop f k).val + 1 - (k : ℕ)) - 1) := fun k => by
    conv_lhs =>
      rw [← Nat.pow_sub_mul_pow p
        (le_trans (coe_le_block_top f k) (Nat.le_succ _))]
    rw [Nat.mul_sub, Nat.mul_one,
      mul_comm (p ^ ((BlockTop f k).val + 1 - (k : ℕ))) (p ^ (k : ℕ))]
  unfold ProdOne
  refine Eq.trans (Finset.prod_congr rfl fun k _ => hfac k) ?_
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- The second product is exactly a power of `p`. -/
theorem prodTwo_eq (p : ℕ) (f : Fin n → ℕ) :
    ProdTwo p f = p ^ (∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val)) := by
  unfold ProdTwo
  rw [← Finset.prod_pow_eq_pow_sum]

/-- The third product is exactly a power of `p`. -/
theorem prodThree_eq (p : ℕ) (f : Fin n → ℕ) :
    ProdThree p f = p ^ (∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val)) := by
  unfold ProdThree
  rw [← Finset.prod_pow_eq_pow_sum]

/-- Full decomposition of the formula into a single power of `p` times a unit
factor; the exponent is exactly the right side of Proposition `prop: dc`
(paper lines 149-153). -/
theorem autFormula_eq_pow_mul (p : ℕ) (f : Fin n → ℕ) :
    AutFormula p f
      = p ^ ((∑ k : Fin n, (k : ℕ))
              + (∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val))
              + (∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val)))
        * ∏ k : Fin n, (p ^ ((BlockTop f k).val + 1 - (k : ℕ)) - 1) := by
  unfold AutFormula
  rw [prodOne_eq p f, prodTwo_eq p f, prodThree_eq p f]
  calc ((p ^ (∑ k : Fin n, (k : ℕ))
            * ∏ k : Fin n, (p ^ ((BlockTop f k).val + 1 - (k : ℕ)) - 1))
          * p ^ (∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val)))
        * p ^ (∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val))
      = ((p ^ (∑ k : Fin n, (k : ℕ)) * p ^ (∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val)))
            * p ^ (∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val)))
          * ∏ k : Fin n, (p ^ ((BlockTop f k).val + 1 - (k : ℕ)) - 1) := by ring
    _ = (p ^ (∑ k : Fin n, (k : ℕ)
              + (∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val)))
            * p ^ (∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val)))
          * ∏ k : Fin n, (p ^ ((BlockTop f k).val + 1 - (k : ℕ)) - 1) := by
          rw [← Nat.pow_add]
    _ = (p ^ ((∑ k : Fin n, (k : ℕ)
                + (∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val)))
              + (∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val))))
          * ∏ k : Fin n, (p ^ ((BlockTop f k).val + 1 - (k : ℕ)) - 1) := by
          rw [← Nat.pow_add]

/-! ### Small arithmetic helpers -/

theorem nat_coprime_pred_self {a : ℕ} (ha : 1 < a) : Nat.Coprime (a - 1) a := by
  refine Nat.coprime_iff_gcd_eq_one.mpr ?_
  have h1 : Nat.gcd (a - 1) a ∣ a - 1 := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (a - 1) a ∣ a := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd (a - 1) a ∣ 1 := by
    have hle : (1 : ℕ) ≤ a := le_of_lt ha
    have hd : Nat.gcd (a - 1) a ∣ a - (a - 1) := Nat.dvd_sub h2 h1
    rwa [show a - (a - 1) = 1 from by omega] at hd
  exact Nat.dvd_one.mp h3

/-- A positive natural raised to any power stays at least `1`. -/
theorem one_le_pow' {a : ℕ} (h : 0 < a) (k : ℕ) : 1 ≤ a ^ k :=
  Nat.succ_le_of_lt (pow_pos h k)

/-- A positive natural divides its positive powers. -/
theorem self_le_pow {a : ℕ} (h : 0 < a) (k : ℕ) (hk : 0 < k) : a ≤ a ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.pow_succ']
  exact Nat.le_mul_of_pos_right _ (pow_pos h j)

/-! ### Rational representation helpers -/

/-- Cross-multiplication and denominator divisibility against a natural
fraction. -/
theorem rat_cross {q : ℚ} {a b : ℕ} (hb0 : 0 < b) (h : q = (a : ℚ) / b) :
    q.num * b = a * q.den ∧ q.den ∣ b := by
  have hne : ((b : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hb0.ne'
  obtain ⟨c, hc1, hc2⟩ :=
    Rat.exists_eq_mul_div_num_and_eq_mul_div_den ((a : ℕ) : ℤ) hne
  have hq : ((a : ℕ) : ℤ) / ((b : ℕ) : ℤ) = ((a : ℕ) : ℚ) / ((b : ℕ) : ℚ) := rfl
  rw [hq] at hc1 hc2
  rw [← h] at hc1 hc2
  have hdenpos : (0 : ℤ) < ((q.den : ℕ) : ℤ) := by exact_mod_cast q.den_pos
  have hc0 : (0 : ℤ) ≤ c := by nlinarith [hc2, hdenpos]
  refine ⟨?_, ?_⟩
  · have e2 : ((q.num : ℤ)) * (((b : ℕ) : ℤ))
        = (((a : ℕ) : ℤ)) * (((q.den : ℕ) : ℤ)) := by
      rw [hc2]
      calc ((q.num : ℤ)) * (c * ((q.den : ℕ) : ℤ))
          = (c * ((q.num : ℤ))) * ((q.den : ℕ) : ℤ) := by ring
        _ = (((a : ℕ) : ℤ)) * ((q.den : ℕ) : ℤ) := by rw [← hc1]
    exact e2
  · refine Dvd.intro c.toNat ?_
    refine Nat.cast_injective (R := ℤ) ?_
    rw [Nat.cast_mul]
    calc ((q.den : ℕ) : ℤ) * ((c.toNat : ℕ) : ℤ) = ((b : ℕ) : ℤ) := by
          rw [Int.toNat_of_nonneg hc0, mul_comm]
          exact hc2.symm

/-- Coprimality transfer for the reduced-denominator corollaries: if the
cross-multiplication equation $q = N / p$ holds and $(p - 1) \\mid N$, then
$(p - 1)$ divides the numerator of $q$. Used for items (1)-(2) of
Proposition `prop: class` (paper lines 158-159). -/
theorem cop_dvd_num_of_cross {p : ℕ} (hp : 1 < p) {q : ℚ} {N : ℕ}
    (hcross : (q.num : ℤ) * ((p : ℕ) : ℤ)
        = ((N : ℕ) : ℤ) * ((q.den : ℕ) : ℤ))
    (hdN : (p - 1 : ℕ) ∣ N) :
    ((p - 1 : ℕ) : ℤ) ∣ q.num := by
  have hcop : Nat.Coprime (p - 1) p := nat_coprime_pred_self hp
  obtain ⟨s, hs⟩ := hdN
  have h1 : ((q.num : ℤ) * ((p : ℕ) : ℤ)).natAbs = q.num.natAbs * p := by
    rw [Int.natAbs_mul]; simp
  have h2 : (((N : ℕ) : ℤ) * ((q.den : ℕ) : ℤ)).natAbs = N * q.den := by
    rw [Int.natAbs_mul]; simp
  have heq : q.num.natAbs * p = N * q.den := by rw [← h1, ← h2, hcross]
  have hkey : p * q.num.natAbs = (p - 1) * (s * q.den) := by
    calc p * q.num.natAbs = q.num.natAbs * p := mul_comm _ _
      _ = N * q.den := heq
      _ = (p - 1) * (s * q.den) := by rw [hs]; ring
  have hdvdN : (p - 1) ∣ q.num.natAbs :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop ⟨s * q.den, hkey⟩
  rcases Int.eq_nat_or_neg q.num with ⟨k, hk | hk⟩
  · rw [hk] at hdvdN ⊢
    exact Int.natCast_dvd_natCast.mpr hdvdN
  · rw [hk] at hdvdN ⊢
    rw [Int.natAbs_neg] at hdvdN
    rw [Int.dvd_neg]
    exact Int.natCast_dvd_natCast.mpr hdvdN

/-- A rational represented by a natural number has numerator that number and
denominator `1`. -/
theorem num_den_of_repr_nat {q : ℚ} {m : ℕ} (h : q = (m : ℚ)) :
    q.num = ((m : ℕ) : ℤ) ∧ q.den = 1 := by
  subst h
  exact ⟨Rat.num_intCast _, Rat.den_intCast _⟩

/-! ### Case computations for the exceptional shapes -/

/-- Item (1) of Proposition `prop: class` (paper line 158; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 155-164):
for a cyclic group (`n = 1`) the ratio is `(p-1)/p`. -/
theorem ratio_case_cyclic (hp : p.Prime) {f : Fin 1 → ℕ} (hpos : Pos f) :
    autRatio p f = ((p - 1 : ℕ) : ℚ) / (p : ℚ) := by
  have bt0 : BlockTop f 0 = 0 :=
    block_top_eq_self f 0 fun s hs => absurd s.isLt (by have := s.isLt; omega)
  have bb0 : BlockBot f 0 = 0 :=
    block_bot_eq_self f 0 fun s hs => absurd s.isLt (by have := s.isLt; omega)
  have hp1 : 1 ≤ f 0 := hpos ⟨0, by norm_num⟩
  have hAF : AutFormula p f = (p - 1) * p ^ (f 0 - 1) := by
    unfold AutFormula ProdOne ProdTwo ProdThree
    simp only [Fin.prod_univ_one, bt0, bb0]
    norm_num [Fin.val_zero]
  have hGC : GroupCard p f = p ^ f 0 := by
    unfold GroupCard
    rw [Fin.sum_univ_one]
  unfold autRatio
  rw [hAF, hGC]
  have hpow : (p ^ (f 0) : ℕ) = p * p ^ (f 0 - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hp1]
    rw [pow_add, pow_one, mul_comm]
  have hden : ((p ^ f 0 : ℕ) : ℚ) ≠ 0 := by
    have : (p ^ f 0 : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
    exact_mod_cast this
  have hpz : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [div_eq_div_iff hden hpz, hpow]
  push_cast
  ring

/-- Item (2) of Proposition `prop: class` (paper line 159): for
`Z_p × Z_p` the ratio is `(p-1)^2 (p+1)/p`. -/
theorem ratio_case_two_const (hp : p.Prime) {f : Fin 2 → ℕ}
    (hv : f 0 = 1 ∧ f 1 = 1) :
    autRatio p f = (((p - 1) ^ 2 * (p + 1) : ℕ) : ℚ) / (p : ℚ) := by
  have hall : ∀ s : Fin 2, f s = 1 := fun s => by
    fin_cases s <;> simp [hv.1, hv.2]
  have btv : ∀ k : Fin 2, (BlockTop f k).val = 1 :=
    fun k => block_top_pair_const_val hall k
  have bbv : ∀ k : Fin 2, (BlockBot f k).val = 0 :=
    fun k => block_bot_pair_const_val hall k
  have hAF : AutFormula p f = (p ^ 2 - 1) * (p ^ 2 - p) := by
    unfold AutFormula ProdOne ProdTwo ProdThree
    simp only [Fin.prod_univ_two, btv 0, btv 1, bbv 0, bbv 1, hall]
    norm_num [Fin.val_one, pow_zero]
  have hGC : GroupCard p f = p ^ 2 := by
    unfold GroupCard
    rw [Fin.sum_univ_two]
    simp only [hall]
  have hconv : (p ^ 2 - 1) * (p ^ 2 - p) = (p - 1) * (p + 1) * ((p - 1) * p) := by
    have h1 : (1 : ℕ) ≤ p := hp.one_lt.le
    have h12 : (1 : ℕ) ≤ p ^ 2 := one_le_pow' hp.pos 2
    have hp2l : (p : ℕ) ≤ p ^ 2 := self_le_pow hp.pos 2 (by omega)
    have h : (((p ^ 2 - 1 : ℕ) : ℤ)) * (((p ^ 2 - p : ℕ) : ℤ))
        = (((p - 1 : ℕ) : ℤ)) * (((p + 1 : ℕ) : ℤ))
            * (((p - 1 : ℕ) : ℤ) * ((p : ℕ) : ℤ)) := by
      have e1 : (((p ^ 2 - 1 : ℕ) : ℤ)) = ((p : ℕ) : ℤ) ^ 2 - 1 := by
        rw [Nat.cast_sub h12, Nat.cast_pow, Nat.cast_one]
      have e2 : (((p ^ 2 - p : ℕ) : ℤ)) = ((p : ℕ) : ℤ) ^ 2 - ((p : ℕ) : ℤ) := by
        rw [Nat.cast_sub hp2l, Nat.cast_pow]
      have e3 : (((p - 1 : ℕ) : ℤ)) = ((p : ℕ) : ℤ) - 1 := by
        rw [Nat.cast_sub h1, Nat.cast_one]
      have e4 : (((p + 1 : ℕ) : ℤ)) = ((p : ℕ) : ℤ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [e1, e2, e3, e4]
      ring
    exact_mod_cast h
  unfold autRatio
  rw [hAF, hGC]
  have hd2 : ((p ^ 2 : ℕ) : ℚ) ≠ 0 := by
    have : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hp.ne_zero
    exact_mod_cast this
  have hpz : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [div_eq_div_iff hd2 hpz, hconv]
  push_cast
  ring

/-- Item (3) of Proposition `prop: class` (paper line 160): for
`Z_p × Z_{p^v}` with `v > 1` the ratio is `(p-1)^2`. -/
theorem ratio_case_two_dist (hp : p.Prime) {f : Fin 2 → ℕ} (h0 : f 0 = 1)
    (h1 : 1 < f 1) :
    autRatio p f = (((p - 1) ^ 2 : ℕ) : ℚ) := by
  have bt0 : BlockTop f 0 = 0 := by
    refine block_top_eq_self f 0 ?_
    intro s hs
    fin_cases s
    · simp at hs
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hs ⊢
      have e0 : f ⟨0, by norm_num⟩ = f 0 := rfl
      have e1 : f ⟨1, by norm_num⟩ = f 1 := rfl
      omega
  have bt1 : BlockTop f 1 = 1 :=
    block_top_eq_self f 1 fun s hs => absurd hs (by have := s.isLt; omega)
  have bb0 : BlockBot f 0 = 0 :=
    block_bot_eq_self f 0 fun s hs => absurd hs (by have := s.isLt; omega)
  have bb1 : BlockBot f 1 = 1 := by
    refine block_bot_eq_self f 1 ?_
    intro s hs
    fin_cases s
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hs ⊢
      have e0 : f ⟨0, by norm_num⟩ = f 0 := rfl
      have e1 : f ⟨1, by norm_num⟩ = f 1 := rfl
      omega
    · simp at hs
  have hAF : AutFormula p f
      = (p - 1) * (p ^ 2 - p) * p * p ^ (f 1 - 1) := by
    unfold AutFormula ProdOne ProdTwo ProdThree
    simp only [Fin.prod_univ_two, bt0, bt1, bb0, bb1, h0]
    norm_num [Fin.val_zero, Fin.val_one, pow_zero]
  have hGC : GroupCard p f = p ^ (1 + f 1) := by
    unfold GroupCard
    rw [Fin.sum_univ_two, h0]
  have hpow1 : (p ^ (1 + f 1) : ℕ) = p * p ^ f 1 := by rw [pow_add, pow_one]
  have hpow2 : (p ^ f 1 : ℕ) = p * p ^ (f 1 - 1) := by
    obtain ⟨b, hb⟩ : ∃ b, f 1 = b + 1 := ⟨f 1 - 1, by omega⟩
    have hmain : ∀ m : ℕ, p ^ (m + 1) = p * p ^ m := fun m => by
      rw [pow_succ']
    rw [hb, hmain, Nat.add_sub_cancel, mul_comm]
  have hconv : (p - 1) * (p ^ 2 - p) * p * p ^ (f 1 - 1)
      = (p - 1) * ((p - 1) * p) * p * p ^ (f 1 - 1) := by
    have h1' : (1 : ℕ) ≤ p := hp.one_lt.le
    have hp2l : (p : ℕ) ≤ p ^ 2 := self_le_pow hp.pos 2 (by omega)
    have h : (((p - 1 : ℕ) : ℤ)) * (((p ^ 2 - p : ℕ) : ℤ)) * ((p : ℕ) : ℤ)
          * ((p ^ (f 1 - 1) : ℕ) : ℤ)
        = (((p - 1 : ℕ) : ℤ)) * ((((p - 1 : ℕ) : ℤ)) * ((p : ℕ) : ℤ))
            * ((p : ℕ) : ℤ) * ((p ^ (f 1 - 1) : ℕ) : ℤ) := by
      have e1 : (((p - 1 : ℕ) : ℤ)) = ((p : ℕ) : ℤ) - 1 := by
        rw [Nat.cast_sub h1', Nat.cast_one]
      have e2 : (((p ^ 2 - p : ℕ) : ℤ)) = ((p : ℕ) : ℤ) ^ 2 - ((p : ℕ) : ℤ) := by
        rw [Nat.cast_sub hp2l, Nat.cast_pow]
      rw [e1, e2]
      ring
    exact_mod_cast h
  unfold autRatio
  rw [hAF, hGC]
  have hd : ((p ^ (1 + f 1) : ℕ) : ℚ) ≠ 0 := by
    have : (p ^ (1 + f 1) : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
    exact_mod_cast this
  rw [div_eq_iff hd, hpow1, hpow2, hconv]
  push_cast
  ring

/-- Item (4) of Proposition `prop: class` (paper line 161; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 155-164): for
`(Z_p)^3` the ratio is `(p-1)^3 (p+1) (p^2+p+1)`. -/
theorem ratio_case_three_const (hp : p.Prime) {f : Fin 3 → ℕ}
    (hv : ∀ i, f i = 1) :
    autRatio p f =
      (((p - 1) ^ 3 * (p + 1) * (p ^ 2 + p + 1) : ℕ) : ℚ) := by
  have hall : ∀ s : Fin 3, f s = 1 := fun s => by fin_cases s <;> simp [hv]
  have btv : ∀ k : Fin 3, (BlockTop f k).val = 2 :=
    fun k => block_top_triple_const_val hall k
  have bbv : ∀ k : Fin 3, (BlockBot f k).val = 0 :=
    fun k => block_bot_triple_const_val hall k
  have hAF : AutFormula p f
      = (p ^ 3 - 1) * (p ^ 3 - p) * (p ^ 3 - p ^ 2) := by
    unfold AutFormula ProdOne ProdTwo ProdThree
    simp only [Fin.prod_univ_three, btv 0, btv 1, btv 2, bbv 0, bbv 1, bbv 2,
      hall]
    norm_num [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_mul,
      zero_mul]
  have hGC : GroupCard p f = p ^ 3 := by
    unfold GroupCard
    rw [Fin.sum_univ_three]
    simp only [hall]
  have hconv : (p ^ 3 - 1) * (p ^ 3 - p) * (p ^ 3 - p ^ 2)
      = (p - 1) ^ 3 * (p + 1) * (p ^ 2 + p + 1) * p ^ 3 := by
    have h1 : (1 : ℕ) ≤ p := hp.one_lt.le
    have h13 : (1 : ℕ) ≤ p ^ 3 := one_le_pow' hp.pos 3
    have hp13 : (p : ℕ) ≤ p ^ 3 := self_le_pow hp.pos 3 (by omega)
    have hp23 : (p ^ 2 : ℕ) ≤ p ^ 3 := by
      calc p ^ 2 = p ^ 2 * 1 := (mul_one _).symm
        _ ≤ p ^ 2 * p := Nat.mul_le_mul_left _ hp.one_lt.le
        _ = p ^ 3 := (pow_succ p 2).symm
    have h : (((p ^ 3 - 1 : ℕ) : ℤ)) * (((p ^ 3 - p : ℕ) : ℤ))
          * (((p ^ 3 - p ^ 2 : ℕ) : ℤ))
        = (((p - 1 : ℕ) : ℤ)) ^ 3 * (((p + 1 : ℕ) : ℤ))
            * (((p ^ 2 + p + 1 : ℕ) : ℤ)) * (((p : ℕ) : ℤ)) ^ 3 := by
      have e1 : (((p ^ 3 - 1 : ℕ) : ℤ)) = ((p : ℕ) : ℤ) ^ 3 - 1 := by
        rw [Nat.cast_sub h13, Nat.cast_pow, Nat.cast_one]
      have e2 : (((p ^ 3 - p : ℕ) : ℤ)) = ((p : ℕ) : ℤ) ^ 3 - ((p : ℕ) : ℤ) := by
        rw [Nat.cast_sub hp13, Nat.cast_pow]
      have e3 : (((p ^ 3 - p ^ 2 : ℕ) : ℤ))
          = ((p : ℕ) : ℤ) ^ 3 - ((p : ℕ) : ℤ) ^ 2 := by
        rw [Nat.cast_sub hp23, Nat.cast_pow, Nat.cast_pow]
      have e4 : (((p - 1 : ℕ) : ℤ)) = ((p : ℕ) : ℤ) - 1 := by
        rw [Nat.cast_sub h1, Nat.cast_one]
      have e5 : (((p + 1 : ℕ) : ℤ)) = ((p : ℕ) : ℤ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      have e6 : (((p ^ 2 + p + 1 : ℕ) : ℤ))
          = ((p : ℕ) : ℤ) ^ 2 + ((p : ℕ) : ℤ) + 1 := by
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
      rw [e1, e2, e3, e4, e5, e6]
      ring
    exact_mod_cast h
  unfold autRatio
  rw [hAF, hGC]
  have hd3 : ((p ^ 3 : ℕ) : ℚ) ≠ 0 := by
    have : (p ^ 3 : ℕ) ≠ 0 := pow_ne_zero 3 hp.ne_zero
    exact_mod_cast this
  rw [div_eq_iff hd3, hconv]
  push_cast
  ring

/-! ### The "all other cases" divisibility (proof lines 166-170) -/

/-- Transcription of the proof of Proposition `prop: class` (paper lines
166-170; source: /home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex
lines 166-170): outside the exceptional shapes the numerator carries the full
factor `p^{a+1} * (p-1)^2`, where `a = Σ f i`; equivalently the ratio is an
integer divisible by `p * (p-1)^2`. -/
theorem prop_class_else (hp : p.Prime) {f : Fin n → ℕ} (hf : Sorted f)
    (hpos : Pos f) (hn : 0 < n) (h1 : n ≠ 1)
    (h2 : ¬ (n = 2 ∧ f ⟨0, hn⟩ = 1))
    (h3 : ¬ (n = 3 ∧ ∀ i : Fin n, f i = 1)) :
    p ^ ((∑ i : Fin n, f i) + 1) * (p - 1) ^ 2 ∣ AutFormula p f := by
  have hn2 : 2 ≤ n := by omega
  have hP1 : ProdOne p f ∣ AutFormula p f :=
    ⟨ProdTwo p f * ProdThree p f, by rw [AutFormula, mul_assoc]⟩
  have hpm1 : (p - 1) ^ 2 ∣ AutFormula p f :=
    Nat.dvd_trans (Nat.pow_dvd_pow _ hn2)
      (Nat.dvd_trans (prodOne_dvd_pm1_pow p f) hP1)
  -- exponent bookkeeping: `Σ f i = Σ (f i - 1) + n`
  have hsplit : (∑ i : Fin n, f i) = (∑ i : Fin n, (f i - 1)) + n := by
    have hc : ∀ i : Fin n, f i = (f i - 1) + 1 := fun i => by
      have := hpos i; omega
    rw [Finset.sum_congr rfl fun i _ => hc i, Finset.sum_add_distrib]
    simp
  -- the third product dominates `Σ (f i - 1)`
  have hw : ∀ i : Fin n, 1 ≤ n - (BlockBot f i).val := fun i => by
    have := block_bot_val_lt f i; omega
  have hK3sum : (∑ i : Fin n, (f i - 1))
      ≤ ∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val) :=
    Finset.sum_le_sum fun i _ => by
      have hm := Nat.mul_le_mul_left (f i - 1) (hw i)
      rwa [Nat.mul_one] at hm
  have hineq : (∑ i : Fin n, f i) + 1
      ≤ (∑ k : Fin n, (k : ℕ))
        + (∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val))
        + (∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val)) := by
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · rcases Nat.lt_or_ge n 3 with h3lt | h3ge
      · -- `n = 2`
        have hn' : n = 2 := by omega
        subst hn'
        have h01 : f 0 ≤ f 1 := hf ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by norm_num)
        have hp0 : 1 ≤ f 0 := hpos ⟨0, by norm_num⟩
        have h20 : f 0 ≠ 1 := fun hc => h2 ⟨rfl, hc⟩
        have hf0ge : 2 ≤ f 0 := by omega
        have hT2 : (∑ k : Fin 2, (k : ℕ)) = 1 := by rw [fin_sum_coe]
        rcases lt_or_eq_of_le h01 with hlt | heq
        · -- strictly increasing: the second product equals `f 0` exactly, while
          -- the third carries `(f 0 - 1)` with weight `2` and `(f 1 - 1)` with
          -- weight `≥ 1` (paper proof, `n = 2` distinct-exponent situation)
          have bt0v : (BlockTop f 0).val = 0 := by
            have hEq := block_top_eq_self f 0 (fun s hs => by
              fin_cases s
              · simp at hs
              · simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
                  Matrix.head_cons] at hs ⊢
                exact hlt.ne')
            rw [hEq]
            rfl
          have bt1v : (BlockTop f 1).val = 1 := by
            have hEq := block_top_eq_self f 1 (fun s hs => by
              fin_cases s
              · simp at hs
              · simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
                  Matrix.head_cons] at hs ⊢
                omega)
            rw [hEq]
            rfl
          have bb0v : (BlockBot f 0).val = 0 := by
            have hEq := block_bot_eq_self f 0 fun s hs => absurd hs
              (by have := s.isLt; omega)
            rw [hEq]
            rfl
          have hD2 : (∑ j : Fin 2, f j * (2 - 1 - (BlockTop f j).val)) = f 0 := by
            rw [Fin.sum_univ_two, bt0v, bt1v]
            norm_num
          have hB : ((f 0 - 1) * 2 + (f 1 - 1) : ℕ)
              ≤ ∑ i : Fin 2, (f i - 1) * (2 - (BlockBot f i).val) := by
            rw [Fin.sum_univ_two]
            refine Nat.add_le_add ?_ ?_
            · rw [bb0v]
            · have hm1 := Nat.mul_le_mul_left (f 1 - 1)
                (show (1 : ℕ) ≤ 2 - (BlockBot f 1).val by
                  have := (BlockBot f 1).isLt; omega)
              rwa [Nat.mul_one] at hm1
          have hAexp : (∑ i : Fin 2, (f i - 1)) = (f 0 - 1) + (f 1 - 1) := by
            rw [Fin.sum_univ_two]
          rw [hT2, hD2]
          omega
        · -- all equal, value `≥ 2` by `h2`
          have hv : f 1 = f 0 := heq.symm
          have hallp : ∀ s : Fin 2, f s = f 0 := fun s => by
            fin_cases s <;> simp [heq] <;> rfl
          have hvne : f 0 ≠ 1 := fun hc => h2 ⟨rfl, hc⟩
          have hv2 : 2 ≤ f 0 := by omega
          have btv : ∀ k : Fin 2, (BlockTop f k).val = 1 :=
            fun k => block_top_pair_const_val hallp k
          have bbv : ∀ k : Fin 2, (BlockBot f k).val = 0 :=
            fun k => block_bot_pair_const_val hallp k
          have hD0 : (∑ j : Fin 2, f j * (2 - 1 - (BlockTop f j).val)) = 0 := by
            rw [Fin.sum_univ_two, btv 0, btv 1]
            simp
          have hTF : (2 : ℕ) + (∑ i : Fin 2, (f i - 1))
              ≤ ∑ i : Fin 2, (f i - 1) * (2 - (BlockBot f i).val) := by
            rw [Fin.sum_univ_two, Fin.sum_univ_two, bbv 0, bbv 1]
            have pb0 : (f ⟨0, by norm_num⟩ - 1) * (2 - 0) = (f 0 - 1) * 2 := by
              rw [show f ⟨0, by norm_num⟩ = f 0 from rfl]
            have pb1 : (f ⟨1, by norm_num⟩ - 1) * (2 - 0) = (f 1 - 1) * 2 := by
              rw [show f ⟨1, by norm_num⟩ = f 1 from rfl]
            have heq' : f 1 = f 0 := heq.symm
            omega
          rw [hT2]
          omega
      · -- `n = 3`
        have hn' : n = 3 := by omega
        subst hn'
        have hp0 : 1 ≤ f 0 := hpos ⟨0, by norm_num⟩
        have hp1v : 1 ≤ f 1 := hpos ⟨1, by norm_num⟩
        have hp2 : 1 ≤ f 2 := hpos ⟨2, by norm_num⟩
        have hchain1 : f 0 ≤ f 1 := hf ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
          (by norm_num)
        have hchain2 : f 1 ≤ f 2 := hf ⟨1, by norm_num⟩ ⟨2, by norm_num⟩
          (by norm_num)
        have hT3 : (∑ k : Fin 3, (k : ℕ)) = 3 := by rw [fin_sum_coe]
        rcases lt_or_eq_of_le (hchain1.trans hchain2) with h02 | heq02
        · -- not all equal: the `j = 0` second-product term contributes `≥ f 0`
          have ht0le : (BlockTop f 0).val ≤ 1 := by
            by_contra hge
            have hlt3 := (BlockTop f 0).isLt
            have h2v : (BlockTop f 0).val = 2 := by omega
            apply h02.ne
            have hbts := block_top_self f 0
            rw [show BlockTop f 0 = (2 : Fin 3) from Fin.val_injective h2v] at hbts
            exact hbts.symm
          have hx0 : (1 : ℕ) ≤ f 0 * (3 - 1 - (BlockTop f 0).val) := by
            have hwtwo : (1 : ℕ) ≤ 3 - 1 - (BlockTop f 0).val := by omega
            have hm : f 0 ≤ f 0 * (3 - 1 - (BlockTop f 0).val) := by
              have h1m := Nat.mul_le_mul_left (f 0) hwtwo
              rwa [Nat.mul_one] at h1m
            omega
          have hs2 : (1 : ℕ) ≤ ∑ j : Fin 3, f j * (3 - 1 - (BlockTop f j).val) := by
            rw [Fin.sum_univ_three]
            have q2 : (0 : ℕ) ≤ f 1 * (3 - 1 - (BlockTop f 1).val) := Nat.zero_le _
            have q3 : (0 : ℕ) ≤ f 2 * (3 - 1 - (BlockTop f 2).val) := Nat.zero_le _
            omega
          rw [hT3]
          omega
        · -- all equal, value `≥ 2` by `h3`
          have hv : f 1 = f 0 := le_antisymm (show f 1 ≤ f 0 by
            rw [heq02]; exact hchain2) hchain1
          have hall3 : ∀ s : Fin 3, f s = f 0 := fun s => by
            fin_cases s <;> simp [hv, heq02] <;> rfl
          have hvne : f 0 ≠ 1 := by
            intro hc
            exact h3 ⟨rfl, fun s => (hall3 s).trans hc⟩
          have hv2 : 2 ≤ f 0 := by omega
          have bbv : ∀ k : Fin 3, (BlockBot f k).val = 0 :=
            fun k => block_bot_triple_const_val hall3 k
          have hD0 : (∑ j : Fin 3, f j * (3 - 1 - (BlockTop f j).val)) = 0 := by
            have btv : ∀ k : Fin 3, (BlockTop f k).val = 2 :=
              fun k => block_top_triple_const_val hall3 k
            rw [Fin.sum_univ_three, btv 0, btv 1, btv 2]
            simp
          have hTF : (2 : ℕ) + (∑ i : Fin 3, (f i - 1))
              ≤ ∑ i : Fin 3, (f i - 1) * (3 - (BlockBot f i).val) := by
            rw [Fin.sum_univ_three, Fin.sum_univ_three, bbv 0, bbv 1, bbv 2]
            have p0 : (f ⟨0, by norm_num⟩ - 1) * (3 - 0) = (f 0 - 1) * 3 := by
              rw [show f ⟨0, by norm_num⟩ = f 0 from rfl]
            have p1 : (f ⟨1, by norm_num⟩ - 1) * (3 - 0) = (f 1 - 1) * 3 := by
              rw [show f ⟨1, by norm_num⟩ = f 1 from rfl]
            have p2 : (f ⟨2, by norm_num⟩ - 1) * (3 - 0) = (f 2 - 1) * 3 := by
              rw [show f ⟨2, by norm_num⟩ = f 2 from rfl]
            have hc02 : f 2 = f 0 := heq02.symm
            omega
          rw [hT3]
          omega
    · -- `n ≥ 4`: triangle number beats its tail
      have hTbig : n + 2 ≤ ∑ k : Fin n, (k : ℕ) := by
        rw [fin_sum_coe, Nat.le_div_iff_mul_le (by norm_num)]
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        have hm2 : (2 : ℕ) ≤ m := by omega
        have e0 : (m + 2) - 1 = m + 1 := by omega
        have e1 : (m + 2) * (m + 1) = m * m + 3 * m + 2 := by ring
        have e2 : ((m + 2) + 2) * 2 = 2 * m + 8 := by ring
        rw [e0, e2, e1]
        have hprod : (4 : ℕ) ≤ m * m := Nat.mul_le_mul hm2 hm2
        omega
      have hb := hK3sum
      have hzb : (0 : ℕ) ≤ ∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val) :=
        Nat.zero_le _
      omega
  -- combine: the decomposition realizes exactly that power of `p`
  have hdec := autFormula_eq_pow_mul p f
  have hpowdvd : p ^ ((∑ i : Fin n, f i) + 1) ∣
      p ^ ((∑ k : Fin n, (k : ℕ))
        + (∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val))
        + (∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val))) :=
    Nat.pow_dvd_pow p hineq
  have hppart : p ^ ((∑ i : Fin n, f i) + 1) ∣ AutFormula p f := by
    rw [hdec]
    exact hpowdvd.mul_right _
  have hcop : Nat.Coprime (p ^ ((∑ i : Fin n, f i) + 1)) ((p - 1) ^ 2) :=
    ((nat_coprime_pred_self hp.one_lt).symm.pow_left _).pow_right 2
  exact hcop.mul_dvd_of_dvd_of_dvd hppart hpm1

/-- Assembly of Proposition `prop: class` (paper lines 155-164; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 155-170). -/
theorem prop_class (hp : p.Prime) {f : Fin n → ℕ} (hf : Sorted f)
    (hpos : Pos f) (hn : 0 < n) :
    (n = 1 ∧ autRatio p f = ((p - 1 : ℕ) : ℚ) / (p : ℚ))
    ∨ (n = 2 ∧ (∀ i : Fin n, f i = 1) ∧
        autRatio p f = (((p - 1) ^ 2 * (p + 1) : ℕ) : ℚ) / (p : ℚ))
    ∨ (n = 2 ∧ f ⟨0, hn⟩ = 1 ∧ ¬(∀ i : Fin n, f i = 1) ∧
        autRatio p f = (((p - 1) ^ 2 : ℕ) : ℚ))
    ∨ (n = 3 ∧ (∀ i, f i = 1) ∧
        autRatio p f =
          (((p - 1) ^ 3 * (p + 1) * (p ^ 2 + p + 1) : ℕ) : ℚ))
    ∨ (p ^ ((∑ i : Fin n, f i) + 1) * (p - 1) ^ 2 ∣ AutFormula p f) := by
  rcases Nat.lt_or_ge n 2 with h12 | h2ge
  · have hn1 : n = 1 := by omega
    subst hn1
    exact Or.inl ⟨rfl, ratio_case_cyclic hp hpos⟩
  rcases Nat.lt_or_ge n 3 with h23 | h3ge
  · have hn2 : n = 2 := by omega
    subst hn2
    by_cases hv : f ⟨0, hn⟩ = 1
    · rcases lt_or_eq_of_le (hf ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ (by norm_num))
        with hlt | heq
      · have notall : ¬(∀ i : Fin 2, f i = 1) := fun hall => by
          have h11 : f 1 = 1 := hall 1
          have hv0 : f 0 = 1 := hv
          have hlt' : f 0 < f 1 := hlt
          omega
        have hv0 : f 0 = 1 := hv
        have hlt1 : (1 : ℕ) < f 1 := by
          have hlt' : f 0 < f 1 := hlt
          omega
        exact Or.inr (Or.inr (Or.inl ⟨rfl, hv, notall,
          ratio_case_two_dist hp hv0 hlt1⟩))
      · have heqN : f 1 = f 0 := heq.symm
        have hv1 : f 1 = 1 := by rw [heqN]; exact hv
        have hall2 : ∀ i : Fin 2, f i = 1 := fun i => by
          fin_cases i
          · exact hv
          · exact hv1
        have hv0 : f 0 = 1 := hv
        exact Or.inr (Or.inl ⟨rfl, hall2,
          ratio_case_two_const hp ⟨hv0, hv1⟩⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (prop_class_else hp hf hpos hn
        (by omega) (fun hc => hv hc.2) (fun hc => absurd hc.1 (by omega))))))
  rcases Nat.lt_or_ge n 4 with h34 | h4ge
  · have hn3 : n = 3 := by omega
    subst hn3
    by_cases hall1 : ∀ i, f i = 1
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hall1,
        ratio_case_three_const hp hall1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (prop_class_else hp hf hpos hn
        (by omega) (fun hc => by have := hc.1; omega)
        (fun hc => hall1 hc.2)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (prop_class_else hp hf hpos hn
      (by omega) (fun hc => by have := hc.1; omega)
      (fun hc => by have := hc.1; omega)))))

/-- Per-component denominator divides the prime. -/
theorem den_autRatio_dvd (hp : p.Prime) {f : Fin n → ℕ} (hf : Sorted f)
    (hpos : Pos f) (hn : 0 < n) : ((autRatio p f).den : ℕ) ∣ p := by
  rcases prop_class hp hf hpos hn with ⟨-, hr⟩
    | ⟨-, -, hr⟩ | ⟨-, -, -, hr⟩ | ⟨-, -, hr⟩ | hd
  · exact (rat_cross hp.pos hr).2
  · exact (rat_cross hp.pos hr).2
  · have hd1 := (num_den_of_repr_nat hr).2
    rw [hd1]
    exact Nat.one_dvd p
  · have hd1 := (num_den_of_repr_nat hr).2
    rw [hd1]
    exact Nat.one_dvd p
  · obtain ⟨w, hw⟩ := hd
    have hrepr : autRatio p f = (((p - 1) ^ 2 * w * p : ℕ) : ℚ) := by
      unfold autRatio GroupCard
      rw [hw, Nat.pow_succ']
      have hdz : (((p ^ (∑ i : Fin n, f i) : ℕ) : ℚ)) ≠ 0 := by
        have : (p ^ (∑ i : Fin n, f i) : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
        exact_mod_cast this
      rw [div_eq_iff hdz]
      push_cast
      ring
    have hd1 := (num_den_of_repr_nat hrepr).2
    rw [hd1]
    exact Nat.one_dvd p

/-- Per-component numerator carries `p - 1`. -/
theorem num_autRatio_dvd_pm1 (hp : p.Prime) {f : Fin n → ℕ} (hf : Sorted f)
    (hpos : Pos f) (hn : 0 < n) : ((p - 1 : ℕ) : ℤ) ∣ (autRatio p f).num := by
  rcases prop_class hp hf hpos hn with ⟨-, hr⟩
    | ⟨-, -, hr⟩ | ⟨-, -, -, hr⟩ | ⟨-, -, hr⟩ | hd
  · exact cop_dvd_num_of_cross hp.one_lt (rat_cross hp.pos hr).1
      (show (p - 1) ∣ p - 1 from Nat.dvd_refl _)
  · exact cop_dvd_num_of_cross hp.one_lt (rat_cross hp.pos hr).1
      (show (p - 1) ∣ (p - 1) ^ 2 * (p + 1) from ⟨(p - 1) * (p + 1), by ring⟩)
  · have hnd := num_den_of_repr_nat hr
    rw [hnd.1]
    exact Int.natCast_dvd_natCast.mpr (dvd_pow_self (p - 1) (by omega))
  · have hnd := num_den_of_repr_nat hr
    rw [hnd.1]
    refine Int.natCast_dvd_natCast.mpr ?_
    exact ⟨(p - 1) ^ 2 * ((p + 1) * (p ^ 2 + p + 1)), by ring⟩
  · obtain ⟨w, hw⟩ := hd
    have hrepr : autRatio p f = (((p - 1) ^ 2 * w * p : ℕ) : ℚ) := by
      unfold autRatio GroupCard
      rw [hw, Nat.pow_succ']
      have hdz : (((p ^ (∑ i : Fin n, f i) : ℕ) : ℚ)) ≠ 0 := by
        have : (p ^ (∑ i : Fin n, f i) : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
        exact_mod_cast this
      rw [div_eq_iff hdz]
      push_cast
      ring
    have hnd := num_den_of_repr_nat hrepr
    rw [hnd.1]
    exact Int.natCast_dvd_natCast.mpr ⟨(p - 1) * w * p, by ring⟩

end McCulloch26_2
