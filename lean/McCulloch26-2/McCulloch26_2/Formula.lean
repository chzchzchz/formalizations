import McCulloch26_2.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Valuations and divisibility of the Hillar-Rhea products

This file proves the two engines extracted from Proposition `prop: dc`
(the `$p$-adic valuation formula`) and the proof of Proposition `prop: class`
(paper lines 166-170, "If $G$ is not cyclic, then by Proposition `prop: form`
we have $(p-1)^2$ divides $|\mathrm{Aut}(G)|$"):

* `prop_dc_val` / `prop_dc`: $v_p(|\mathrm{Aut}(G)|)$ equals
  $\sum_k k + \sum_j e_j(n-1-d_j) + \sum_i (e_i-1)(n-c_i)$ positionally.
* `autFormula_dvd_pm1_pow`: $(p-1)^n \mid |\mathrm{Aut}(G)|$, because each
  first-product factor $p^{d_k} - p^{k-1}$ is divisible by $p-1$.

## References

Source: /home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex
lines 149-153 (Proposition `prop: dc`) and lines 166-170 (proof of
Proposition `prop: class`).
-/

namespace McCulloch26_2

variable {n : ℕ} {p : ℕ}

/-! ### Generic helpers -/

/-- A prime never divides `p ^ t - 1` for positive `t`. -/
theorem prime_not_dvd_pow_sub_one (hp : p.Prime) (ht : 0 < t) : ¬ (p ∣ p ^ t - 1) := by
  intro hdvd
  have h1 : p ∣ p ^ t := dvd_pow_self p (ne_of_gt ht)
  have hdvd1 : p ∣ p ^ t - (p ^ t - 1) := Nat.dvd_sub h1 hdvd
  rw [Nat.sub_sub_self (by have := pow_pos hp.pos t; omega)] at hdvd1
  exact hp.not_dvd_one hdvd1

/-- If every element of an index set carries a divisor of `a`, then the whole
product carries `a` raised to the cardinality. -/
theorem dvd_prod_of_dvd {ι : Type*} (s : Finset ι) (a : ℕ) (g : ι → ℕ)
    (h : ∀ i ∈ s, a ∣ g i) : a ^ s.card ∣ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dvd_rfl
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.card_insert_of_notMem hx, Nat.pow_succ']
    exact Nat.mul_dvd_mul (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The `p`-valuation of a product is the sum of the valuations (no
coprimality needed along the single coordinate `p`). -/
theorem factorization_prod_apply {ι : Type*} (s : Finset ι) (g : ι → ℕ)
    (hp : p.Prime) (h0 : ∀ i ∈ s, 0 < g i) :
    (∏ i ∈ s, g i).factorization p = ∑ i ∈ s, (g i).factorization p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hx0 : 0 < g x := h0 x (Finset.mem_insert_self x s)
    have hrest : ∀ i ∈ s, 0 < g i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert hx, Nat.factorization_mul (ne_of_gt hx0)
      (ne_of_gt (Finset.prod_pos hrest))]
    simp only [Finsupp.add_apply, ih hrest, Finset.sum_insert hx]

theorem factorization_pow_self (hp : p.Prime) (e : ℕ) : (p ^ e).factorization p = e := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    show p.factorization p = 1 from hp.factorization_self, mul_one]

/-- Coercion index sits below its own block top. -/
theorem coe_le_block_top (f : Fin n → ℕ) (k : Fin n) :
    (k : ℕ) ≤ (BlockTop f k).val :=
  Fin.le_iff_val_le_val.mp (block_top_ge f k)

/-- Block bottom value is a valid index bound. -/
theorem block_bot_val_lt (f : Fin n → ℕ) (i : Fin n) : (BlockBot f i).val < n :=
  (Fin.le_iff_val_le_val.mp (block_bot_le' f i)).trans_lt i.isLt

theorem fin_sum_coe (n : ℕ) : ∑ k : Fin n, (k : ℕ) = n * (n - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (k : ℕ))]
  exact Finset.sum_range_id n

/-! ### Positivity of the three products -/

theorem prodOne_pos (p : ℕ) (_hp : 1 < p) (f : Fin n → ℕ) : 0 < ProdOne p f := by
  refine Finset.prod_pos fun k _ => Nat.sub_pos_of_lt ?_
  exact Nat.pow_lt_pow_right _hp (Nat.lt_succ_of_le (coe_le_block_top f k))

theorem prodTwo_pos (p : ℕ) (hp : 0 < p) (f : Fin n → ℕ) : 0 < ProdTwo p f :=
  Finset.prod_pos fun j _ => pow_pos hp _

theorem prodThree_pos (p : ℕ) (hp : 0 < p) (f : Fin n → ℕ) : 0 < ProdThree p f :=
  Finset.prod_pos fun i _ => pow_pos hp _

theorem prodOne_ne_zero (p : ℕ) (hp : 1 < p) (f : Fin n → ℕ) : ProdOne p f ≠ 0 :=
  ne_of_gt (prodOne_pos p hp f)

theorem prodTwo_ne_zero (p : ℕ) (hp : 0 < p) (f : Fin n → ℕ) : ProdTwo p f ≠ 0 :=
  ne_of_gt (prodTwo_pos p hp f)

theorem prodThree_ne_zero (p : ℕ) (hp : 0 < p) (f : Fin n → ℕ) : ProdThree p f ≠ 0 :=
  ne_of_gt (prodThree_pos p hp f)

/-! ### First product -/

/-- Each factor `p^{d_k} - p^{k-1}` splits as `p^{k-1} (p^{d_k-k+1} - 1)`
with the second part prime to `p`; hence its `p`-valuation is `k - 1`
(one-indexed), i.e. the coercion here. -/
theorem prodOne_factorization (hp : p.Prime) (f : Fin n → ℕ) :
    (ProdOne p f).factorization p = ∑ k : Fin n, (k : ℕ) := by
  have hpos : ∀ k : Fin n, 0 < p ^ ((BlockTop f k).val + 1) - p ^ (k : ℕ) := fun k =>
    Nat.sub_pos_of_lt
      (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_of_le (coe_le_block_top f k)))
  unfold ProdOne
  rw [factorization_prod_apply _ _ hp (fun k _ => hpos k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hkle : (k : ℕ) ≤ (BlockTop f k).val := coe_le_block_top f k
  have hm : 0 < (BlockTop f k).val + 1 - (k : ℕ) :=
    Nat.sub_pos_of_lt (Nat.lt_succ_of_le hkle)
  have hf1 : p ^ (k : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hf2 : p ^ ((BlockTop f k).val + 1 - (k : ℕ)) - 1 ≠ 0 := fun hc =>
    prime_not_dvd_pow_sub_one hp hm (by rw [hc]; exact Nat.dvd_zero p)
  have h2 : (k : ℕ) ≤ (BlockTop f k).val + 1 := Nat.le_succ_of_le hkle
  have hspl : p ^ ((BlockTop f k).val + 1) - p ^ (k : ℕ)
      = p ^ (k : ℕ) * (p ^ ((BlockTop f k).val + 1 - (k : ℕ)) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one,
      Nat.mul_comm (p ^ (k : ℕ))
        (p ^ ((BlockTop f k).val + 1 - (k : ℕ))), ← Nat.pow_sub_mul_pow p h2]
  rw [hspl, Nat.factorization_mul hf1 hf2]
  simp only [Finsupp.add_apply, factorization_pow_self hp,
    Nat.factorization_eq_zero_of_not_dvd (prime_not_dvd_pow_sub_one hp hm)]
  omega

/-- Each first-product factor is divisible by `p - 1`, because
`p^{m} - 1 = (p-1) * Σ_{i<m} p^i` for `m ≥ 1`. -/
theorem pm1_dvd_pow_sub_one (p : ℕ) : ∀ t : ℕ, 0 < t → (p - 1) ∣ p ^ t - 1
  | 1, _ => by simpa using dvd_refl _
  | t + 2, h => by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0; simp
    have ih := pm1_dvd_pow_sub_one p (t + 1) (by omega)
    have hspl : p ^ (t + 2) - 1 = p * (p ^ (t + 1) - 1) + (p - 1) := by
      rw [pow_succ', Nat.mul_sub, Nat.mul_one]
      have hPle : p ≤ p * p ^ (t + 1) := by
        have hpowpos : 0 < p ^ (t + 1) := pow_pos h0 _
        have h1p : 1 ≤ p ^ (t + 1) := by omega
        calc p = p * 1 := (mul_one p).symm
          _ ≤ p * p ^ (t + 1) := Nat.mul_le_mul_left _ h1p
      have hlin : p * p ^ (t + 1) - 1
          = p * p ^ (t + 1) - p + (p - 1) := by omega
      exact hlin
    rw [hspl]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_refl _)

/-- Every factor `p^{d_k} - p^{k-1}` is divisible by `p - 1`
(paper lines 166-170 argument; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 166-170). -/
theorem prodOne_dvd_pm1_pow (p : ℕ) (f : Fin n → ℕ) : (p - 1) ^ n ∣ ProdOne p f := by
  have hfac : ∀ k : Fin n, (p - 1) ∣ p ^ ((BlockTop f k).val + 1) - p ^ (k : ℕ) := by
    intro k
    have hkle : (k : ℕ) ≤ (BlockTop f k).val := coe_le_block_top f k
    have hm : 0 < (BlockTop f k).val + 1 - (k : ℕ) :=
      Nat.sub_pos_of_lt (Nat.lt_succ_of_le hkle)
    have hspl : p ^ ((BlockTop f k).val + 1) - p ^ (k : ℕ)
        = p ^ (k : ℕ) * (p ^ ((BlockTop f k).val + 1 - (k : ℕ)) - 1) := by
      rw [Nat.mul_sub, Nat.mul_one,
        Nat.mul_comm (p ^ (k : ℕ))
          (p ^ ((BlockTop f k).val + 1 - (k : ℕ))),
        ← Nat.pow_sub_mul_pow p (Nat.le_succ_of_le hkle)]
    rw [hspl]
    exact dvd_mul_of_dvd_right (pm1_dvd_pow_sub_one p _ hm) _
  have h := dvd_prod_of_dvd (Finset.univ : Finset (Fin n)) (p - 1)
    (fun k => p ^ ((BlockTop f k).val + 1) - p ^ (k : ℕ))
    (fun k _ => hfac k)
  rwa [Finset.card_fin] at h

/-! ### Second and third products -/

theorem prodTwo_factorization (hp : p.Prime) (f : Fin n → ℕ) :
    (ProdTwo p f).factorization p
      = ∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val) := by
  unfold ProdTwo
  refine Eq.trans (factorization_prod_apply Finset.univ _ hp
    (fun j _ => pow_pos hp.pos _)) ?_
  exact Finset.sum_congr rfl fun j _ => factorization_pow_self hp _

theorem prodThree_factorization (hp : p.Prime) (f : Fin n → ℕ) :
    (ProdThree p f).factorization p
      = ∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val) := by
  unfold ProdThree
  refine Eq.trans (factorization_prod_apply Finset.univ _ hp
    (fun i _ => pow_pos hp.pos _)) ?_
  exact Finset.sum_congr rfl fun i _ => factorization_pow_self hp _

/-! ### The full formula valuation: Proposition `prop: dc` -/

/-- Positional form of Proposition `prop: dc` (paper lines 149-153; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 149-153):
the largest power of `p` dividing `AutFormula p f` has exponent equal to the
sum of the positional contributions. Unlike the printed statement this does
not even need sortedness or positivity of `f`. -/
theorem prop_dc_val (hp : p.Prime) (f : Fin n → ℕ) :
    (AutFormula p f).factorization p
      = (∑ k : Fin n, (k : ℕ))
        + (∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val))
        + (∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val)) := by
  have hnz : ProdOne p f ≠ 0 ∧ ProdTwo p f ≠ 0 ∧ ProdThree p f ≠ 0 :=
    ⟨prodOne_ne_zero p hp.one_lt f, prodTwo_ne_zero p hp.pos f,
      prodThree_ne_zero p hp.pos f⟩
  unfold AutFormula
  rw [Nat.factorization_mul (mul_ne_zero hnz.1 hnz.2.1) hnz.2.2,
    Nat.factorization_mul hnz.1 hnz.2.1]
  simp only [Finsupp.add_apply, prodOne_factorization hp f,
    prodTwo_factorization hp f, prodThree_factorization hp f]

/-- Proposition `prop: dc` with the triangular sum in closed form
(paper lines 149-153; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 149-153;
the printed distinct-exponent formulation uses multiplicities
$k_i$, encoded here positionally over the sorted sequence). -/
theorem prop_dc (hp : p.Prime) (f : Fin n → ℕ) :
    (AutFormula p f).factorization p
      = n * (n - 1) / 2
        + (∑ j : Fin n, f j * (n - 1 - (BlockTop f j).val))
        + (∑ i : Fin n, (f i - 1) * (n - (BlockBot f i).val)) := by
  rw [prop_dc_val hp f, fin_sum_coe]

end McCulloch26_2
