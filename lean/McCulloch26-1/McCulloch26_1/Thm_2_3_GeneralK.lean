import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Field.GeomSum
import Mathlib.GroupTheory.SemidirectProduct
import McCulloch26_1.Thm_2_3_TwoEnds

/-!
# Theorem 2.3 for all k: the Frobenius groups of order `2^m (2^m - 1)`

The general instantiation of the generalized Theorem 2.3
(`no_factorization_with_small_ends`) with the Frobenius groups of tex lines
129-142: for `k ≥ 3`, writing `m = k - 1`, the group with kernel the additive
group of `F_{2^m}` and complement the multiplicative group of `F_{2^m}`
acting by field multiplication possesses no factorization
`(2, ..., 2, 2^m - 1, 2)` (tex lines 132-133).

The two properties the generalized theorem reads off the Frobenius structure
(tex lines 133-134) come from the field axioms:

* transitivity of the complement on the nonidentity kernel elements:
  conjugating `a` by the unit `a b⁻¹` carries it to `b` (tex line 131: the
  action is field multiplication);
* elements outside the kernel have odd order: for a unit `u ≠ 1` and
  `r = 2^m - 1`, Fermat gives `u ^ r = 1`, and the geometric-sum identity
  `∑ i < r, u ^ i = (u ^ r - 1) / (u - 1)` collapses to `0` in
  characteristic `2` (the denominator is a unit), so `x ^ r = 1` and
  `orderOf x` divides the odd number `r`.

When `k = 3` (so `m = 2`) the group is isomorphic to `A_4`; the concrete
Bergman instance over `alternatingGroup (Fin 4)` is formalized separately
in `McCulloch26_1.Thm_2_3_A4_Instance`.

Source:
/home/chz/src/gamskil/docs/arxiv/2607.20569v3/Some_Answers_Factorization.tex
lines 128-142.
-/

namespace McCulloch26_1.Cor23GK

private instance fact_two_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

section Field

variable {K : Type*} [Field K]

/-- tex line 131: left multiplication by a unit, as an automorphism of the
additive group of `K` (written multiplicatively via `Multiplicative K`). -/
def unitMulAut (u : Kˣ) : MulAut (Multiplicative K) where
  toFun x := Multiplicative.ofAdd (u * x.toAdd)
  invFun x := Multiplicative.ofAdd (u⁻¹ * x.toAdd)
  left_inv x := Multiplicative.ext (by
    simp only [toAdd_ofAdd]
    rw [← mul_assoc, Units.inv_mul, one_mul])
  right_inv x := Multiplicative.ext (by
    simp only [toAdd_ofAdd]
    rw [← mul_assoc, Units.mul_inv, one_mul])
  map_mul' x y := Multiplicative.ext (by
    simp only [toAdd_ofAdd, toAdd_mul, mul_add])

/-- tex line 131: left multiplication by a unit, pointwise. -/
@[simp] theorem unitMulAut_apply (u : Kˣ) (x : Multiplicative K) :
    unitMulAut u x = Multiplicative.ofAdd (u * x.toAdd) := rfl

/-- tex line 131: the multiplicative group acts on the additive group by
field multiplication, monoidally in the acting unit. -/
def unitsMulAut : Kˣ →* MulAut (Multiplicative K) where
  toFun := unitMulAut
  map_one' := by
    ext x
    simp only [unitMulAut_apply, MulAut.one_apply, toAdd_ofAdd, Units.val_one,
      one_mul]
  map_mul' u v := by
    ext x
    simp only [unitMulAut_apply, MulAut.mul_apply, toAdd_ofAdd, Units.val_mul,
      mul_assoc]

/-- tex line 131: the hom application is left multiplication, pointwise. -/
@[simp] theorem unitsMulAut_apply (u : Kˣ) (x : Multiplicative K) :
    (unitsMulAut u) x = Multiplicative.ofAdd (u * x.toAdd) := rfl

end Field

section Frobenius

/-- The finite field `F_{2^m}` carrying both the kernel (its additive
group) and the complement (its multiplicative group) of tex lines 129-131. -/
abbrev F2m (m : ℕ) := GaloisField 2 m

/-- The Frobenius group of tex lines 129-131: the additive group of
`F_{2^m}`, semidirect its unit group acting by field multiplication. -/
abbrev Frobenius (m : ℕ) : Type :=
  Multiplicative (F2m m) ⋊[unitsMulAut (K := F2m m)] (F2m m)ˣ

/-- The kernel of tex line 130: the elementary abelian `2`-group `F_{2^m}`,
embedded on the left of the semidirect product. -/
noncomputable def frobKernel (m : ℕ) : Subgroup (Frobenius m) :=
  MonoidHom.range (SemidirectProduct.inl (G := (F2m m)ˣ))

/-- Kernel membership, unfolded (tex line 130). -/
theorem mem_frobKernel {m : ℕ} {z : Frobenius m} :
    z ∈ frobKernel m ↔
      ∃ a : Multiplicative (F2m m), SemidirectProduct.inl a = z :=
  MonoidHom.mem_range

/-- The complement component of a power is the power of the unit
(tex line 131). -/
theorem frob_pow_right (m : ℕ) (z : Frobenius m) (r : ℕ) :
    (z ^ r).right = z.right ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ, SemidirectProduct.mul_right, ih, pow_succ]

/-- The kernel component of a power is the geometric action of the unit on
the base point (tex line 131): the running sum `∑ i < r, u ^ i * a`. -/
theorem frob_pow_left (m : ℕ) (z : Frobenius m) (r : ℕ) :
    ((z ^ r).left).toAdd =
      (∑ i ∈ Finset.range r, (z.right : F2m m) ^ i) * z.left.toAdd := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, SemidirectProduct.mul_left, frob_pow_right,
        toAdd_mul, ih]
      simp only [unitsMulAut_apply, toAdd_ofAdd, Units.val_pow_eq_pow_val,
        Finset.sum_range_succ, add_mul]

/-- tex line 134: an element outside the kernel has odd order. Fermat gives
`u ^ (2 ^ m - 1) = 1` for the unit component, and the geometric sum
collapses in characteristic `2` because `u - 1` is a unit, so the whole
element satisfies `x ^ (2 ^ m - 1) = 1`. -/
theorem odd_order_of_outside {m : ℕ} (hm : m ≠ 0) {z : Frobenius m}
    (hz : z.right ≠ 1) : ¬ (2 : ℕ) ∣ orderOf z := by
  haveI : Fintype (F2m m) := Fintype.ofFinite _
  have hcard : Fintype.card (F2m m) = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 m hm
  have hu0 : (z.right : F2m m) ≠ 0 := Units.ne_zero z.right
  have hu1 : (z.right : F2m m) ≠ 1 := fun hc => hz (Units.ext hc)
  -- Fermat for the unit (tex line 131: the complement is the
  -- multiplicative group of the field)
  have hupowK : (z.right : F2m m) ^ (2 ^ m - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one (z.right : F2m m) hu0
    rwa [hcard] at h
  have hupowU : z.right ^ (2 ^ m - 1) = 1 :=
    Units.ext (by simp only [Units.val_pow_eq_pow_val, hupowK, Units.val_one])
  -- the geometric sum vanishes since `u - 1` is a unit
  have hsum : ∑ i ∈ Finset.range (2 ^ m - 1), (z.right : F2m m) ^ i = 0 := by
    rw [geom_sum_eq hu1, hupowK]
    simp
  have hzpow : z ^ (2 ^ m - 1) = 1 := by
    have hL := frob_pow_left m z (2 ^ m - 1)
    rw [hsum, zero_mul] at hL
    ext
    · rw [hL]; simp
    · rw [frob_pow_right, SemidirectProduct.one_right,
        Units.val_pow_eq_pow_val, hupowK, Units.val_one]
  -- the order divides the odd number `2 ^ m - 1`
  -- `2 ^ m` is even, so `2 ^ m - 1` is odd; keep the even witness an opaque
  -- variable so that the final `omega` sees only linear facts
  have h_even : ∃ w, 2 ^ m = 2 * w := by
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
    exact ⟨2 ^ m₀, by rw [hm₀, pow_succ]; ring⟩
  have hparity : ∀ v q : ℕ, 0 < v → ¬ (2 * v - 1 = 2 * q) := by
    intro v q hv h
    omega
  obtain ⟨w, hw, hwpos⟩ : ∃ w, 2 ^ m = 2 * w ∧ 0 < w := by
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
    exact ⟨2 ^ m₀, by rw [hm₀, pow_succ]; ring, Nat.two_pow_pos _⟩
  have hrodd : ¬ (2 : ℕ) ∣ 2 ^ m - 1 := by
    rw [hw]
    rintro ⟨q, hq⟩
    exact hparity w q hwpos hq
  intro hdvd
  have hord : orderOf z ∣ 2 ^ m - 1 := orderOf_dvd_of_pow_eq_one hzpow
  exact hrodd (hdvd.trans hord)

/-- tex line 137: even-order elements lie in the kernel. -/
theorem heven_frobenius {m : ℕ} (hm : m ≠ 0) {z : Frobenius m}
    (h2 : (2 : ℕ) ∣ orderOf z) : z ∈ frobKernel m := by
  by_contra hN
  have hzr : z.right ≠ 1 := by
    intro hc
    refine hN ⟨z.left, ?_⟩
    ext
    · rfl
    · rw [SemidirectProduct.right_inl, hc]
  exact odd_order_of_outside hm hzr h2

/-- tex line 138: the kernel is normal; conjugation moves the base point by
the action of the complement component and returns via the inverse. -/
theorem frobKernel_normal (m : ℕ) : (frobKernel m).Normal where
  conj_mem := by
    intro n hn g
    rw [mem_frobKernel] at hn ⊢
    obtain ⟨a, rfl⟩ := hn
    refine ⟨g.left * (unitsMulAut (K := F2m m) g.right) a * g.left⁻¹, ?_⟩
    have key : ∀ y : Multiplicative (F2m m),
        (unitsMulAut (K := F2m m) g.right)
          ((unitsMulAut (K := F2m m) g.right⁻¹) y) = y := by
      intro y
      simp only [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        MulAut.one_apply]
    ext
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        SemidirectProduct.inv_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, mul_one]
      rw [key g.left⁻¹]
    · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
        SemidirectProduct.right_inl, mul_one, Units.val_mul, Units.mul_inv,
        Units.val_one]

/-- tex line 130: the kernel is elementary abelian, so its elements
commute. -/
theorem frobKernel_comm (m : ℕ) {x y : Frobenius m}
    (hx : x ∈ frobKernel m) (hy : y ∈ frobKernel m) : x * y = y * x := by
  rw [mem_frobKernel] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← map_mul, mul_comm a b, map_mul]

/-- tex line 131: conjugating a kernel element by a complement element
rescales it by the inverse unit (field multiplication). -/
theorem conj_inl_inr (m : ℕ) (v : (F2m m)ˣ) (a : Multiplicative (F2m m)) :
    (SemidirectProduct.inr v : Frobenius m)⁻¹ * SemidirectProduct.inl a *
      SemidirectProduct.inr v
      = SemidirectProduct.inl (Multiplicative.ofAdd ((v⁻¹ : F2m m) * a.toAdd)) := by
  rw [← map_inv]
  ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
      SemidirectProduct.left_inl, SemidirectProduct.right_inr, one_mul,
      mul_one, unitsMulAut_apply, toAdd_ofAdd, MulEquiv.map_one,
      Units.val_inv_eq_inv_val]
  · simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inr,
      SemidirectProduct.right_inl, mul_one, inv_mul_cancel]

/-- tex line 139: the complement is transitive on the nonidentity kernel
elements; the conjugating unit is `a b⁻¹` (field multiplication). -/
theorem frobKernel_conj (m : ℕ) {x y : Frobenius m}
    (hx : x ∈ frobKernel m) (hy : y ∈ frobKernel m) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) : ∃ t : Frobenius m, t⁻¹ * x * t = y := by
  rw [mem_frobKernel] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hne : ∀ c : Multiplicative (F2m m),
      (SemidirectProduct.inl c : Frobenius m) ≠ 1 → c.toAdd ≠ 0 := by
    intro c hc h0
    apply hc
    rw [← ofAdd_toAdd c, h0, ofAdd_zero, map_one]
  have ha := hne a hx1
  have hb := hne b hy1
  have huinv : ((Units.mk0 (a.toAdd * (b.toAdd)⁻¹)
      (mul_ne_zero ha (inv_ne_zero hb)))⁻¹ : F2m m) * a.toAdd = b.toAdd := by
    rw [Units.val_mk0, mul_inv_rev, inv_inv, mul_assoc,
      inv_mul_cancel₀ ha, mul_one]
  refine ⟨SemidirectProduct.inr (Units.mk0 (a.toAdd * (b.toAdd)⁻¹)
    (mul_ne_zero ha (inv_ne_zero hb))), ?_⟩
  rw [conj_inl_inr, huinv, ofAdd_toAdd]

end Frobenius

/-- tex lines 132-133: the size tuple `(2, ..., 2, 2^m - 1, 2)` of the
`k = m + 1` factors: `m - 1` entries `2`, then `2^m - 1`, then `2`. -/
def sizesFrob (m : ℕ) : Fin (m + 1) → ℕ :=
  fun t => if (t : ℕ) = m - 1 then 2 ^ m - 1 else 2

/-- Theorem `thm1` (tex lines 132-142) for all `k ≥ 3`, parametrized by
`k = m' + 3` (so `m = k - 1 = m' + 2`): the Frobenius group of order
`2^m (2^m - 1)` with kernel `F_2^m` and complement the multiplicative
group of `F_{2^m}` possesses no `k`-fold factorization for the
factorization `(2, ..., 2, 2^m - 1, 2)` of `|G|`. -/
theorem no_factorization_frobenius (m' : ℕ) :
    ¬ ∃ A : Fin (m' + 3) → Set (Frobenius (m' + 2)),
      IsFactorization A ∧ ∀ t, Nat.card ↥(A t) = sizesFrob (m' + 2) t := by
  rintro ⟨A, hfac, hcard⟩
  refine no_factorization_with_small_ends (frobKernel_normal _) (fun x y hx hy =>
      frobKernel_comm _ hx hy) (fun z hz => heven_frobenius (by omega) hz)
    (fun x y hx hx1 hy hy1 => frobKernel_conj _ hx hy hx1 hy1) A hfac ?_ ?_
  · rw [hcard 0]
    simp [sizesFrob]
  · rw [hcard (Fin.last (m' + 2))]
    simp [sizesFrob]

end McCulloch26_1.Cor23GK
