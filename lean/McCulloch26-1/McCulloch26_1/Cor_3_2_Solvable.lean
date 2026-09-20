import McCulloch26_1.Thm_3_1_SufficientCondition

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Corollary 3.2 (`solv`) of McCulloch26-1

Every solvable finite group admits a 2-factorization `G = A · B` with
prescribed factor sizes `|A| = a`, `|B| = b` for every factorization
`a * b = |G|`, realized through Theorem 3.1.

Route (tex lines 217-218): a solvable group has a subgroup chain from `{e}` to
`G` whose consecutive indices are primes (refine each derived-series step,
whose quotient is abelian, by descending through maximal subgroups -- a
maximal subgroup of a finite abelian group has prime index); the edge indices
can then be split into two blocks realizing `a` and `b`, and the one-sidedness
condition of Theorem 3.1 holds vacuously for two blocks (tex lines 203-209).

Source:
/home/chz/src/gamskil/docs/arxiv/2607.20569v3/Some_Answers_Factorization.tex
lines 213-219 (statement and printed proof).
-/

open Set Function Finset

namespace McCulloch26_1.Cor32

/-- The top subgroup's carrier is the whole type (cardinality form). -/
theorem natCard_top {B : Type*} [Group B] [Finite B] :
    Nat.card ↥(⊤ : Subgroup B) = Nat.card B := by
  symm
  refine Nat.card_eq_of_bijective (fun b => ⟨b, Subgroup.mem_top b⟩) ⟨?_, ?_⟩
  · exact fun a b hab => congrArg Subtype.val hab
  · exact fun z => ⟨z.val, Subtype.ext rfl⟩

/-- A pointwise-commutative group makes every subgroup normal. -/
theorem normal_of_pointwiseComm {A : Type*} [Group A]
    (hcomm : ∀ x y : A, x * y = y * x) (S : Subgroup A) : S.Normal :=
  ⟨fun x hx g => by
    have h : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcomm g x]
        _ = x * (g * g⁻¹) := mul_assoc x g g⁻¹
        _ = x := by rw [mul_inv_cancel g, mul_one]
    rw [h]
    exact hx⟩

/-- The element commutator of two lifts, read in the ambient group, lands in
`H` whenever the subgroup commutator `⁅K,K⁆` lies in `H`. -/
theorem coe_commutator_mem {G : Type*} [Group G] {H K : Subgroup G}
    (hcK : ⁅K, K⁆ ≤ H) (a b : ↥K) :
    ((⁅a, b⁆ : ↥K) : G) ∈ H := by
  have hcoe : ((⁅a, b⁆ : ↥K) : G) = ⁅(a : G), (b : G)⁆ := rfl
  rw [hcoe]
  exact hcK (Subgroup.commutator_mem_commutator a.property b.property)

/-- The alternating product `a * b * a⁻¹ * b⁻¹` of lifts lies in
`H.subgroupOf K`. -/
theorem mulInv_mem_subgroupOf {G : Type*} [Group G] {H K : Subgroup G}
    (hcK : ⁅K, K⁆ ≤ H) (a b : ↥K) :
    (a * b * a⁻¹ * b⁻¹ : ↥K) ∈ H.subgroupOf K :=
  Subgroup.mem_subgroupOf.mpr (coe_commutator_mem hcK a b)

/-- The quotient `K ⧸ H.subgroupOf K` is pointwise commutative when the
subgroup commutator of `K` lies in `H`. -/
theorem quotient_pointwiseComm {G : Type*} [Group G] {H K : Subgroup G}
    (hcK : ⁅K, K⁆ ≤ H) [(H.subgroupOf K).Normal] (u v : ↥K ⧸ H.subgroupOf K) :
    u * v = v * u := by
  refine QuotientGroup.induction_on u ?_
  intro a
  refine QuotientGroup.induction_on v ?_
  intro b
  have hprod1 : ((a * b)⁻¹ * (b * a) : ↥K) = ⁅b⁻¹, a⁻¹⁆ := by
    rw [commutatorElement_def, mul_inv_rev, inv_inv, inv_inv, ← mul_assoc]
  have hmem : ((a * b)⁻¹ * (b * a) : ↥K) ∈ H.subgroupOf K := by
    rw [hprod1, Subgroup.mem_subgroupOf]
    exact coe_commutator_mem hcK b⁻¹ a⁻¹
  have key : ((a * b : ↥K) : ↥K ⧸ H.subgroupOf K)
      = ((b * a : ↥K) : ↥K ⧸ H.subgroupOf K) :=
    (QuotientGroup.eq (a := (a * b : ↥K)) (b := (b * a : ↥K))).mpr hmem
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact key

/-- If `⁅K,K⁆ ≤ H`, then `H.subgroupOf K` is normal in `↥K`. -/
theorem normal_subgroupOf_of_commutator_le {G : Type*} [Group G] {H K : Subgroup G}
    (hcK : ⁅K, K⁆ ≤ H) : (H.subgroupOf K).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hid : ((g * x * g⁻¹ : ↥K) : G)
        = ((⁅(g : ↥K), (x : ↥K)⁆ : ↥K) : G) * (x : G) := by
      rw [commutatorElement_def]
      show (g : G) * (x : G) * (g : G)⁻¹
        = (g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹ * (x : G)
      rw [mul_assoc ((g : G) * (x : G) * (g : G)⁻¹) (x : G)⁻¹ (x : G),
        inv_mul_cancel (x : G), mul_one]
    rw [hid]
    exact Subgroup.mul_mem H (coe_commutator_mem hcK g x) hx⟩

/-- A finite nontrivial pointwise-commutative group has a maximal proper subgroup whose
index is prime ("each factor group is cyclic of prime order", tex line 218). -/
theorem exists_coatom_index_prime {A : Type*} [Group A] [Finite A]
    (hnt : Nontrivial A) (hcomm : ∀ x y : A, x * y = y * x) :
    ∃ M : Subgroup A, (∀ R : Subgroup A, M ≤ R → R = M ∨ R = ⊤) ∧
      ∃ p : ℕ, p.Prime ∧ Nat.card (A ⧸ M) = p := by
  classical
  have hfinSub : Finite (Subgroup A) :=
    Finite.of_injective (fun H : Subgroup A => (H : Set A))
      (fun H H' hHH => SetLike.ext' hHH)
  letI : Fintype {R : Subgroup A // R ≠ ⊤} := Fintype.ofFinite _
  obtain ⟨M, hMin, hMmax⟩ := Finset.exists_max_image
    (s := (Finset.univ : Finset {R : Subgroup A // R ≠ ⊤}))
    (f := fun R : {R : Subgroup A // R ≠ ⊤} => Nat.card ↥R.val)
    (⟨⟨⊥, bot_ne_top⟩, Finset.mem_univ _⟩)
  have hMT : M.val ≠ ⊤ := M.property
  haveI hnormM : M.val.Normal := normal_of_pointwiseComm hcomm M.val
  have hcoatom : ∀ R : Subgroup A, M.val ≤ R → R = M.val ∨ R = ⊤ := by
    intro R hRM
    by_cases hRT : R = ⊤
    · exact Or.inr hRT
    · by_cases hMR : M.val = R
      · exact Or.inl hMR.symm
      · exfalso
        have hRin : ⟨R, hRT⟩ ∈ (Finset.univ : Finset {R : Subgroup A // R ≠ ⊤}) :=
          Finset.mem_univ _
        have hssub : ((↑M.val : Set A)) ⊂ ((↑R : Set A)) := by
          refine ⟨fun x hx => hRM hx, fun hRsub => ?_⟩
          refine hMR (SetLike.ext fun z => ?_)
          exact ⟨fun hx => hRM hx, fun hz => hRsub hz⟩
        haveI : Fintype ↥M.val := Fintype.ofFinite _
        haveI : Fintype ↥R := Fintype.ofFinite _
        have hcardlt : Nat.card ↥M.val < Nat.card ↥R :=
          Finite.card_lt_card (Set.toFinite _) hssub
        exact absurd (hcardlt.trans_le (hMmax ⟨R, hRT⟩ hRin))
          (lt_irrefl (Nat.card ↥M.val))
  refine ⟨M.val, hcoatom, ?_⟩
  -- the index is prime: a proper prime divisor would give, through Cauchy's
  -- theorem in the quotient, an intermediate subgroup strictly between `M`
  -- and the top, contradicting maximality
  have hxM : ∃ x : A, x ∉ M.val := by
    by_contra hall
    push_neg at hall
    exact hMT ((Subgroup.eq_top_iff' M.val).mpr hall)
  obtain ⟨x, hx⟩ := hxM
  haveI : Nonempty (A ⧸ M.val) := ⟨QuotientGroup.mk' M.val x⟩
  have hQnt : Nontrivial (A ⧸ M.val) := by
    refine ⟨QuotientGroup.mk' M.val x, 1, ?_⟩
    intro hc
    have h1 : x ∈ MonoidHom.ker (QuotientGroup.mk' M.val) := hc
    rw [QuotientGroup.ker_mk'] at h1
    exact hx h1
  haveI : Finite (A ⧸ M.val) :=
    Finite.of_surjective (QuotientGroup.mk' M.val)
      (QuotientGroup.mk'_surjective M.val)
  haveI : Fintype (A ⧸ M.val) := Fintype.ofFinite _
  have hc1 : 1 < Nat.card (A ⧸ M.val) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff_nontrivial.mpr hQnt
  have hc0 : Nat.card (A ⧸ M.val) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨QuotientGroup.mk' M.val x⟩, ‹Finite _›⟩
  by_cases hp : Nat.Prime (Nat.card (A ⧸ M.val))
  · exact ⟨_, hp, rfl⟩
  · exfalso
    obtain ⟨q, hq, c', hc'⟩ := Nat.exists_prime_and_dvd (ne_of_gt hc1)
    have hc'0 : 0 < c' := by
      rcases Nat.eq_zero_or_pos c' with h | h
      · rw [h, Nat.mul_zero] at hc'
        exact absurd hc' hc0
      · exact h
    have hqc : q < Nat.card (A ⧸ M.val) := by
      rcases Nat.lt_or_ge c' 2 with h | h
      · exfalso
        apply hp
        have hc'1 : c' = 1 := by omega
        rw [hc', hc'1, Nat.mul_one]
        exact hq
      · have hc'2 : 2 ≤ c' := h
        have hqpos : 0 < q := hq.pos
        calc q < 2 * q := by omega
            _ = q * 2 := mul_comm _ _
            _ ≤ q * c' := Nat.mul_le_mul_left _ hc'2
            _ = Nat.card (A ⧸ M.val) := hc'.symm
    -- Cauchy in the quotient: an element of prime order `q`
    haveI : Fact q.Prime := ⟨hq⟩
    have hdvdF : q ∣ Fintype.card (A ⧸ M.val) := by
      rw [← Nat.card_eq_fintype_card]
      exact ⟨c', hc'⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card q hdvdF
    have hy1 : y ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hy
      exact hq.ne_one hy.symm
    set S : Subgroup (A ⧸ M.val) := Subgroup.zpowers y with hSdef
    have hSneT : S ≠ ⊤ := by
      intro htop
      have h1 := Nat.card_zpowers y
      rw [← hSdef, htop, natCard_top] at h1
      omega
    -- the preimage of `S` is an intermediate subgroup strictly between `M`
    -- and the top, contradicting maximality
    have hMle : M.val ≤ Subgroup.comap (QuotientGroup.mk' M.val) S := by
      intro m hm
      have heq : (QuotientGroup.mk' M.val) m = 1 := by
        have h1 : m ∈ MonoidHom.ker (QuotientGroup.mk' M.val) := by
          rw [QuotientGroup.ker_mk']
          exact hm
        exact h1
      show (QuotientGroup.mk' M.val) m ∈ S
      rw [heq]
      exact Subgroup.one_mem S
    have hneT : Subgroup.comap (QuotientGroup.mk' M.val) S ≠ ⊤ := by
      intro he
      apply hSneT
      refine le_antisymm le_top ?_
      intro w _
      obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective M.val w
      have h4 : a ∈ Subgroup.comap (QuotientGroup.mk' M.val) S := by
        rw [he]
        exact Subgroup.mem_top a
      have h5 : (QuotientGroup.mk' M.val) a ∈ S := h4
      rw [ha] at h5
      exact h5
    have hneM : Subgroup.comap (QuotientGroup.mk' M.val) S ≠ M.val := by
      intro he
      obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective M.val y
      have hzin : z ∈ Subgroup.comap (QuotientGroup.mk' M.val) S := by
        show (QuotientGroup.mk' M.val) z ∈ S
        rw [hz, hSdef]
        exact Subgroup.mem_zpowers y
      have hzM : z ∈ M.val := by
        rw [← he]
        exact hzin
      have hphi1 : (QuotientGroup.mk' M.val) z = 1 := by
        have h1 : z ∈ MonoidHom.ker (QuotientGroup.mk' M.val) := by
          rw [QuotientGroup.ker_mk']
          exact hzM
        exact h1
      rw [hz] at hphi1
      exact hy1 hphi1
    rcases hcoatom (Subgroup.comap (QuotientGroup.mk' M.val) S) hMle with he | he
    · exact hneM he
    · exact hneT he

/-! ### Splicing chains -/

/-- Concatenating two prime-index chains that share the middle subgroup
(the second one nonempty) yields a prime-index chain. -/
theorem chain_splice {G : Type*} [Group G] {A B C : Subgroup G}
    {F₁ F₂ : ℕ → Subgroup G} {r₁ r₂ : ℕ}
    (hr1 : 0 < r₁) (hr2 : 0 < r₂)
    (hF10 : F₁ 0 = A) (hF1r : F₁ r₁ = B) (hF20 : F₂ 0 = B) (hF2r : F₂ r₂ = C)
    (hm1 : ∀ j, F₁ j ≤ F₁ (j + 1)) (hm2 : ∀ j, F₂ j ≤ F₂ (j + 1))
    (he1 : ∀ j < r₁, ((F₁ j).relIndex (F₁ (j + 1))).Prime)
    (he2 : ∀ j < r₂, ((F₂ j).relIndex (F₂ (j + 1))).Prime) :
    ∃ (r : ℕ) (F : ℕ → Subgroup G),
      F 0 = A ∧ F r = C ∧ (∀ j, F j ≤ F (j + 1)) ∧
      (∀ j < r, ((F j).relIndex (F (j + 1))).Prime) ∧ 0 < r := by
  refine ⟨r₁ + r₂, fun j => if j ≤ r₁ then F₁ j else F₂ (j - r₁), ?_, ?_, ?_, ?_, by omega⟩
  · simp [hF10]
  · show (if r₁ + r₂ ≤ r₁ then F₁ (r₁ + r₂) else F₂ (r₁ + r₂ - r₁)) = C
    rw [if_neg (by omega), show r₁ + r₂ - r₁ = r₂ from by omega, hF2r]
  · intro j
    rcases Nat.lt_or_ge j r₁ with hj | hj
    · have h1 : j + 1 ≤ r₁ := by omega
      show (if j ≤ r₁ then F₁ j else _) ≤ (if j + 1 ≤ r₁ then F₁ (j + 1) else _)
      rw [if_pos (Nat.le_of_lt hj), if_pos h1]
      exact hm1 j
    · rcases eq_or_ne j r₁ with hr | hr
      · rw [hr]
        show (if r₁ ≤ r₁ then F₁ r₁ else _) ≤ (if r₁ + 1 ≤ r₁ then _ else F₂ ((r₁+1) - r₁))
        rw [if_pos (le_of_eq rfl), if_neg (by omega), show r₁ + 1 - r₁ = 1 from by omega,
          hF1r, ← hF20]
        exact hm2 0
      · show (if j ≤ r₁ then _ else F₂ (j - r₁)) ≤ (if j + 1 ≤ r₁ then _ else F₂ ((j+1) - r₁))
        rw [if_neg (by omega), if_neg (by omega),
          show j + 1 - r₁ = (j - r₁) + 1 from by omega]
        exact hm2 (j - r₁)
  · intro j hj
    rcases Nat.lt_or_ge j r₁ with hjr | hjr
    · have h1 : j + 1 ≤ r₁ := by omega
      show (((if j ≤ r₁ then F₁ j else _)).relIndex
        ((if j + 1 ≤ r₁ then F₁ (j + 1) else _))).Prime
      rw [if_pos (Nat.le_of_lt hjr), if_pos h1]
      exact he1 j hjr
    · show (((if j ≤ r₁ then _ else F₂ (j - r₁))).relIndex
        ((if j + 1 ≤ r₁ then _ else F₂ ((j+1) - r₁)))).Prime
      rcases eq_or_ne j r₁ with hr | hr
      · rw [hr]
        show (((if r₁ ≤ r₁ then F₁ r₁ else _)).relIndex
          ((if r₁ + 1 ≤ r₁ then _ else F₂ ((r₁+1) - r₁)))).Prime
        rw [if_pos (le_of_eq rfl), if_neg (by omega), show r₁ + 1 - r₁ = 1 from by omega,
          hF1r, ← hF20]
        exact he2 0 hr2
      · rw [if_neg (by omega), if_neg (by omega),
          show j + 1 - r₁ = (j - r₁) + 1 from by omega]
        exact he2 (j - r₁) (by omega)

/-! ### Refining an abelian-quotient segment into prime steps -/

/-- Every segment `[H, K]` whose top quotient is abelian (`⁅K,K⁆ ≤ H`) can be
refined into a chain with prime successive relative indices ("each factor group
is cyclic of prime order", tex line 218). -/
theorem exists_seg {G : Type*} [Group G] [Finite G] : ∀ (m : ℕ) (K H : Subgroup G),
    H ≤ K → ⁅K,K⁆ ≤ H → (H.subgroupOf K).Normal →
    Nat.card (K ⧸ H.subgroupOf K) ≤ m →
    ∃ (r : ℕ) (F : ℕ → Subgroup G),
      F 0 = H ∧ F r = K ∧ (∀ j, F j ≤ F (j + 1)) ∧
      (∀ j < r, ((F j).relIndex (F (j + 1))).Prime) ∧ (H < K → 0 < r) := by
  intro m
  refine Nat.strong_induction_on
    (p := fun m => ∀ (K H : Subgroup G), H ≤ K → ⁅K,K⁆ ≤ H →
      (H.subgroupOf K).Normal → Nat.card (K ⧸ H.subgroupOf K) ≤ m →
        ∃ (r : ℕ) (F : ℕ → Subgroup G),
          F 0 = H ∧ F r = K ∧ (∀ j, F j ≤ F (j + 1)) ∧
          (∀ j < r, ((F j).relIndex (F (j + 1))).Prime) ∧ (H < K → 0 < r)) m ?_
  intro m ih K H hHK hcK hLnorm hm
  haveI hfinQ : Finite (↥K ⧸ H.subgroupOf K) :=
    Finite.of_surjective (QuotientGroup.mk' (H.subgroupOf K))
      (QuotientGroup.mk'_surjective (H.subgroupOf K))
  haveI hLnorm : (H.subgroupOf K).Normal := normal_subgroupOf_of_commutator_le hcK
  rcases le_or_lt 2 (Nat.card (K ⧸ H.subgroupOf K)) with hc2 | hc2
  · -- nontrivial quotient: descend through a maximal subgroup of prime index
    haveI : Fintype (↥K ⧸ H.subgroupOf K) := Fintype.ofFinite _
    have hc2' : 1 < Fintype.card (↥K ⧸ H.subgroupOf K) := by
      rw [← Nat.card_eq_fintype_card]; omega
    haveI hQnt : Nontrivial (↥K ⧸ H.subgroupOf K) :=
      (Fintype.one_lt_card_iff_nontrivial (α := ↥K ⧸ H.subgroupOf K)).mp hc2'
    have hcomm := quotient_pointwiseComm hcK
    obtain ⟨M, hMcoat, p, hp, hpCard⟩ := exists_coatom_index_prime hQnt hcomm
    haveI hMnormal : M.Normal := normal_of_pointwiseComm hcomm M
    set L : Subgroup ↥K := H.subgroupOf K with hLdef
    set N' : Subgroup ↥K := Subgroup.comap (QuotientGroup.mk' L) M with hN'def
    set N : Subgroup G := Subgroup.map K.subtype N' with hNdef
    have hinj : Function.Injective K.subtype := fun a b hab => Subtype.ext hab
    have hLN : L ≤ N' := by
      intro l hl
      have h1 : l ∈ MonoidHom.ker (QuotientGroup.mk' L) := by
        rw [QuotientGroup.ker_mk']
        exact hl
      show (QuotientGroup.mk' L) l ∈ M
      rw [show (QuotientGroup.mk' L) l = 1 from h1]
      exact Subgroup.one_mem M
    have hHN : H ≤ N := by
      intro z hz
      have h1 : (⟨z, hHK hz⟩ : ↥K) ∈ MonoidHom.ker (QuotientGroup.mk' L) := by
        rw [QuotientGroup.ker_mk']
        exact hz
      have hm : (QuotientGroup.mk' L) (⟨z, hHK hz⟩ : ↥K) ∈ M := by
        rw [show (QuotientGroup.mk' L) (⟨z, hHK hz⟩ : ↥K) = 1 from h1]
        exact Subgroup.one_mem M
      exact Subgroup.mem_map.mpr ⟨⟨z, hHK hz⟩, hm, rfl⟩
    have hNKle : N ≤ K := by
      intro c hc
      rw [hNdef, Subgroup.mem_map] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      exact x.property
    have hCKleN : ⁅N,N⁆ ≤ H := (Subgroup.commutator_mono hNKle hNKle).trans hcK
    have hp2 : 2 ≤ p := hp.two_le
    have hMneT : M ≠ ⊤ := by
      intro hMT
      rw [hMT] at hpCard
      have honelt : Nat.card ((↥K ⧸ H.subgroupOf K) ⧸ (⊤ : Subgroup (↥K ⧸ H.subgroupOf K))) = 1 := by
        refine Nat.card_eq_one_iff_exists.mpr ⟨(1 : ↥K ⧸ H.subgroupOf K), fun x => ?_⟩
        refine QuotientGroup.induction_on x ?_
        intro a
        exact ((QuotientGroup.eq_one_iff a).mpr (Subgroup.mem_top a))
      rw [honelt] at hpCard
      omega
    obtain ⟨w, hwM⟩ : ∃ w : ↥K ⧸ L, w ∉ M := by
      by_contra hall
      push_neg at hall
      exact hMneT ((Subgroup.eq_top_iff' M).mpr hall)
    obtain ⟨γ, hγeq⟩ := QuotientGroup.mk'_surjective L w
    have hγN' : γ ∉ N' := by
      intro hmem
      have hγm : (QuotientGroup.mk' L) γ ∈ M := hmem
      rw [hγeq] at hγm
      exact hwM hγm
    have hNltK : N < K := by
      refine lt_of_le_of_ne hNKle ?_
      intro hNeq
      apply hγN'
      have himem : (K.subtype γ : G) ∈ N := by rw [hNeq]; exact γ.property
      rw [hNdef, Subgroup.mem_map] at himem
      obtain ⟨c, hcMem, hcEq⟩ := himem
      rw [Subtype.ext hcEq.symm]
      exact hcMem
    haveI hlnN : (H.subgroupOf N).Normal := normal_subgroupOf_of_commutator_le hCKleN
    haveI hfinHN : Finite (↥N ⧸ H.subgroupOf N) :=
      Finite.of_surjective (QuotientGroup.mk' (H.subgroupOf N))
        (QuotientGroup.mk'_surjective (H.subgroupOf N))
    haveI : Nonempty (↥N ⧸ H.subgroupOf N) := ⟨QuotientGroup.mk' (H.subgroupOf N) 1⟩
    have hp2 : 2 ≤ p := hp.two_le
    have hp2 : 2 ≤ p := hp.two_le
    have hcardNpos : 0 < Nat.card (↥N ⧸ H.subgroupOf N) := Nat.card_pos
    have hp2 : 2 ≤ p := hp.two_le
    have hprod : H.relIndex N * N.relIndex K = Nat.card (K ⧸ H.subgroupOf K) :=
      Subgroup.relIndex_mul_relIndex H N K hHN hNKle
    have hNKp : N.relIndex K = p := by
      have stepK : K = Subgroup.map K.subtype (⊤ : Subgroup ↥K) := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have stepMap : (Subgroup.map K.subtype N').relIndex (Subgroup.map K.subtype (⊤ : Subgroup ↥K))
          = Nat.card (↥K ⧸ N') := by
        rw [Subgroup.relIndex_map_map_of_injective N' (⊤ : Subgroup ↥K) hinj,
          Subgroup.relIndex_top_right]
        rfl
      rw [stepK, stepMap,
        (Nat.card_congr (QuotientGroup.quotientQuotientEquivQuotient L N' hLN).toEquiv).symm,
        show ((Subgroup.comap (QuotientGroup.mk' L) M).map (QuotientGroup.mk' L)) = M from
          Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective L) M]
      exact hpCard
    have hc1 : H.relIndex N < Nat.card (K ⧸ H.subgroupOf K) := by
      have h1 : H.relIndex N * 1 < H.relIndex N * p :=
        (Nat.mul_lt_mul_left hcardNpos).mpr hp2
      rw [Nat.mul_one, ← hNKp] at h1
      rwa [hprod] at h1
    obtain ⟨r', F', hF'0, hF'r', hmono', hedge', hrpos'⟩ :=
      ih (H.relIndex N) (lt_of_lt_of_le hc1 hm) N H hHN hCKleN hlnN
        (show Nat.card (N ⧸ H.subgroupOf N) ≤ H.relIndex N from le_refl _)
    rcases eq_or_ne H N with hHeq | hHne
    · -- degenerate: `H` itself is the pulled-back coatom, so `[H, K]` is prime
      have hHp : H.relIndex K = p := by rw [hHeq]; exact hNKp
      refine ⟨1, fun j => if j = 0 then H else K, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro j
        by_cases hj : j = 0
        · subst hj; simpa using hHK
        · simpa [hj] using le_refl _
      · intro j hj
        have hj0 : j = 0 := Nat.lt_one_iff.mp hj
        subst hj0
        show Nat.Prime (H.relIndex K)
        rw [hHp]
        exact hp
      · exact fun _ => Nat.zero_lt_one
    · -- genuine splice of the recursive chain with the single edge `[N, K]`
      set F₂ : ℕ → Subgroup G := fun j => if j = 0 then N else K with hF₂
      have hF₂0 : F₂ 0 = N := by simp [hF₂]
      have hF₂1 : F₂ 1 = K := by simp [hF₂]
      have hF₂m : ∀ j, F₂ j ≤ F₂ (j + 1) := by
        intro j
        by_cases hj : j = 0
        · subst hj
          show N ≤ K
          exact hNKle
        · show (if j = 0 then N else K) ≤ (if j + 1 = 0 then N else K)
          rw [if_neg hj, if_neg (Nat.succ_ne_zero j)]
      have hF₂e : ∀ j < 1, ((F₂ j).relIndex (F₂ (j + 1))).Prime := by
        intro j hj
        have hj0 : j = 0 := Nat.lt_one_iff.mp hj
        subst hj0
        show Nat.Prime ((if (0:ℕ) = 0 then N else K).relIndex
          (if (0:ℕ) + 1 = 0 then N else K))
        rw [if_pos rfl, if_neg (by omega)]
        rw [hNKp]
        exact hp
      obtain ⟨r, F, hf0, hfr, hmon, hed, hpos⟩ :=
        chain_splice (hrpos' (lt_of_le_of_ne hHN hHne))
          Nat.zero_lt_one hF'0 hF'r' hF₂0 hF₂1 hmono' hF₂m hedge' hF₂e
      exact ⟨r, F, hf0, hfr, hmon, hed, fun _ => hpos⟩
  · -- index 1: nothing to refine
    have h1' : H.relIndex K = 1 := by
      show Nat.card (K ⧸ H.subgroupOf K) = 1
      haveI : Nonempty (↥K ⧸ H.subgroupOf K) := ⟨QuotientGroup.mk' (H.subgroupOf K) 1⟩
      have hcpos : 0 < Nat.card (K ⧸ H.subgroupOf K) := Nat.card_pos
      omega
    have hKeqH : K ≤ H := Subgroup.relIndex_eq_one.mp h1'
    have hHeq : H = K := le_antisymm hHK hKeqH
    refine ⟨0, fun _ => H, rfl, hHeq, fun j => le_refl _,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun hlt => ?_⟩
    exact absurd (hHeq ▸ hlt) (lt_irrefl K)

/-! ### The full chain of a finite solvable group -/

/-- Strong-induction step: for every subgroup `K` of a group `G` such that
`↥K` is solvable, there is a chain from `⊥` to `K` with prime relative
indices on every edge. -/
theorem exists_chain_aux {G : Type*} [Group G] [Finite G] : ∀ (m : ℕ) (K : Subgroup G),
    Nat.card ↥K ≤ m →
    IsSolvable ↥K →
    ∃ (n : ℕ) (F : ℕ → Subgroup G),
      F 0 = ⊥ ∧ F n = K ∧ (∀ j, F j ≤ F (j + 1)) ∧
      (∀ j < n, ((F j).relIndex (F (j + 1))).Prime) := by
  intro m
  refine Nat.strong_induction_on (p := fun m => ∀ (K : Subgroup G), Nat.card ↥K ≤ m →
    IsSolvable ↥K → ∃ (n : ℕ) (F : ℕ → Subgroup G),
      F 0 = ⊥ ∧ F n = K ∧ (∀ j, F j ≤ F (j + 1)) ∧
      (∀ j < n, ((F j).relIndex (F (j + 1))).Prime)) m ?_
  intro m ih K hcard hsolvK
  classical
  rcases eq_or_ne K ⊥ with hKb | hKb
  · exact ⟨0, fun _ => ⊥, rfl, hKb.symm, fun j => le_refl _,
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · have hex : ∃ z : ↥K, z ≠ 1 := by
      by_contra hz
      push_neg at hz
      refine hKb ((Subgroup.eq_bot_iff_forall K).mpr fun x hx => ?_)
      exact congrArg Subtype.val (hz ⟨x, hx⟩)
    obtain ⟨z, hz1⟩ := hex
    haveI hntK : Nontrivial ↥K := by refine ⟨z, (1 : ↥K), hz1⟩
    obtain ⟨γ, -, hγC⟩ := SetLike.exists_of_lt
      (IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K))
    set Cint : Subgroup ↥K := ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ with hCintdef
    set C : Subgroup G := Cint.map K.subtype with hCdef
    have hinj : Function.Injective K.subtype := fun a b hab => Subtype.ext hab
    have hCK : C ≤ K := by
      intro c hc
      rw [hCdef, Subgroup.mem_map] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      exact x.property
    have hCKne : C ≠ K := by
      intro heq
      apply hγC
      have hγin : (K.subtype γ : G) ∈ C := by rw [heq]; exact γ.property
      rw [hCdef, Subgroup.mem_map] at hγin
      obtain ⟨c, hc, hce⟩ := hγin
      rw [Subtype.ext hce.symm]
      exact hc
    have hCintSolv : IsSolvable ↥Cint := subgroup_solvable_of_solvable Cint
    have hCsolv : IsSolvable ↥C := by
      have he := Subgroup.equivMapOfInjective Cint K.subtype hinj
      exact solvable_of_surjective (f := he.toMonoidHom) he.surjective
    have hCCle : ⁅K,K⁆ ≤ C := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      have key : ((⁅(⟨a, ha⟩ : ↥K), (⟨b, hb⟩ : ↥K)⁆ : ↥K) : G) = ⁅a, b⁆ := by
        show K.subtype ⁅(⟨a, ha⟩ : ↥K), (⟨b, hb⟩ : ↥K)⁆ = ⁅a, b⁆
        rw [map_commutatorElement]
        rfl
      exact Subgroup.mem_map.mpr
        ⟨⁅(⟨a, ha⟩ : ↥K), (⟨b, hb⟩ : ↥K)⁆,
          Subgroup.commutator_mem_commutator
            (Subgroup.mem_top (x := (⟨a, ha⟩ : ↥K)))
            (Subgroup.mem_top (x := (⟨b, hb⟩ : ↥K))), key⟩
    have hCssub : C < K := lt_of_le_of_ne hCK hCKne
    have hcardC : Nat.card ↥C < Nat.card ↥K := Finite.card_lt_card (Set.toFinite _) hCssub
    obtain ⟨n₁, F₁, hF₁0, hF₁n, hmono₁, hedge₁⟩ :=
      ih (Nat.card ↥C) (lt_of_lt_of_le hcardC hcard) C le_rfl hCsolv
    haveI hLnormC : (C.subgroupOf K).Normal := normal_subgroupOf_of_commutator_le hCCle
    have hdvdSeg : Nat.card (K ⧸ C.subgroupOf K) ∣ Nat.card ↥K :=
      Subgroup.relIndex_dvd_card C K
    haveI hfinK : Finite ↥K :=
      Finite.of_injective (Subtype.val : ↥K → G) Subtype.coe_injective
    haveI : Nonempty ↥K := ⟨z⟩
    have hbSeg : Nat.card (K ⧸ C.subgroupOf K) ≤ m :=
      Nat.le_trans (Nat.le_of_dvd Nat.card_pos hdvdSeg) hcard
    rcases Nat.eq_zero_or_pos n₁ with h0 | hn₁pos
    · -- first chain empty: `C = ⊥`, so the segment alone already starts at `⊥`
      obtain ⟨r₂, F₂, hF₂0, hF₂r, hmono₂, hedge₂, -⟩ :=
        exists_seg m K C hCK hCCle hLnormC hbSeg
      refine ⟨r₂, F₂, ?_, hF₂r, hmono₂, hedge₂⟩
      rw [hF₂0, show C = ⊥ from hF₁n.symm.trans (by rw [h0]; exact hF₁0)]
    · -- genuine splice of the chain of `C` with the prime-index segment `[C, K]`
      obtain ⟨r₂, F₂, hF₂0, hF₂r, hmono₂, hedge₂, hrpos₂⟩ :=
        exists_seg m K C hCK hCCle hLnormC hbSeg
      obtain ⟨r, F, hf0, hfr, hmon, hed, -⟩ :=
        chain_splice hn₁pos (hrpos₂ hCssub) hF₁0 hF₁n hF₂0 hF₂r hmono₁ hmono₂ hedge₁ hedge₂
      exact ⟨r, F, hf0, hfr, hmon, hed⟩

/-- A finite solvable group admits a subgroup chain from `⊥` to `⊤` whose
successive relative indices are all prime. -/
theorem exists_chain_of_solvable {G : Type*} [Group G] [Finite G]
    (hsolv : IsSolvable G) :
    ∃ (n : ℕ) (Gd : ℕ → Subgroup G),
      Gd 0 = ⊥ ∧ Gd n = ⊤ ∧ (∀ j, Gd j ≤ Gd (j + 1)) ∧
      (∀ j < n, ((Gd j).relIndex (Gd (j + 1))).Prime) :=
  exists_chain_aux (Nat.card G) ⊤ (by rw [natCard_top])
    (subgroup_solvable_of_solvable ⊤)

/-- Iterated monotonicity along a chain. -/
theorem le_of_mono_chain {G : Type*} [Group G] {F : ℕ → Subgroup G}
    (hmono : ∀ j, F j ≤ F (j + 1)) {j k : ℕ} (h : j ≤ k) : F j ≤ F k := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (hmono _)

/-- The relative indices along a monotone chain multiply to the total relative
index. -/
theorem prod_relIndex_chain {G : Type*} [Group G] {F : ℕ → Subgroup G}
    (n : ℕ) (hmono : ∀ j, F j ≤ F (j + 1)) :
    (∏ j ∈ Finset.range n, (F j).relIndex (F (j + 1))) = (F 0).relIndex (F n) := by
  induction n with
  | zero => simp
  | succ n ihn =>
      rw [Finset.prod_range_succ, ihn,
        Subgroup.relIndex_mul_relIndex (F 0) (F n) (F (n + 1))
          (le_of_mono_chain hmono (Nat.zero_le n)) (hmono n)]

/-! ### Splitting a divisor of a product of primes, and the corollary -/

/-- A divisor of a product of primes is a subproduct over some subset of the
indices ("`a` is a product of prime indices in its composition series, and so
is `b`", tex lines 217-218). -/
theorem exists_finset_prod_eq {e : ℕ → ℕ} :
    ∀ (n a : ℕ), (∀ i < n, (e i).Prime) →
      a ∣ ∏ i ∈ Finset.range n, e i →
      ∃ s ⊆ Finset.range n, ∏ i ∈ s, e i = a := by
  intro n
  induction n with
  | zero =>
    intro a _ hdvd
    rw [Finset.prod_range_zero] at hdvd
    exact ⟨∅, Finset.empty_subset _, by simpa using (Nat.dvd_one.mp hdvd).symm⟩
  | succ n ihn =>
    intro a hprime hdvd
    rw [Finset.prod_range_succ] at hdvd
    rcases Nat.coprime_or_dvd_of_prime (hprime n (Nat.lt_succ_self n)) a with hp | hdv
    · -- the new prime does not divide `a`: it stays out of the subset
      obtain ⟨s, hssub, hsprod⟩ :=
        ihn a (fun i hi => hprime i (Nat.lt_succ_of_lt hi))
          ((Nat.Coprime.dvd_mul_right hp.symm).mp hdvd)
      exact ⟨s, Finset.Subset.trans hssub (Finset.range_mono (Nat.le_succ n)), hsprod⟩
    · -- the new prime divides `a`: put it into the subset and recurse on `c`
      obtain ⟨c, hc⟩ := hdv
      have hn0 : e n ≠ 0 := (hprime n (Nat.lt_succ_self n)).ne_zero
      have hstep : c ∣ ∏ i ∈ Finset.range n, e i := by
        refine (mul_dvd_mul_iff_left hn0).mp ?_
        rw [mul_comm (e n) (∏ i ∈ Finset.range n, e i)]
        rwa [hc] at hdvd
      obtain ⟨s, hssub, hsprod⟩ :=
        ihn c (fun i hi => hprime i (Nat.lt_succ_of_lt hi)) hstep
      refine ⟨insert n s, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hjn | hj
        · rw [hjn]
          exact Finset.mem_range.mpr (Nat.lt_succ_self n)
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (hssub hj)))
      · rw [Finset.prod_insert (fun hj => Nat.lt_irrefl n (Finset.mem_range.mp (hssub hj))),
          hsprod, hc]

/-- Shared chain-level assembly behind Corollaries 3.2 and 3.3: any finite
group with a chain `⊥ = Gd 0 ≤ … ≤ Gd n = ⊤` whose relative indices are all
prime realizes a 2-factorization with prescribed sizes for every factorization
of the group order ("a is a product of prime indices", tex lines 217-218;
one-sidedness vacuous at two blocks, tex lines 203-209). -/
theorem exists_two_of_chain {G : Type*} [Group G] [Finite G]
    {n : ℕ} {Gd : ℕ → Subgroup G}
    (h0 : Gd 0 = ⊥) (hn : Gd n = ⊤) (hle : ∀ j, Gd j ≤ Gd (j + 1))
    (hprime : ∀ j < n, ((Gd j).relIndex (Gd (j + 1))).Prime)
    (a b : ℕ) (hab : a * b = Nat.card G) :
    ∃ A₀ A₁ : Set G,
      IsFactorization ![A₀, A₁] ∧ Nat.card A₀ = a ∧ Nat.card A₁ = b := by
  classical
  have hall : ∏ i ∈ Finset.range n, (Gd i).relIndex (Gd (i + 1)) = Nat.card G := by
    rw [prod_relIndex_chain n hle, h0, hn, Subgroup.relIndex_bot_left, natCard_top]
  have hadvd : a ∣ ∏ i ∈ Finset.range n, (Gd i).relIndex (Gd (i + 1)) := by
    rw [hall]
    exact ⟨b, hab.symm⟩
  obtain ⟨s₁, hs₁sub, hs₁prod⟩ :=
    exists_finset_prod_eq n a (fun i hi => hprime i hi) hadvd
  -- the two complementary blocks fed to the engine; its one-sidedness
  -- hypothesis is vacuous at two blocks (tex lines 203-209)
  have hsSub : ∀ t : Fin 2,
      (Fin.cases s₁ (fun _ => Finset.range n \ s₁) t : Finset ℕ) ⊆ Finset.Iio n := by
    intro t
    fin_cases t
    · show s₁ ⊆ Finset.Iio n
      intro j hj
      exact Finset.mem_Iio.mpr (Finset.mem_range.mp (hs₁sub hj))
    · show (Finset.range n \ s₁ : Finset ℕ) ⊆ Finset.Iio n
      intro j hj
      exact Finset.mem_Iio.mpr (Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1)
  have hempty : ((s₁ ∩ (Finset.range n \ s₁ : Finset ℕ)) : Finset ℕ) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun j hj => ?_
    rcases Finset.mem_inter.mp hj with ⟨h1, h2⟩
    rcases Finset.mem_sdiff.mp h2 with ⟨-, h3⟩
    exact h3 h1
  have hsDisj : ∀ t t' : Fin 2, t ≠ t' →
      ((Fin.cases s₁ (fun _ => Finset.range n \ s₁) t : Finset ℕ) ∩
          Fin.cases s₁ (fun _ => Finset.range n \ s₁) t') = ∅ := by
    intro t t' htt'
    have hvne : (t : ℕ) ≠ (t' : ℕ) := fun hc => htt' (Fin.ext hc)
    have h2t := t.isLt
    have h2t' := t'.isLt
    by_cases ht : (t : ℕ) = 0
    · have ht0 : t = 0 := Fin.ext ht
      have ht1 : t' = 1 := Fin.ext (by omega)
      subst ht0; subst ht1
      show ((s₁ ∩ (Finset.range n \ s₁ : Finset ℕ)) : Finset ℕ) = ∅
      exact hempty
    · have ht1 : t = 1 := Fin.ext (by omega)
      have ht0 : t' = 0 := Fin.ext (by omega)
      subst ht1; subst ht0
      show (((Finset.range n \ s₁ : Finset ℕ)) ∩ s₁ : Finset ℕ) = ∅
      rw [Finset.inter_comm]
      exact hempty
  have hsCov : ∀ j, j < n → ∃ t : Fin 2,
      j ∈ (Fin.cases s₁ (fun _ => Finset.range n \ s₁) t : Finset ℕ) := by
    intro j hj
    by_cases hj1 : j ∈ s₁
    · refine ⟨(0 : Fin 2), ?_⟩
      show j ∈ s₁
      exact hj1
    · refine ⟨(1 : Fin 2), ?_⟩
      show j ∈ (Finset.range n \ s₁ : Finset ℕ)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hj, hj1⟩
  have hsOne : ∀ j, j < n → ∀ t : Fin 2,
      j ∈ (Fin.cases s₁ (fun _ => Finset.range n \ s₁) t : Finset ℕ) →
      (∀ a' : Fin 2, a' < t →
        ((Fin.cases s₁ (fun _ => Finset.range n \ s₁) a' : Finset ℕ) ∩
            Finset.Iio (j + 1)) = ∅) ∨
      (∀ a' : Fin 2, a' > t →
        ((Fin.cases s₁ (fun _ => Finset.range n \ s₁) a' : Finset ℕ) ∩
            Finset.Iio (j + 1)) = ∅) := by
    intro j _jlt t _ht
    fin_cases t
    · refine Or.inl fun a' ha' => ?_
      exact absurd (Fin.lt_iff_val_lt_val.mp ha') (Nat.not_lt_zero _)
    · refine Or.inr fun a' ha' => ?_
      have hc : (1 : ℕ) < (a' : ℕ) := Fin.lt_iff_val_lt_val.mp ha'
      have hval := a'.isLt
      omega
  have hsCard : ∀ t : Fin 2,
      (∏ i ∈ (Fin.cases s₁ (fun _ => Finset.range n \ s₁) t : Finset ℕ),
        (Gd i).relIndex (Gd (i + 1)))
        = Fin.cases a (fun _ => b) t := by
    intro t
    fin_cases t
    · show (∏ i ∈ s₁, (Gd i).relIndex (Gd (i + 1))) = a
      exact hs₁prod
    · show (∏ i ∈ (Finset.range n \ s₁ : Finset ℕ),
        (Gd i).relIndex (Gd (i + 1))) = b
      have ha0 : a ≠ 0 := by
        intro h0'
        rw [h0', Nat.zero_mul] at hab
        exact absurd (Nat.lt_of_lt_of_eq Nat.card_pos hab.symm) (Nat.not_lt_zero 0)
      have hsplit : (∏ i ∈ (Finset.range n \ s₁ : Finset ℕ), (Gd i).relIndex (Gd (i + 1)))
          * ∏ i ∈ s₁, (Gd i).relIndex (Gd (i + 1))
            = ∏ i ∈ Finset.range n, (Gd i).relIndex (Gd (i + 1)) :=
        Finset.prod_sdiff hs₁sub
      rw [hs₁prod, hall, ← hab, mul_comm _ a] at hsplit
      exact mul_left_cancel₀ ha0 hsplit
  obtain ⟨A, hiso, hAcard⟩ :=
    theorem_3_1 (k := 2) h0 hn hle
      (fun t => Fin.cases a (fun _ => b) t)
      (fun t => Fin.cases s₁ (fun _ => Finset.range n \ s₁) t)
      hsSub hsDisj hsCov hsOne hsCard
  refine ⟨A 0, A 1, ?_, ?_, ?_⟩
  · have hfun : (![A 0, A 1] : Fin 2 → Set G) = A := by
      funext t
      fin_cases t <;> rfl
    rw [hfun]
    exact hiso
  · exact hAcard (0 : Fin 2)
  · exact hAcard (1 : Fin 2)

/-- **Corollary 3.2 (`solv`)**: if `G` is a solvable finite group, then a
2-factorization of `G` can be realized via Theorem 3.1 (`thm2`) for every
factorization `(a, b)` of `|G|` (tex lines 213-219).

Route (tex lines 217-218): the chain of `exists_chain_of_solvable` has prime
relative indices multiplying to `|G|`; assembly in `exists_two_of_chain`. -/
theorem corollary_3_2 {G : Type*} [Group G] [Finite G]
    (hsolv : IsSolvable G) (a b : ℕ) (hab : a * b = Nat.card G) :
    ∃ A₀ A₁ : Set G,
      IsFactorization ![A₀, A₁] ∧ Nat.card A₀ = a ∧ Nat.card A₁ = b := by
  obtain ⟨n, Gd, hGd0, hGdn, hGdmono, hGdedge⟩ := exists_chain_of_solvable hsolv
  exact exists_two_of_chain hGd0 hGdn hGdmono hGdedge a b hab

end McCulloch26_1.Cor32
