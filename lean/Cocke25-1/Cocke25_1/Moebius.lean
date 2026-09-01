import Cocke25_1.ElemCenters
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.GroupTheory.PGroup

/-! # The Möbius function on the element-center poset (`sec: Moby`)

Formalization of Cocke25-1 (*A Möbius function on the Centralizer Lattice*,
arXiv:2512.13839v2), Section `sec: Moby`: the Möbius function $\mu$ on the
poset $\mathcal{Z}(G) \cup \{\mathbf{Z}(G)\}$ under containment, the counting
congruence $|\mathbf{Z}^*(g)|/|\mathbf{Z}(G)| \equiv \mu(\mathbf{Z}(g)) \bmod p$
for $p$-groups (Proposition `prop: p-Mob`), and the main congruences
(Theorem `thm: Mob`).

Encoding deltas (see `status.md`): the poset Möbius function is taken from
mathlib's incidence algebra, `Mathlib.Combinatorics.Enumerative.IncidenceAlgebra`
(`IncidenceAlgebra.mu`), instantiated on the subsingleton poset of element
centers $\mathcal{Z}(G) \cup \{\mathbf{Z}(G)\}$ ordered by containment; the
exact inversion identity `IncidenceAlgebra.sum_Icc_mu_right` supplies the
$\sum\mu \equiv -1 \pmod p$ congruence of `thm: Mob` exactly (~ it holds as an
equality of integers). The quotient $|\mathbf{Z}^*(g)|/|\mathbf{Z}(G)|$
is encoded as the number of cosets meeting $\mathbf{Z}^*(g)$, i.e. the second
factor of `natCard_elementCenterClass_eq`. -/

namespace Cocke25_1

variable {G : Type*} [Group G]

open scoped Classical

/-! ### The center poset and the Möbius function -/

/-- The distinct element centers strictly contained in $X$, as a Finset:
the strict lower set summed over by the Möbius recurrence (tex lines 421-427;
"since the $\mathbf{Z}(g_i)$'s and $\mathbf{Z}(G)$ are all of the distinct
element centers that are properly contained in $\mathbf{Z}(g)$", tex line 447).
Members are exactly the sets $\mathbf{Z}(g)$ with $\mathbf{Z}(g)
\subset X$. -/
noncomputable def centerProperInside [Fintype G] (X : Set G) : Finset (Set G) :=
  (Finset.univ.filter fun g : G => elementCenter g ⊂ X).image fun g => elementCenter g

theorem mem_centerProperInside [Fintype G] {Y X : Set G} :
    Y ∈ centerProperInside X ↔ ∃ g : G, elementCenter g = Y ∧ elementCenter g ⊂ X :=
  Finset.mem_image.trans
    ⟨fun ⟨g, hg, hY⟩ => ⟨g, hY, (Finset.mem_filter.mp hg).2⟩,
     fun ⟨g, hEq, hSS⟩ => ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSS⟩, hEq⟩⟩

/-! ### Cardinality bookkeeping -/

omit [Group G] in
/-- Two disjoint sets: cardinality is additive. -/
theorem natCard_union_add [Finite G] {A B : Set G} (hAB : Disjoint A B) :
    Nat.card ↥(A ∪ B) = Nat.card ↥A + Nat.card ↥B := by
  classical
  rw [Nat.card_congr (Equiv.Set.union hAB), Nat.card_sum]

omit [Group G] in
/-- A Finset-indexed pairwise-disjoint family: cardinality of the union is the
sum of the cardinalities. -/
theorem natCard_biUnion_add [Finite G] {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (F : ι → Set G) (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (F i) (F j)) :
    Nat.card ↥(⋃ i ∈ (S : Set ι), F i)
      = ∑ i ∈ S, Nat.card ↥(F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S haS ih =>
    have hs : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (F i) (F j) := fun i hi j hj hij =>
      hpair i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hub : (⋃ i ∈ ((insert a S : Finset ι) : Set ι), F i)
        = F a ∪ ⋃ i ∈ ((S : Finset ι) : Set ι), F i := by
      ext w
      simp [Set.mem_iUnion, Finset.mem_insert]
    have hd : Disjoint (F a) (⋃ i ∈ ((S : Finset ι) : Set ι), F i) := by
      rw [Set.disjoint_iff]
      intro w hw
      rw [Set.mem_inter_iff] at hw
      obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.mp hw.2
      have hdj : Disjoint (F a) (F j) :=
        hpair a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (fun heq => haS (heq ▸ hj))
      rw [Set.disjoint_left] at hdj
      exact hdj hw.1 hwj
    rw [hub, natCard_union_add hd, ih hs, Finset.sum_insert haS]

/-! ### The element-center poset and its mathlib Möbius function

The poset $\mathcal{Z}(G) \cup \{\mathbf{Z}(G)\}$ is the subtype of `Set G`
whose members are the element centers (each $\mathbf{Z}(g)$, including
$\mathbf{Z}(1) = \mathbf{Z}(G)$, so the bottom $\hat 0$ is present). It carries
the containment (sub)order, which is a threshold decidable locally finite order
(`subtypeInstLocallyFiniteOrder`). We take $\mu$ to be mathlib's poset Möbius
function `IncidenceAlgebra.mu` seeded at the bottom: $\mu(X) = \mu(\hat
0, X)$. The exact inversion identity
`IncidenceAlgebra.sum_Icc_mu_right` then makes the counting congruences of
`thm: Mob` honestly exact. -/

/-- A subset of $G$ is an element center if it is $\mathbf{Z}(g)$ for some $g$
(tex lines 421-427; the image of $g \mapsto \mathbf{Z}(g)$). -/
noncomputable def IsElementCenter (X : Set G) : Prop :=
  ∃ g : G, elementCenter g = X

/-- The element-center poset $\mathcal{Z}(G) \cup \{\mathbf{Z}(G)\}$, a subtype
of `Set G` ordered by containment. -/
abbrev elementCenterSet (G : Type*) [Group G] := {X : Set G // IsElementCenter X}

/-- The bottom element $\hat 0 = \mathbf{Z}(G)$, which equals
$\mathbf{Z}(1)$ (`elementCenter_eq_center_iff`). -/
noncomputable def centerBot [Fintype G] : elementCenterSet G :=
  ⟨(Subgroup.center G : Set G),
    ⟨1, (elementCenter_eq_center_iff 1).mpr (Subgroup.one_mem _)⟩⟩

/-- The finite support of the poset: the image of $g \mapsto \mathbf{Z}(g)$.
Every element center is in the image by definition of `IsElementCenter`, so
this Finset is the whole poset carrier. -/
noncomputable def centerFinset [Fintype G] : Finset (elementCenterSet G) :=
  (Finset.univ : Finset G).image (fun g : G => ⟨elementCenter g, ⟨g, rfl⟩⟩)

/-- Every element center lies in `centerFinset`. -/
lemma mem_centerFinset [Fintype G] (x : elementCenterSet G) :
    x ∈ centerFinset (G := G) := by
  classical
  rcases x.2 with ⟨g, hg⟩
  exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, Subtype.ext hg⟩

/-- The containment (sub)order on element centers is locally finite: each
order interval is the restriction of the finite `centerFinset` to its bounds.
This makes mathlib's incidence-algebra Möbius function (`IncidenceAlgebra.mu`)
and its exact inversion (`IncidenceAlgebra.sum_Icc_mu_right`) available on the
element-center poset. -/
noncomputable instance [Fintype G] : LocallyFiniteOrder (elementCenterSet G) where
  finsetIcc a b := (centerFinset (G := G)).filter fun z => a ≤ z ∧ z ≤ b
  finsetIco a b := (centerFinset (G := G)).filter fun z => a ≤ z ∧ z < b
  finsetIoc a b := (centerFinset (G := G)).filter fun z => a < z ∧ z ≤ b
  finsetIoo a b := (centerFinset (G := G)).filter fun z => a < z ∧ z < b
  finset_mem_Icc a b x := by
    classical
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_centerFinset x, h⟩⟩
  finset_mem_Ico a b x := by
    classical
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_centerFinset x, h⟩⟩
  finset_mem_Ioc a b x := by
    classical
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_centerFinset x, h⟩⟩
  finset_mem_Ioo a b x := by
    classical
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_centerFinset x, h⟩⟩

/-- The Möbius function of Cocke25-1 on the poset of element centers under
containment ($\mathcal{Z}(G) \cup \{\mathbf{Z}(G)\}$, tex lines 421-427):
$\mu(\hat{0}) = 1$ for the unique minimal element $\hat 0 = \mathbf{Z}(G)$, and
$\mu(x) = -\sum_{y < x} \mu(y)$ otherwise. Defined as mathlib's poset Möbius
`IncidenceAlgebra.mu` seeded at the bottom `centerBot`, evaluated at $X$ when
$X$ is an element center (and $0$ otherwise; the function is only ever
evaluated on element centers and code downstream relies on that).
-/
noncomputable def centerMoebius [Fintype G] (X : Set G) : ℤ := by
  classical
  exact if h : IsElementCenter X then IncidenceAlgebra.mu ℤ centerBot ⟨X, h⟩ else 0


/-! ### Toward Proposition `prop: p-Mob` -/

/-- The quotient $|\mathbf{Z}^*(g)|/|\mathbf{Z}(G)|$: the number of cosets of
$\mathbf{Z}(G)$ meeting $\mathbf{Z}^*(g)$ ("the number of elements of a
transversal for $\mathbf{Z}(G)$ in $G$ that lie in $\mathbf{Z}^*(g)$", tex
line 412). Second factor of `natCard_elementCenterClass_eq`. -/
noncomputable def starCosetCount (g : G) : ℕ :=
  Nat.card ((elementCenterClass g).image (↑) : Set (G ⧸ Subgroup.center G))

theorem natCard_elementCenterClass_eq_mul [Finite G] (g : G) :
    Nat.card (elementCenterClass g)
      = Nat.card (Subgroup.center G) * starCosetCount g :=
  natCard_elementCenterClass_eq g

/-- Strict containment of sets lowers `Nat.card`. -/
theorem natCard_lt_of_ssubset [Finite G] {Y X : Set G} (hSS : Y ⊂ X) :
    Nat.card ↥Y < Nat.card ↥X :=
  Set.Finite.card_lt_card (Set.toFinite X) hSS

/-- In a finite $p$-group, a proper subgroup inclusion divides the order with
a factor still divisible by $p$ ("where $p$ divides
$|\mathbf{Z}(g):\mathbf{Z}(G)|$", tex line 443). -/
theorem exists_pos_index_mul {ι : Type*} [Group ι] {p : ℕ}
    [hp : Fact p.Prime] (hpg : IsPGroup p ι) [Finite ι] {H K : Subgroup ι}
    (hHK : H < K) :
    ∃ k : ℕ, 0 < k ∧ p ∣ k ∧ Nat.card ↥K = k * Nat.card ↥H := by
  obtain ⟨x, hxK, hxH⟩ : ∃ x, x ∈ K ∧ x ∉ H := by
    by_contra hcon
    push_neg at hcon
    refine hHK.ne (le_antisymm hHK.le ?_)
    exact SetLike.le_def.mpr fun y hy => hcon y hy
  have hcarrne : ((↑H : Set ι)) ≠ ((↑K : Set ι)) := by
    intro heq
    have h1 : x ∈ (↑H : Set ι) := by rw [heq]; exact hxK
    exact hxH h1
  have hlt : Nat.card ↥H < Nat.card ↥K :=
    Set.Finite.card_lt_card (Set.toFinite _)
      (Set.ssubset_iff_subset_ne.mpr
        ⟨fun x hx => hHK.le (SetLike.mem_coe.mpr hx), hcarrne⟩)
  have hK : IsPGroup p K := IsPGroup.to_subgroup hpg K
  have hH : IsPGroup p H := IsPGroup.to_subgroup hpg H
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hK
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hH
  have hba : b < a := by
    rcases lt_or_ge b a with h | h
    · exact h
    · rw [ha, hb] at hlt
      exact absurd hlt (not_lt.mpr (Nat.pow_le_pow_right hp.out.one_lt.le h))
  refine ⟨p ^ (a - b), Nat.pow_pos (Nat.lt_of_succ_le hp.out.one_lt.le), ?_, ?_⟩
  · cases hc : a - b with
    | zero => exact absurd hc (by omega)
    | succ j => exact ⟨p ^ j, pow_succ' p j⟩
  · have hac : a = a - b + b := (Nat.sub_add_cancel (Nat.le_of_lt hba)).symm
    have h2 : p ^ a = p ^ (a - b + b) := congrArg (fun t => p ^ t) hac
    rw [ha, h2, pow_add, hb]

/-- Pointwise congruence lifts to Finset sums in $\mathbb{Z}$. -/
theorem intSum_modEq {ι : Type*} (S : Finset ι) (f g : ι → ℤ) (m : ℤ)
    (h : ∀ i ∈ S, f i ≡ g i [ZMOD m]) :
    (∑ i ∈ S, f i) ≡ (∑ i ∈ S, g i) [ZMOD m] := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Int.ModEq.rfl
  | insert a S haS ih =>
    rw [Finset.sum_insert haS, Finset.sum_insert haS]
    exact Int.ModEq.add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- From a vanishing sum to a one-sided congruence against the negation. -/
theorem intModEq_of_add_eq_zero {m a b : ℤ} (h : a + b ≡ 0 [ZMOD m]) :
    a ≡ -b [ZMOD m] := by
  have e1 : (a + b : ℤ) ≡ 0 [ZMOD m] := h
  have e2 : (0 : ℤ) ≡ (-b + b) [ZMOD m] := by simp [Int.ModEq]
  have e3 := e1.trans e2
  exact Int.ModEq.add_right_cancel' b e3


/-- Base case of the Möbius recursion: $\mu(\mathbf{Z}(G)) = 1$, the unique
minimal element $\hat{0}$ (tex line 424). Mathlib's incidence-algebra Möbius
gives this as `IncidenceAlgebra.mu_self` at the bottom element. -/
theorem centerMoebius_center [Finite G] [Fintype G] :
    centerMoebius (Subgroup.center G : Set G) = 1 := by
  classical
  have hc : IsElementCenter ((Subgroup.center G : Set G)) :=
    ⟨1, (elementCenter_eq_center_iff 1).mpr (Subgroup.one_mem _)⟩
  unfold centerMoebius centerBot
  simp [hc, IncidenceAlgebra.mu_self]

/-- The strict-lower Möbius sum over the element-center poset (mathlib's
`Ico centerBot z`) equals the Finset sum over `centerProperInside X` of the
center-Möbius values: each is the sum of $\mu(\hat 0, \cdot)$ over the distinct
element centers strictly below $X$, with $z \mapsto z.1$ the bijection between
the subtype and set indexings (tex lines 449-451). Bridge turning mathlib's
poset recurrence into the paper's `centerProperInside` recurrence. -/
private lemma sum_mu_Ico_eq_centerProperInside [Fintype G] {X : Set G}
    (hX : IsElementCenter X) :
    (∑ x ∈ (Finset.Ico centerBot (⟨X, hX⟩ : elementCenterSet G)),
        IncidenceAlgebra.mu ℤ centerBot x)
      = (centerProperInside X).sum centerMoebius := by
  classical
  let z : elementCenterSet G := ⟨X, hX⟩
  let val : elementCenterSet G → Set G := fun x => x.1
  have hterm : ∀ x ∈ Finset.Ico centerBot z,
      centerMoebius (val x) = IncidenceAlgebra.mu ℤ centerBot x := by
    intro x hx
    have hctr : IsElementCenter (val x) := x.2
    unfold centerMoebius
    rw [dif_pos hctr]
  have hcsub : ∀ g : G, (Subgroup.center G : Set G) ⊆ elementCenter g :=
    fun g _z hz => Subgroup.mem_centralizer_iff.mpr (fun y _ => Subgroup.mem_center_iff.mp hz y)
  have hinj : Set.InjOn val ↑(Finset.Ico centerBot z) := by
    intro a _ b _ hab
    exact Subtype.ext hab
  have himg : (Finset.Ico centerBot z).image val = centerProperInside X := by
    rw [Finset.ext_iff]
    intro Y
    rw [Finset.mem_image]
    constructor
    · intro ⟨x, hx, hxy⟩
      rw [← hxy]
      rw [mem_centerProperInside]
      have hxltz : (x : Set G) < (z : Set G) :=
        (Subtype.coe_lt_coe).mpr ((Finset.mem_Ico.mp hx).2)
      have hxsub : val x ⊂ X := by
        dsimp [z]
        exact Set.ssubset_iff_subset_ne.mpr
          (lt_iff_le_and_ne.mp (by simpa using hxltz))
      rcases Finset.mem_image.mp (mem_centerFinset x) with ⟨g, hg, hgx⟩
      refine ⟨g, congrArg val hgx, ?_⟩
      · exact by rwa [(congrArg val hgx).symm] at hxsub
    · intro hY
      rcases mem_centerProperInside.mp hY with ⟨g, hEq, hSS⟩
      let x : elementCenterSet G := ⟨Y, ⟨g, hEq⟩⟩
      have hxIco : x ∈ Finset.Ico centerBot z := by
        rw [Finset.mem_Ico]
        constructor
        · change (Subgroup.center G : Set G) ⊆ Y
          rw [← hEq]
          exact hcsub g
        · have hYsub : Y ⊂ X := by rwa [hEq] at hSS
          have hle : x ≤ z := by
            change (x : Set G) ⊆ (z : Set G)
            dsimp [x, z]
            exact (Set.ssubset_iff_subset_ne.mp hYsub).1
          have hne : x ≠ z := by
            intro h
            have hyx : Y = X := by simpa [x, z] using congrArg val h
            exact (Set.ssubset_iff_subset_ne.mp hYsub).2 hyx
          exact lt_iff_le_and_ne.mpr ⟨hle, hne⟩
      exact ⟨x, hxIco, rfl⟩
  calc
    (∑ x ∈ Finset.Ico centerBot z, IncidenceAlgebra.mu ℤ centerBot x)
        = (∑ x ∈ Finset.Ico centerBot z, centerMoebius (val x)) :=
          Finset.sum_congr rfl (fun x hx => (hterm x hx).symm)
    _ = (∑ Y ∈ (Finset.Ico centerBot z).image val, centerMoebius Y) := by
          rw [Finset.sum_image (s := Finset.Ico centerBot z)
            (g := val) (f := centerMoebius) hinj]
    _ = (centerProperInside X).sum centerMoebius := by rw [himg]

/-- Recurrence step of the Möbius function: for $X$ an element center unequal to
$\mathbf{Z}(G)$, $\mu(X) = -\sum_{Y \in \mathrm{CPI}(X)} \mu(Y)$ over the
distinct element centers properly contained in $X$ ($\mu(x) = -\sum_{y<x}
\mu(y)$, tex lines 423-427). Read off mathlib's recurrence
`IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne` on the element-center poset, via the
`sum_mu_Ico_eq_centerProperInside` bridge. -/
theorem centerMoebius_eq_neg_sum [Finite G] [Fintype G] {X : Set G}
    (hX : IsElementCenter X) (hne : X ≠ (Subgroup.center G : Set G)) :
    centerMoebius X =
      -((centerProperInside X).sum fun Y => centerMoebius Y) := by
  classical
  let z : elementCenterSet G := ⟨X, hX⟩
  have hzbot : centerBot ≠ z := fun h => hne ((Subtype.ext_iff).mp h).symm
  have hcm : centerMoebius X = IncidenceAlgebra.mu ℤ centerBot z := by
    unfold centerMoebius
    rw [dif_pos hX]
  have hrec : IncidenceAlgebra.mu ℤ centerBot z =
      -∑ x ∈ Finset.Ico centerBot z, IncidenceAlgebra.mu ℤ centerBot x :=
    IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne (𝕜 := ℤ) (a := centerBot) (b := z) hzbot
  rw [hcm, hrec, ← sum_mu_Ico_eq_centerProperInside hX]

/-- **Exact Möbius inversion (upgrade of `thm: Mob` (1)).** For any element
center $X \ne \mathbf{Z}(G)$,
$$\sum_{x \in {]\!\hat 0, X]}} \mu(\hat 0, x) = -1,$$
i.e. the Möbius defects of the distinct element centers above $\hat 0 =
\mathbf{Z}(G)$ and at most $X$ sum to $-1$, as an *equality* of integers. This
is the exact core of the congruence `centerMoebius_sum_modEq_canon` (the paper
states it only $\pmod p$, tex lines 452-456): by
`IncidenceAlgebra.sum_Icc_mu_right` the full lower sum
$\sum_{x \in [\hat 0, X]}\mu(\hat 0,x)$ is `0` (the delta of the inversion), and
splitting off the bottom element's `1 = \mu(\hat 0,\hat 0)$
(`IncidenceAlgebra.mu_self`) leaves $\sum_{]\hat 0, X]} =
-1$. Note $]\hat 0, X]$ = the noncentral element centers contained in $X$. -/
theorem centerMoebius_sum_eq_neg_one [Fintype G] {X : Set G}
    (hX : IsElementCenter X) (hne : X ≠ (Subgroup.center G : Set G)) :
    (∑ x ∈ (Finset.Ioc centerBot (⟨X, hX⟩ : elementCenterSet G)),
        IncidenceAlgebra.mu ℤ centerBot x) = -1 := by
  classical
  let z : elementCenterSet G := ⟨X, hX⟩
  have hle : centerBot ≤ z := by
    change (Subgroup.center G : Set G) ⊆ X
    rcases hX with ⟨g, hg⟩
    rw [← hg]
    exact fun _a ha =>
      Subgroup.mem_centralizer_iff.mpr (fun _ _ => Subgroup.mem_center_iff.mp ha _)
  have hicsum : (∑ x ∈ (Finset.Icc centerBot z),
      IncidenceAlgebra.mu ℤ centerBot x) = 0 := by
    have hsz := IncidenceAlgebra.sum_Icc_mu_right (𝕜 := ℤ) (a := centerBot) (b := z)
    have hzb : centerBot ≠ z := fun h => hne ((Subtype.ext_iff).mp h).symm
    rw [hsz, if_neg hzb]
  have hcons : (∑ x ∈ (Finset.Icc centerBot z), IncidenceAlgebra.mu ℤ centerBot x)
      = 1 + (∑ x ∈ (Finset.Ioc centerBot z), IncidenceAlgebra.mu ℤ centerBot x) := by
    rw [Finset.Icc_eq_cons_Ioc hle, Finset.sum_cons]
    simp [IncidenceAlgebra.mu_self]
  have h1 : 1 + (∑ x ∈ (Finset.Ioc centerBot z), IncidenceAlgebra.mu ℤ centerBot x) = 0 := by
    rw [← hcons]
    exact hicsum
  dsimp [z] at h1 ⊢
  omega
