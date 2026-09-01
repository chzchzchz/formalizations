import Cocke25_1.Moebius

/-! # The counting congruence of `prop: p-Mob`

Formalization of Cocke25-1, Proposition `prop: p-Mob` (tex lines 430-448):
for a $p$-group, $|\mathbf{Z}^*(g)|/|\mathbf{Z}(G)| \equiv \mu(\mathbf{Z}(g))
\bmod p$, with the quotient encoded as `starCosetCount g`. -/

namespace Cocke25_1

variable {G : Type*} [Group G]

open scoped Classical

/-- $\mathbf{Z}(G) \subseteq \mathbf{Z}(g)$: central elements commute with
all of $G$, hence lie in every centralizer.

Source (Section `sec: elems`, tex line 371):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem center_subset_elementCenter (g : G) :
    (Subgroup.center G : Set G) ⊆ elementCenter g := fun _z hz =>
  Subgroup.mem_centralizer_iff.mpr fun y _ => Subgroup.mem_center_iff.mp hz y

/-- Element-center hypothesis bundle for representatives $s$ strictly inside
$\mathbf{Z}(g)$ (tex lines 437, 447: "$\mathbf{Z}(g_1), \dots$ distinct and
comprise all of the element centers properly contained in $\mathbf{Z}(g)$";
the representative set excludes $\mathbf{Z}(G)$'s class and $g$ itself). -/
structure RepProps (G : Type*) [Group G] (g : G) (s : Finset G) : Prop where
  gne : g ∉ (Subgroup.center G : Set G)
  noncenter : ∀ j ∈ s, j ∉ (Subgroup.center G : Set G)
  inside : ∀ j ∈ s, elementCenter j ⊆ elementCenter g
  distinct : ∀ j ∈ s, ∀ k ∈ s, elementCenter j = elementCenter k → j = k
  proper : ∀ j ∈ s, elementCenter j ≠ elementCenter g
  cover : ∀ x : G, x ∉ (Subgroup.center G : Set G) →
    elementCenter x ⊆ elementCenter g → elementCenter x ≠ elementCenter g →
    ∃ j ∈ s, elementCenter j = elementCenter x

/-- Every subgroup's carrier carries the same cardinal as the subgroup. -/
theorem natCard_coe_set_eq {K : Subgroup G} :
    Nat.card ↥((K : Set G)) = Nat.card ↥K := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun _ => SetLike.mem_coe)]

/-- Cardinality identity behind `prop: p-Mob` (tex lines 437-443): with one
representative per strictly-smaller non-central center,
$$|\mathbf{Z}(g)| = |\mathbf{Z}(G)| \cdot (\mathrm{sc}(g) +
\sum_{j} \mathrm{sc}(j) + 1),$$
where $\mathrm{sc}$ counts cosets of $\mathbf{Z}(G)$ meeting each class.
Proof: decompose $\mathbf{Z}(g)$ via `cor: z_stars_fin`
(`zstars_fin_eq`, tex line 404), additivity over the disjoint pieces
(`natCard_union_add`, `natCard_biUnion_add`), then substitute
`natCard_elementCenterClass_eq_mul` per piece. -/
theorem natCard_elementCenter_eq_sum [Finite G] {g : G} {s : Finset G}
    (rp : RepProps G g s) :
    Nat.card ↥(elementCenter g)
      = Nat.card ↥((Subgroup.center G : Set G)) *
          ((starCosetCount g + ∑ j ∈ s, starCosetCount j) + 1) := by
  classical
  have hgns : g ∉ s := fun hh => rp.proper g hh rfl
  have hSnc : ∀ j ∈ insert g s, j ∉ (Subgroup.center G : Set G) := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hjr | hj
    · rw [hjr]
      exact rp.gne
    · exact rp.noncenter j hj
  have hSsub : ∀ j ∈ insert g s, elementCenter j ⊆ elementCenter g := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hjr | hj
    · rw [hjr]
    · exact rp.inside j hj
  have hSdist : ∀ j ∈ insert g s, ∀ k ∈ insert g s,
      elementCenter j = elementCenter k → j = k := by
    intro j hj k hk heq
    rcases Finset.mem_insert.mp hj with hjr | hj
    · rw [hjr] at heq ⊢
      rcases Finset.mem_insert.mp hk with hkr | hk
      · subst hkr
        rfl
      · exact absurd heq.symm (rp.proper k hk)
    · rcases Finset.mem_insert.mp hk with hkr | hk
      · rw [hkr] at heq ⊢
        exact absurd heq (rp.proper j hj)
      · exact rp.distinct j hj k hk heq
  have hScov : ∀ x : G, x ∉ (Subgroup.center G : Set G) →
      elementCenter x ⊆ elementCenter g →
      ∃ j ∈ insert g s, elementCenter j = elementCenter x := by
    intro x hxnc hxsub
    by_cases hc : elementCenter x = elementCenter g
    · exact ⟨g, Finset.mem_insert_self _ _, hc.symm⟩
    · obtain ⟨j, hj, heq⟩ := rp.cover x hxnc hxsub hc
      exact ⟨j, Finset.mem_insert_of_mem hj, heq⟩
  have hHmem : elementCenter g ∈ centralizers G :=
    centralizerSet_mem_centralizers (centralizerSet {g})
  have hdec := zstars_fin_eq hHmem hSnc hSsub hSdist hScov
  have hdis := zstars_fin_disjoint hSnc hSdist
  have hdU : Disjoint
      (⋃ j ∈ ((insert g s : Finset G) : Set G), elementCenterClass j)
      ((Subgroup.center G : Set G)) := by
    rw [Set.disjoint_left]
    intro w hw1 hw2
    obtain ⟨j, hjS, hwj⟩ := Set.mem_iUnion₂.mp hw1
    have hjm : j ∈ insert g s := Finset.mem_coe.mp hjS
    rcases Finset.mem_insert.mp hjm with hjr | hjm
    · rw [hjr] at hwj
      exact Set.disjoint_left.mp
        (hdis.1 g (Finset.mem_insert_self _ _)) hwj hw2
    · exact Set.disjoint_left.mp
        (hdis.1 j (Finset.mem_insert_of_mem hjm)) hwj hw2
  have hpair : ∀ j ∈ insert g s, ∀ k ∈ insert g s, j ≠ k →
      Disjoint (elementCenterClass j) (elementCenterClass k) := by
    intro j hj k hk hne
    rcases Finset.mem_insert.mp hj with hjr | hj
    · rw [hjr] at hne ⊢
      rcases Finset.mem_insert.mp hk with hkr | hk
      · exact absurd hkr hne.symm
      · exact hdis.2 g (Finset.mem_insert_self _ _) k
          (Finset.mem_insert_of_mem hk) hne
    · rcases Finset.mem_insert.mp hk with hkr | hk
      · rw [hkr]
        refine Set.disjoint_left.mpr fun w hw1 hw2 => ?_
        have e1 : elementCenter w = elementCenter j := hw1
        have e2 : elementCenter w = elementCenter g := hw2
        exact rp.proper j hj (by rw [← e1, ← e2])
      · exact hdis.2 j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hne
  have hsum : ∑ j ∈ insert g s, Nat.card ↥(elementCenterClass j)
      = ∑ j ∈ insert g s, Nat.card ↥(Subgroup.center G) * starCosetCount j :=
    Finset.sum_congr rfl fun j hj => natCard_elementCenterClass_eq_mul j
  rw [hdec, natCard_union_add hdU, natCard_coe_set_eq,
    natCard_biUnion_add (insert g s) (fun j => elementCenterClass j) hpair,
    hsum, Finset.sum_insert hgns, ← Finset.mul_sum]
  ring
/-- Möbius recursion in split form (tex lines 445-447): with one
representative per strictly-smaller center,
$\mu(\mathbf{Z}(g)) = -(1 + \sum_{j} \mu(\mathbf{Z}(g_j)))$. -/
theorem moebius_split [Finite G] [Fintype G] {g : G} {s : Finset G}
    (rp : RepProps G g s) :
    centerMoebius (elementCenter g)
      = -(1 + ∑ j ∈ s, centerMoebius (elementCenter j)) := by
  classical
  have hne : elementCenter g ≠ (Subgroup.center G : Set G) := fun he =>
    rp.gne ((elementCenter_eq_center_iff g).mp he)
  have hc1 : elementCenter (1 : G) = (Subgroup.center G : Set G) :=
    (elementCenter_eq_center_iff 1).mpr (Subgroup.one_mem _)
  have hcsub1 : elementCenter (1 : G) ⊆ elementCenter g := by
    rw [hc1]
    exact center_subset_elementCenter g
  have hcne1 : ¬(elementCenter g ⊆ elementCenter (1 : G)) := fun hs =>
    rp.gne ((elementCenter_eq_center_iff g).mp
      (Set.eq_of_subset_of_subset (hs.trans (le_of_eq hc1))
        (center_subset_elementCenter g)))
  have hcpi : centerProperInside (elementCenter g)
      = insert (Subgroup.center G : Set G) (s.image fun i => elementCenter i) := by
    ext Y
    rw [mem_centerProperInside, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨g', hEqY, hSS⟩
      by_cases hc : elementCenter g' = (Subgroup.center G : Set G)
      · left
        rw [← hEqY, hc]
      · right
        have hxnc : g' ∉ (Subgroup.center G : Set G) := fun hm =>
          hc ((elementCenter_eq_center_iff g').mpr hm)
        have hne2 : elementCenter g' ≠ elementCenter g := fun he =>
          hSS.2 (by rw [he])
        obtain ⟨j, hj, heq⟩ := rp.cover g' hxnc hSS.1 hne2
        exact ⟨j, hj, heq.trans hEqY⟩
    · rintro (hY | ⟨i, hi₁, heqY⟩)
      · exact ⟨(1 : G), ((elementCenter_eq_center_iff 1).mpr
          (Subgroup.one_mem _)).trans hY.symm, ⟨hcsub1, hcne1⟩⟩
      · exact ⟨i, heqY, ⟨rp.inside i hi₁,
          fun hsub => rp.proper i hi₁
            (Set.eq_of_subset_of_subset (rp.inside i hi₁) hsub)⟩⟩
  have hnc : ¬(Subgroup.center G : Set G) ∈ s.image (fun i => elementCenter i) :=
    fun hm => by
      obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hm
      exact rp.noncenter j hj ((elementCenter_eq_center_iff j).mp hjc)
  rw [centerMoebius_eq_neg_sum (hX := ⟨g, rfl⟩) hne, hcpi, Finset.sum_insert hnc,
    centerMoebius_center, Finset.sum_image rp.distinct]

/-! ### The center order and shared bookkeeping -/

/-- The order of $\mathbf{Z}(G)$ in a finite $p$-group is a positive power of
$p$ (`IsPGroup.iff_card`), hence positive. -/
theorem card_center_pos {p : ℕ} [hp : Fact p.Prime] (hpg : IsPGroup p G)
    [Finite G] : 0 < Nat.card ↥(Subgroup.center G) := by
  obtain ⟨w, hexp⟩ :=
    IsPGroup.iff_card.mp (IsPGroup.to_subgroup hpg (Subgroup.center G))
  rw [hexp]
  exact Nat.pow_pos (Nat.lt_of_succ_le hp.out.one_lt.le)

/-! ### Proposition `prop: p-Mob` -/

/-- **Proposition `prop: p-Mob`** of Cocke25-1: in a finite $p$-group,
$$|\mathbf{Z}^*(g)|/|\mathbf{Z}(G)| \equiv \mu(\mathbf{Z}(g)) \pmod p,$$
where the quotient counts cosets of $\mathbf{Z}(G)$ meeting
$\mathbf{Z}^*(g)$ ("the number of elements of a transversal for
$\mathbf{Z}(G)$ in $G$ that lie in $\mathbf{Z}^*(g)$", tex line 412) and
$\mu$ is the centralizer-lattice Möbius function (tex lines 421-427).

Proof: strong induction on $|\mathbf{Z}(g)|$. If $g \in \mathbf{Z}(G)$ both
sides are $1$: $\mathbf{Z}^*(g) = \mathbf{Z}(G)$ is one coset (tex line 375).
Otherwise representatives $g_i$ for the strictly smaller element centers
(`cor: z_stars_fin`, tex lines 403-405) give
$$|\mathbf{Z}(g)| = |\mathbf{Z}(G)| \cdot (\mathrm{sc}(g) +
\sum_i \mathrm{sc}(g_i) + 1),$$
while the index $|\mathbf{Z}(g):\mathbf{Z}(G)|$ is divisible by $p$ (tex line
443), killing the bracket modulo $p$; the Möbius recursion
$\mu(\mathbf{Z}(g)) = -(1 + \sum_i \mu(\mathbf{Z}(g_i)))$ (tex lines 445-447)
and induction on each $g_i$ finish the congruence.

Source (Section `sec: Moby`, proposition `prop: p-Mob`, statement tex lines
430-448):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem starCosetCount_modEq_moebius {p : ℕ} [hp : Fact p.Prime]
    (hpg : IsPGroup p G) [Finite G] [Fintype G] (g : G) :
    ((starCosetCount g : ℕ) : ℤ)
      ≡ centerMoebius (elementCenter g) [ZMOD (p : ℤ)] := by
  classical
  have hcCpos := card_center_pos hpg
  have key : ∀ m : ℕ, ∀ q : G, Nat.card ↥(elementCenter q) ≤ m →
      ((starCosetCount q : ℕ) : ℤ)
        ≡ centerMoebius (elementCenter q) [ZMOD (p : ℤ)] := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro q hqm
      by_cases hqc : q ∈ Subgroup.center G
      · have heq : elementCenter q = (Subgroup.center G : Set G) :=
          (elementCenter_eq_center_iff q).mpr hqc
        have hcls : elementCenterClass q = (Subgroup.center G : Set G) :=
          elementCenterClass_center hqc
        have e := natCard_elementCenterClass_eq_mul q
        rw [hcls, natCard_coe_set_eq] at e
        have hscq : starCosetCount q = 1 :=
          mul_left_cancel₀ hcCpos.ne' (e.symm.trans (mul_one _).symm)
        rw [hscq, heq, centerMoebius_center]
        exact Int.ModEq.rfl
      · obtain ⟨s₀, hs₀nc, hs₀sub, hs₀dist, hs₀cov⟩ :=
          exists_zstars_reps (H := elementCenter q)
        set s₁ : Finset G :=
          s₀.filter (fun i => elementCenter i ≠ elementCenter q) with hs₁def
        have hrp : RepProps G q s₁ :=
          { gne := hqc
            noncenter := fun j hj => hs₀nc j (Finset.mem_filter.mp hj).1
            inside := fun j hj => hs₀sub j (Finset.mem_filter.mp hj).1
            distinct := fun j hj k hk heq =>
              hs₀dist j (Finset.mem_filter.mp hj).1 k
                (Finset.mem_filter.mp hk).1 heq
            proper := fun j hj => (Finset.mem_filter.mp hj).2
            cover := by
              intro x hxnc hxsub hxne
              obtain ⟨i, hi₀, heq⟩ := hs₀cov x hxnc hxsub
              refine ⟨i, Finset.mem_filter.mpr ⟨hi₀, ?_⟩, heq⟩
              rw [heq]
              exact hxne }
        have hqs₁ : q ∉ s₁ := fun hh => hrp.proper q hh rfl
        have hKcard : Nat.card ↥(elementCenter q)
            = Nat.card ↥(Subgroup.centralizer (centralizerSet {q})) :=
          natCard_coe_set_eq (K := Subgroup.centralizer (centralizerSet {q}))
        have hle : Subgroup.center G ≤
            Subgroup.centralizer (centralizerSet {q}) :=
          SetLike.le_def.mpr (center_le_of_mem_centralizers
            (centralizerSet_mem_centralizers (centralizerSet {q})))
        have hqK : q ∈ Subgroup.centralizer (centralizerSet {q}) :=
          Subgroup.mem_centralizer_iff.mpr fun y hy =>
            (Subgroup.mem_centralizer_iff.mp hy
              q (Set.mem_singleton_iff.mpr rfl)).symm
        obtain ⟨k, -, hpdvd, hkcard⟩ := exists_pos_index_mul hpg
          (lt_of_le_of_ne hle fun he =>
            hqc (by rw [he.symm] at hqK; exact hqK))
        have hpart := natCard_elementCenter_eq_sum hrp
        rw [hKcard, hkcard, natCard_coe_set_eq,
          Nat.mul_comm k (Nat.card ↥(Subgroup.center G))] at hpart
        have hkX : k = (starCosetCount q + ∑ j ∈ s₁, starCosetCount j) + 1 :=
          mul_left_cancel₀ hcCpos.ne' hpart
        rw [hkX] at hpdvd
        have hv : ((starCosetCount q : ℕ) : ℤ)
            + ((∑ j ∈ s₁, starCosetCount j : ℕ) : ℤ) + 1 ≡ 0 [ZMOD (p : ℤ)] := by
          rw [Int.modEq_zero_iff_dvd]
          exact_mod_cast hpdvd
        have hspl : ((starCosetCount q : ℕ) : ℤ)
            ≡ -(((∑ j ∈ s₁, starCosetCount j : ℕ) : ℤ) + 1) [ZMOD (p : ℤ)] :=
          intModEq_of_add_eq_zero hv
        rw [add_comm] at hspl
        have hIHsum : (∑ j ∈ s₁, ((starCosetCount j : ℕ) : ℤ))
              ≡ ∑ j ∈ s₁, centerMoebius (elementCenter j) [ZMOD (p : ℤ)] := by
          refine intSum_modEq _ _ _ _ fun i hi => ?_
          have hiSS : elementCenter i ⊂ elementCenter q :=
            ⟨hrp.inside i hi, fun hsub => hrp.proper i hi
              (Set.eq_of_subset_of_subset (hrp.inside i hi) hsub)⟩
          exact ih _ (lt_of_lt_of_le (natCard_lt_of_ssubset hiSS) hqm) i
            (le_refl _)
        have hIH2 : ((∑ j ∈ s₁, starCosetCount j : ℕ) : ℤ)
              ≡ ∑ j ∈ s₁, centerMoebius (elementCenter j) [ZMOD (p : ℤ)] := by
          rw [Nat.cast_sum]
          exact hIHsum
        rw [moebius_split hrp]
        exact hspl.trans (Int.ModEq.neg (Int.ModEq.add_left 1 hIH2))
  exact key (Nat.card ↥(elementCenter g)) g (le_refl _)

/-! ### Theorem `thm: Mob`, item (1) -/

/-- Cardinality form of `cor: z_stars_fin` (tex lines 403-405): with one
representative $j$ per distinct element center contained in $H$,
$$|H| = |\mathbf{Z}(G)| \cdot \left(\sum_{j \in s} \mathrm{sc}(j) + 1\right),$$
i.e. $|H : \mathbf{Z}(G)| = \big(\sum_j \mathrm{sc}(j)\big) + 1$ (tex lines
455-458). Proof: decompose $H$ via `zstars_fin_eq`, add over the disjoint
pieces (`natCard_union_add`, `natCard_biUnion_add`), substitute
`natCard_elementCenterClass_eq_mul` per piece and factor out
$|\mathbf{Z}(G)|$. -/
theorem natCard_eq_sum_starCosetCount [Finite G] {H : Set G}
    (hHmem : H ∈ centralizers G) {s : Finset G}
    (hs_nc : ∀ g ∈ s, g ∉ (Subgroup.center G : Set G))
    (hs_sub : ∀ g ∈ s, elementCenter g ⊆ H)
    (hs_dist : ∀ g ∈ s, ∀ k ∈ s, elementCenter g = elementCenter k → g = k)
    (hs_cov : ∀ x : G, x ∉ (Subgroup.center G : Set G) → elementCenter x ⊆ H →
      ∃ g ∈ s, elementCenter g = elementCenter x) :
    Nat.card ↥H
      = Nat.card ↥(Subgroup.center G) * ((∑ j ∈ s, starCosetCount j) + 1) := by
  classical
  have hdec := zstars_fin_eq hHmem hs_nc hs_sub hs_dist hs_cov
  have hdis := zstars_fin_disjoint hs_nc hs_dist
  have hdU : Disjoint (⋃ j ∈ ((s : Finset G) : Set G), elementCenterClass j)
      ((Subgroup.center G : Set G)) := by
    rw [Set.disjoint_left]
    intro w hw1 hw2
    obtain ⟨j, hjS, hwj⟩ := Set.mem_iUnion₂.mp hw1
    exact Set.disjoint_left.mp (hdis.1 j (Finset.mem_coe.mp hjS)) hwj hw2
  have hpair : ∀ j ∈ s, ∀ k ∈ s, j ≠ k →
      Disjoint (elementCenterClass j) (elementCenterClass k) :=
    fun j hj k hk hne => hdis.2 j hj k hk hne
  rw [hdec, natCard_union_add hdU, natCard_coe_set_eq,
    natCard_biUnion_add s (fun j => elementCenterClass j) hpair,
    Finset.sum_congr rfl fun j _ => natCard_elementCenterClass_eq_mul j,
    ← Finset.mul_sum]
  ring

/-- **Theorem `thm: Mob`, item (1)** of Cocke25-1: for a nonabelian finite
$p$-group, a centralizer $H \in \mathfrak{C}(G)$ properly containing
$\mathbf{Z}(G)$, and representatives whose element centers comprise all
element centers contained in $H$ ("let $\mathbf{Z}(g_1), \dots$ be distinct
and comprise all of the non-central element centers contained in $H$", tex
lines 449-451),
$$\sum_{j \in s} \mu(\mathbf{Z}(j)) \equiv -1 \pmod p$$
(tex lines 469-471). Proof: the counting identity
`natCard_eq_sum_starCosetCount` gives
$p \mid |H:\mathbf{Z}(G)| = (\sum_j \mathrm{sc}(j)) + 1$ (index step via
`exists_pos_index_mul`), while `starCosetCount_modEq_moebius` replaces each
$\mathrm{sc}(j)$ by $\mu(\mathbf{Z}(j))$ modulo $p$.

Source (Section `sec: Moby`, theorem `thm: Mob`, statement tex lines 452-468,
item (1); proof tex lines 469-486):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem centerMoebius_sum_modEq {p : ℕ} [hp : Fact p.Prime] (hpg : IsPGroup p G)
    [Finite G] [Fintype G] {H : Set G} (hHmem : H ∈ centralizers G)
    (hHne : H ≠ (Subgroup.center G : Set G)) {s : Finset G}
    (hs_nc : ∀ g ∈ s, g ∉ (Subgroup.center G : Set G))
    (hs_sub : ∀ g ∈ s, elementCenter g ⊆ H)
    (hs_dist : ∀ g ∈ s, ∀ k ∈ s, elementCenter g = elementCenter k → g = k)
    (hs_cov : ∀ x : G, x ∉ (Subgroup.center G : Set G) → elementCenter x ⊆ H →
      ∃ g ∈ s, elementCenter g = elementCenter x) :
    (∑ j ∈ s, centerMoebius (elementCenter j)) ≡ (-1 : ℤ) [ZMOD ↑p] := by
  classical
  have hcCpos := card_center_pos hpg
  have hKcarr : ((Subgroup.centralizer (centralizerSet H) : Set G)) = H := hHmem
  obtain ⟨k, -, hpdvd, hkcard⟩ := exists_pos_index_mul hpg
    (lt_of_le_of_ne
      (show Subgroup.center G ≤ Subgroup.centralizer (centralizerSet H) from by
        intro x hx
        have hxH : x ∈ H := center_le_of_mem_centralizers hHmem hx
        rwa [← hKcarr] at hxH)
      (fun he => hHne (by rw [← hKcarr, he])))
  have hcnt := natCard_eq_sum_starCosetCount hHmem hs_nc hs_sub hs_dist hs_cov
  have hHK : Nat.card ↥H
      = Nat.card ↥(Subgroup.centralizer (centralizerSet H)) :=
    ((congrArg (fun S : Set G => Nat.card ↥S) hKcarr.symm).trans
      (natCard_coe_set_eq (K := Subgroup.centralizer (centralizerSet H))))
  rw [hHK, hkcard, Nat.mul_comm k (Nat.card ↥(Subgroup.center G))] at hcnt
  have hsum1 : k = (∑ j ∈ s, starCosetCount j) + 1 :=
    mul_left_cancel₀ hcCpos.ne' hcnt
  have hpdvd2 : p ∣ ((∑ j ∈ s, starCosetCount j) + 1) := by
    rw [← hsum1]
    exact hpdvd
  have hspl : (((∑ j ∈ s, starCosetCount j : ℕ) : ℤ)) ≡ (-1 : ℤ) [ZMOD ↑p] :=
    intModEq_of_add_eq_zero (Int.modEq_zero_iff_dvd.mpr (by exact_mod_cast hpdvd2))
  have hsumMod : (((∑ j ∈ s, starCosetCount j : ℕ) : ℤ))
      ≡ ∑ j ∈ s, centerMoebius (elementCenter j) [ZMOD ↑p] := by
    rw [Nat.cast_sum]
    exact intSum_modEq s _ _ _ fun j _ => starCosetCount_modEq_moebius hpg j
  exact hsumMod.symm.trans hspl

/-! ### Canonical form of `thm: Mob` (1) and its dual item (2) -/

/-- The distinct non-central element centers contained in $X$, as a Finset —
the canonical index set of the Möbius sums in `thm: Mob`
($\{Z \in \mathcal{Z}(G) \mid Z \subseteq H\}$, tex line 455). -/
noncomputable def canonCentersBelow [Fintype G] (X : Set G) : Finset (Set G) :=
  (Finset.univ.image fun g : G => elementCenter g).filter
    fun Z => Z ⊆ X ∧ Z ≠ (Subgroup.center G : Set G)

/-- The rep-set sum is independent of the chosen representatives: it equals
the canonical sum over `canonCentersBelow H` ("the $\mathbf{Z}(g_i)$ distinct
and comprising all of the element centers contained in $H$", tex lines
449-451). -/
theorem sum_canonCentersBelow_eq [Fintype G] {H : Set G} {s : Finset G}
    (hs_nc : ∀ g ∈ s, g ∉ (Subgroup.center G : Set G))
    (hs_sub : ∀ g ∈ s, elementCenter g ⊆ H)
    (hs_dist : ∀ g ∈ s, ∀ k ∈ s, elementCenter g = elementCenter k → g = k)
    (hs_cov : ∀ x : G, x ∉ (Subgroup.center G : Set G) → elementCenter x ⊆ H →
      ∃ g ∈ s, elementCenter g = elementCenter x) :
    (∑ j ∈ s, centerMoebius (elementCenter j))
      = (∑ Z ∈ canonCentersBelow H, centerMoebius Z) := by
  classical
  refine Finset.sum_bij (fun j _ => elementCenter j)
    (fun j hj => ?memT)
    (fun a₁ ha₁ a₂ ha₂ => hs_dist a₁ ha₁ a₂ ha₂)
    (fun Z hZ => ?surj)
    (fun _ _ => rfl)
  · refine Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    exact ⟨hs_sub j hj, fun he =>
      hs_nc j hj ((elementCenter_eq_center_iff j).mp he)⟩
  · obtain ⟨g, -, hEq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hZ).1
    have hfilt := (Finset.mem_filter.mp hZ).2
    obtain ⟨a, ha, hac⟩ := hs_cov g
      (fun hm => hfilt.2 (by rw [← hEq]; exact (elementCenter_eq_center_iff g).mpr hm))
      (by rw [hEq]; exact hfilt.1)
    exact ⟨a, ha, hac.trans hEq⟩

/-- Canonical form of `thm: Mob` item (1): the Möbius sum over the distinct
non-central element centers contained in $H$ is $-1 \bmod p$ (tex lines
452-456, 469-471). -/
theorem centerMoebius_sum_modEq_canon {p : ℕ} [hp : Fact p.Prime]
    (hpg : IsPGroup p G) [Finite G] [Fintype G] {H : Set G}
    (hHmem : H ∈ centralizers G) (hHne : H ≠ (Subgroup.center G : Set G)) :
    (∑ Z ∈ canonCentersBelow H, centerMoebius Z) ≡ (-1 : ℤ) [ZMOD ↑p] := by
  classical
  obtain ⟨s₀, hs₀nc, hs₀sub, hs₀dist, hs₀cov⟩ := exists_zstars_reps (H := H)
  rw [← sum_canonCentersBelow_eq hs₀nc hs₀sub hs₀dist hs₀cov]
  exact centerMoebius_sum_modEq hpg hHmem hHne hs₀nc hs₀sub hs₀dist hs₀cov

/-- If $\mathbf{C}_G(H) = \mathbf{Z}(G)$ for $H \in \mathfrak{C}(G)$ then
$H = G$: the contrapositive supplying the "properly contains
$\mathbf{Z}(G)$" hypothesis of `thm: Mob` (1) at the dual centralizer
(tex line 461). -/
theorem eq_univ_of_centralizerSet_eq_center {H : Set G}
    (hHmem : H ∈ centralizers G)
    (he : centralizerSet H = (Subgroup.center G : Set G)) : H = Set.univ := by
  have hfix : cclosure H = H := hHmem
  rw [← hfix]
  show centralizerSet (centralizerSet H) = Set.univ
  rw [he]
  apply Set.eq_univ_of_forall
  intro w _
  exact fun hm => (Subgroup.mem_center_iff.mp hm w).symm

/-- Duality bridge behind `thm: Mob` (2) (tex lines 461-462, via `cor: bij`
/ `prop: cent_basic` (3)): for $H \in \mathfrak{C}(G)$,
$$H \subseteq \mathbf{C}_G(x) \iff \mathbf{Z}(x) \subseteq \mathbf{C}_G(H).$$ -/
theorem elemCentralizer_ge_iff_center_le {H : Set G} (hHmem : H ∈ centralizers G)
    {x : G} : H ⊆ centralizerSet {x} ↔ elementCenter x ⊆ centralizerSet H :=
  ⟨fun h => centralizerSet_mono h, fun h => by
    have h3 : centralizerSet (centralizerSet H)
        ⊆ centralizerSet (elementCenter x) := centralizerSet_mono h
    rwa [show centralizerSet (centralizerSet H) = H from hHmem,
      show centralizerSet (elementCenter x) = centralizerSet {x} from
        centralizerSet_triple ({x} : Set G)] at h3⟩

/-- **Theorem `thm: Mob`, item (2)** (tex lines 459-462), equivalently the
introduction restatement `intro: Mob` (tex lines 78-81): with $H \in
\mathfrak{C}(G)$ properly contained in $G$, the Möbius sum over the element
centers contained in $\mathbf{C}_G(H)$ is $-1 \bmod p$. By the duality bridge
(`elemCentralizer_ge_iff_center_le`, `cor: bij`) these centers are exactly
the $\mu(\mathbf{Z}(\mathbf{C}_G(g)))$ for element centralizers
$\mathbf{C}_G(g)$ with $H \subseteq \mathbf{C}_G(g) \subset G$. Proof: item
(1) at $\mathbf{C}_G(H)$, which properly contains $\mathbf{Z}(G)$ since
otherwise $H = \mathbf{C}_G(\mathbf{Z}(G)) = G$
(`eq_univ_of_centralizerSet_eq_center`).

Source (Section `sec: Moby`, theorem `thm: Mob` item (2); Introduction
theorem `intro: Mob`, tex lines 78-81):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem centerMoebius_dual_sum_modEq {p : ℕ} [hp : Fact p.Prime]
    (hpg : IsPGroup p G) [Finite G] [Fintype G] {H : Set G}
    (hHmem : H ∈ centralizers G) (hHne : H ≠ Set.univ) :
    (∑ Z ∈ canonCentersBelow (centralizerSet H), centerMoebius Z)
      ≡ (-1 : ℤ) [ZMOD ↑p] :=
  centerMoebius_sum_modEq_canon hpg (centralizerSet_mem_centralizers _)
    (fun he => hHne (eq_univ_of_centralizerSet_eq_center hHmem he))

/-! ### $F$-groups (`cor: non_ab_F-Gp`, tex lines 470-487) -/

/-- An $F$-group (Rebmann; tex line 470, dual center form tex line 472):
comparable non-central element centers coincide. -/
def IsFGroup (G : Type*) [Group G] : Prop :=
  ∀ x y : G, x ∉ (Subgroup.center G : Set G) → y ∉ (Subgroup.center G : Set G) →
    elementCenter x ⊆ elementCenter y → elementCenter x = elementCenter y

/-- In an $F$-group every non-central element center has Möbius value $-1$
(tex line 474): the only element center properly below $\mathbf{Z}(g)$ is
$\hat 0 = \mathbf{Z}(G)$, so the recurrence collapses to
$\mu(\mathbf{Z}(g)) = -\mu(\hat 0)$. -/
theorem centerMoebius_eq_neg_one [Finite G] [Fintype G] (hf : IsFGroup G)
    {g : G} (hg : g ∉ (Subgroup.center G : Set G)) :
    centerMoebius (elementCenter g) = -1 := by
  classical
  have hc1 : elementCenter (1 : G) = (Subgroup.center G : Set G) :=
    (elementCenter_eq_center_iff 1).mpr (Subgroup.one_mem _)
  have hcsub1 : elementCenter (1 : G) ⊆ elementCenter g := by
    rw [hc1]
    exact center_subset_elementCenter g
  have hcne1 : ¬(elementCenter g ⊆ elementCenter (1 : G)) := fun hs =>
    hg ((elementCenter_eq_center_iff g).mp
      (Set.eq_of_subset_of_subset (hs.trans (le_of_eq hc1))
        (center_subset_elementCenter g)))
  have hcpi : centerProperInside (elementCenter g)
      = insert (Subgroup.center G : Set G) (∅ : Finset (Set G)) := by
    ext Y
    rw [mem_centerProperInside, Finset.mem_insert]
    constructor
    · rintro ⟨j, hEqY, hSS⟩
      rcases eq_or_ne (elementCenter j) (Subgroup.center G : Set G) with hc | hc
      · left
        rw [← hEqY, hc]
      · right
        exact absurd (hf j g
          (fun hm => hc ((elementCenter_eq_center_iff j).mpr hm)) hg
            hSS.1).symm.le hSS.2
    · rintro (hY | hY)
      · exact ⟨(1 : G), hc1.trans hY.symm, ⟨hcsub1, hcne1⟩⟩
      · exact absurd hY (by simp)
  have hne : elementCenter g ≠ (Subgroup.center G : Set G) := fun he =>
    hg ((elementCenter_eq_center_iff g).mp he)
  rw [centerMoebius_eq_neg_sum (hX := ⟨g, rfl⟩) hne, hcpi, Finset.sum_insert (by simp),
    Finset.sum_empty, add_zero, centerMoebius_center]

/-- Corollary `cor: non_ab_F-Gp` (1) (tex lines 476-480): in a finite
$p$-group that is an $F$-group, the number of non-central element centers
contained in any $H \in \mathfrak{C}(G)$, $H \neq \mathbf{Z}(G)$, is
congruent to $1$ modulo $p$. Item (2) is the same statement read through the
duality bridge (`elemCentralizer_ge_iff_center_le`), counting proper element
centralizers containing $H$.

Source (Section `sec: Moby`, corollary `cor: non_ab_F-Gp`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem card_canonCentersBelow_modEq {p : ℕ} [hp : Fact p.Prime]
    (hpg : IsPGroup p G) (hf : IsFGroup G) [Finite G] [Fintype G] {H : Set G}
    (hHmem : H ∈ centralizers G) (hHne : H ≠ (Subgroup.center G : Set G)) :
    (((canonCentersBelow H).card : ℕ) : ℤ) ≡ 1 [ZMOD ↑p] := by
  classical
  have hsum := centerMoebius_sum_modEq_canon hpg hHmem hHne
  have hall : ∀ Z ∈ canonCentersBelow H, centerMoebius Z = (-1 : ℤ) := by
    intro Z hZ
    obtain ⟨g, -, hEq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hZ).1
    have hfilt := (Finset.mem_filter.mp hZ).2
    rw [← hEq]
    refine centerMoebius_eq_neg_one hf fun hm => ?_
    exact hfilt.2 (by rw [← hEq]; exact (elementCenter_eq_center_iff g).mpr hm)
  have hSeq : ∀ t : Finset (Set G),
      (∀ Z ∈ t, centerMoebius Z = (-1 : ℤ)) →
      ((∑ Z ∈ t, centerMoebius Z) : ℤ) = -((t.card : ℕ) : ℤ) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | insert a t haS ih =>
        intro hall
        rw [Finset.sum_insert haS,
          ih fun Z hZ => hall Z (Finset.mem_insert_of_mem hZ),
          Finset.card_insert_of_notMem haS]
        push_cast
        rw [neg_add, hall a (Finset.mem_insert_self _ _)]
        ring
  rw [hSeq (canonCentersBelow H) hall] at hsum
  simpa using Int.ModEq.neg hsum

/-! ### Centralizer graph (unlabeled proposition part (3), `cor: cent_graph_degree`)

Encoding delta: the centralizer graph $\Gamma_{\mathcal{Z}}(G)$ is captured
through its vertex-neighbor data rather than a `SimpleGraph` instance — the
proposition's content is the neighbor description below and the counting in
`centralizerGraphDegree_modEq`; vertices are the distinct non-central element
centers (`canonCentersBelow Set.univ`). -/

/-- Neighbors of the vertex $\mathbf{Z}(g)$ in the centralizer graph
$\Gamma_{\mathcal{Z}}(G)$ — part (3) of the unlabeled proposition, tex lines
509-511:
$$N(\mathbf{Z}(g)) = \{\mathbf{Z}(y) \in \mathcal{Z}(G) \mid \mathbf{Z}(y)
\subseteq \mathbf{C}_G(g)\} \setminus \{\mathbf{Z}(g)\}.$$ -/
noncomputable def centralizerGraphNbrs [Fintype G] (g : G) : Finset (Set G) :=
  (canonCentersBelow (centralizerSet {g})).erase (elementCenter g)

/-- Membership characterization of part (3)'s neighbor set. -/
theorem mem_centralizerGraphNbrs [Fintype G] {g : G}
    (_hg : g ∉ (Subgroup.center G : Set G)) {Z : Set G} :
    Z ∈ centralizerGraphNbrs g ↔
      (∀ z ∈ Z, z * g = g * z) ∧
        (∃ y : G, y ∉ (Subgroup.center G : Set G) ∧ elementCenter y = Z) ∧
        Z ≠ elementCenter g := by
  classical
  have hgself : g ∈ centralizerSet {g} :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff.mp hw]
  constructor
  · intro hmem
    obtain ⟨hne, hcanon⟩ := Finset.mem_erase.mp hmem
    obtain ⟨himg, hfilt⟩ := Finset.mem_filter.mp hcanon
    obtain ⟨y, -, hyEq⟩ := Finset.mem_image.mp himg
    refine ⟨fun z hz => ?_, ⟨y, fun hm => ?_, hyEq⟩, hne⟩
    · exact (Subgroup.mem_centralizer_iff.mp (hfilt.1 hz) g
        (Set.mem_singleton_iff.mpr rfl)).symm
    · exact hfilt.2 (by rw [← hyEq]; exact (elementCenter_eq_center_iff y).mpr hm)
  · rintro ⟨hcomm, ⟨y, hync, hyEq⟩, hne⟩
    refine Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hyEq⟩,
        ⟨fun z hz => Subgroup.mem_centralizer_iff.mpr fun w hw => by
          rw [Set.mem_singleton_iff.mp hw]
          exact (hcomm z hz).symm,
          fun hc => hync ((elementCenter_eq_center_iff y).mp (hyEq.trans hc))⟩⟩⟩

/-- Degree of the vertex $\mathbf{Z}(g)$ (part (3)): one less than the number
of non-central element centers contained in $\mathbf{C}_G(g)$. -/
theorem card_centralizerGraphNbrs [Fintype G] {g : G}
    (hg : g ∉ (Subgroup.center G : Set G)) :
    (centralizerGraphNbrs g).card
      = (canonCentersBelow (centralizerSet {g})).card - 1 := by
  classical
  have hgself : g ∈ centralizerSet {g} :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff.mp hw]
  have hmem : elementCenter g ∈ canonCentersBelow (centralizerSet {g}) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩,
        ⟨fun z hz => Subgroup.mem_centralizer_iff.mpr fun w hw => by
          rw [Set.mem_singleton_iff.mp hw]
          exact Subgroup.mem_centralizer_iff.mp hz g hgself,
          fun hc => hg ((elementCenter_eq_center_iff g).mp hc)⟩⟩
  rw [centralizerGraphNbrs]
  exact Finset.card_erase_of_mem hmem

/-- **Corollary `cor: cent_graph_degree`** (tex lines 517-523): in a finite
$p$-group that is an $F$-group, the degree of every vertex
$\mathbf{Z}(g)$ of the centralizer graph $\Gamma_{\mathcal{Z}}(G)$ is
congruent to $0$ modulo $p$. Proof: the vertex count of `thm: Mob` (1)
(`card_canonCentersBelow_modEq`) at $H = \mathbf{C}_G(g)$ is $\equiv 1$
($\mathbf{C}_G(g) \neq \mathbf{Z}(G)$ since $g$ lies in the former but not
the latter); subtracting the removed self-vertex gives $\equiv 0$.

Source (Section `sec: Moby`, corollary `cor: cent_graph_degree`;
Introduction `intro: cent_graph_degree`, tex lines 85-87):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem centralizerGraphDegree_modEq {p : ℕ} [hp : Fact p.Prime]
    (hpg : IsPGroup p G) (hf : IsFGroup G) [Finite G] [Fintype G] {g : G}
    (hg : g ∉ (Subgroup.center G : Set G)) :
    (((centralizerGraphNbrs g).card : ℕ) : ℤ) ≡ 0 [ZMOD ↑p] := by
  classical
  have hgself : g ∈ centralizerSet {g} :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff.mp hw]
  have hcC := card_canonCentersBelow_modEq hpg hf
    (centralizerSet_mem_centralizers ({g} : Set G))
    (fun he => hg (by rw [← he]; exact hgself))
  have hmem : elementCenter g ∈ canonCentersBelow (centralizerSet {g}) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩,
        ⟨fun z hz => Subgroup.mem_centralizer_iff.mpr fun w hw => by
          rw [Set.mem_singleton_iff.mp hw]
          exact Subgroup.mem_centralizer_iff.mp hz g hgself,
          fun hc => hg ((elementCenter_eq_center_iff g).mp hc)⟩⟩
  have hcpos : 0 < (canonCentersBelow (centralizerSet {g})).card :=
    Finset.card_pos.mpr ⟨elementCenter g, hmem⟩
  have hdvd := hcC.dvd
  have h2 := Int.dvd_neg.mpr hdvd
  rw [neg_sub] at h2
  rw [centralizerGraphNbrs, Finset.card_erase_of_mem hmem,
    Nat.cast_sub (by omega), Int.modEq_zero_iff_dvd]
  exact h2

/-! ### Commuting graph and transversal subgraph (parts (1)-(2)) -/

omit [Group G] in
/-- Cardinality bridge: filtering $G$ by membership in $S \subseteq G$
recovers $|S|$ — the reading of $|\mathbf{C}_G(x)|$ in tex lines 507/512. -/
theorem card_filter_mem_set_eq [Fintype G] (S : Set G) :
    (Finset.univ.filter fun y : G => y ∈ S).card = Nat.card ↥S := by
  classical
  haveI := (Set.toFinite S).fintype
  rw [Nat.card_eq_fintype_card]
  refine Finset.card_bij (fun y hy => ⟨y, by simpa using hy⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun _ _ _ _ h => congrArg Subtype.val h)
    fun b _ => ⟨b.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.property⟩,
      rfl⟩

/-- Part (1) of the unlabeled proposition (tex lines 503-505): neighbors of
$x$ in the commuting graph $\mathfrak{G}(G)$:
$$N(x) = (\mathbf{C}_G(\{x\}) \setminus \{x\}) \setminus \mathbf{Z}(G).$$ -/
noncomputable def commutingGraphNbrs [Fintype G] (x : G) : Finset G :=
  (Finset.univ.filter fun y : G => y ∈ centralizerSet {x} ∧
    y ∉ (Subgroup.center G : Set G)).erase x

theorem mem_commutingGraphNbrs [Fintype G] {x y : G} :
    y ∈ commutingGraphNbrs x ↔
      y * x = x * y ∧ y ≠ x ∧ y ∉ (Subgroup.center G : Set G) := by
  classical
  have hxself : x ∈ centralizerSet {x} :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff.mp hw]
  constructor
  · intro hmem
    obtain ⟨hne, hcanon⟩ := Finset.mem_erase.mp hmem
    obtain ⟨-, hyC, hy⟩ := Finset.mem_filter.mp hcanon
    exact ⟨(Subgroup.mem_centralizer_iff.mp hyC x
        (Set.mem_singleton_iff.mpr rfl)).symm, hne, hy⟩
  · rintro ⟨hcomm, hne, hy⟩
    refine Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_, hy⟩⟩
    rw [Set.mem_singleton_iff.mp hw]
    exact hcomm.symm

/-- Part (2) of the unlabeled proposition (tex lines 507-509): neighbors of
$x$ in the induced subgraph $\mathfrak{G}^*(G)$ on a transversal $T$:
$$N(x) = (\mathbf{C}_G(\{x\}) \cap T) \setminus (\{x\} \cup
(\mathbf{Z}(G) \cap T)).$$ -/
noncomputable def transversalGraphNbrs [Fintype G] (T : Finset G) (x : G) :
    Finset G :=
  (T.filter fun y : G => y ∈ centralizerSet {x} ∧
    y ∉ (Subgroup.center G : Set G)).erase x

/-- Degree of $x$ in $\mathfrak{G}(G)$ (part (1), tex lines 505-507):
$$\deg x = |\mathbf{C}_G(\{x\})| - |\mathbf{Z}(G)| - 1.$$ -/
theorem card_commutingGraphNbrs [Fintype G] {x : G}
    (hx : x ∉ (Subgroup.center G : Set G)) :
    (commutingGraphNbrs x).card
      = Nat.card ↥(centralizerSet {x}) - Nat.card ↥(Subgroup.center G) - 1 := by
  classical
  have hgself : x ∈ centralizerSet {x} :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff.mp hw]
  have hxmem : x ∈ Finset.univ.filter
      (fun y : G => y ∈ centralizerSet {x} ∧ y ∉ (Subgroup.center G : Set G)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgself, hx⟩
  have hBeq : (Finset.univ.filter fun y : G => y ∈ centralizerSet {x} ∧
      y ∈ (Subgroup.center G : Set G))
      = Finset.univ.filter fun y : G => y ∈ (Subgroup.center G : Set G) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => h.2, fun h => ⟨fun w hw => ?_, h⟩⟩
    rw [Set.mem_singleton_iff.mp hw]
    exact Subgroup.mem_center_iff.mp h x
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (p := fun y : G => y ∈ (Subgroup.center G : Set G))
    (s := Finset.univ.filter fun y : G => y ∈ centralizerSet {x})
  rw [Finset.filter_filter, Finset.filter_filter, hBeq,
    card_filter_mem_set_eq ((Subgroup.center G : Set G)), natCard_coe_set_eq,
    card_filter_mem_set_eq (centralizerSet {x})] at hsplit
  have hprepos : 0 < (Finset.univ.filter (fun y : G => y ∈ centralizerSet {x} ∧
      y ∉ (Subgroup.center G : Set G))).card :=
    Finset.card_pos.mpr ⟨x, hxmem⟩
  have hf0 : (commutingGraphNbrs x).card + 1
      = (Finset.univ.filter (fun y : G => y ∈ centralizerSet {x} ∧
          y ∉ (Subgroup.center G : Set G))).card := by
    rw [commutingGraphNbrs, Finset.card_erase_of_mem hxmem]
    omega
  have hz1 : ((Nat.card ↥(Subgroup.center G) : ℕ) : ℤ)
      + (((Finset.univ.filter (fun y : G =>
          y ∈ centralizerSet {x} ∧ y ∉ (Subgroup.center G : Set G))).card : ℕ) : ℤ)
      = ((Nat.card ↥(centralizerSet {x}) : ℕ) : ℤ) := by
    exact_mod_cast hsplit
  have hz2 : (((commutingGraphNbrs x).card : ℕ) : ℤ) + 1
      = (((Finset.univ.filter (fun y : G =>
          y ∈ centralizerSet {x} ∧ y ∉ (Subgroup.center G : Set G))).card : ℕ) : ℤ) := by
    exact_mod_cast hf0
  omega

/-- Degree of $x$ in $\mathfrak{G}^*(G)$ (part (2), tex lines 509-512): two
less than $|\mathbf{C}_G(\{x\}) \cap T|$; under full transversality of $T$
that count is the index $|\mathbf{C}_G(x):\mathbf{Z}(G)|$ (encoding delta:
the coset-representative correspondence is left implicit). -/
theorem card_transversalGraphNbrs [Fintype G] {T : Finset G} {x : G}
    (hxT : x ∈ T) (hx : x ∉ (Subgroup.center G : Set G))
    (hc1 : (T.filter fun y : G => y ∈ (Subgroup.center G : Set G)).card = 1) :
    (transversalGraphNbrs T x).card
      = (T.filter fun y : G => y ∈ centralizerSet {x}).card - 2 := by
  classical
  have hgself : x ∈ centralizerSet {x} :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff.mp hw]
  have hxmem : x ∈ T.filter
      (fun y : G => y ∈ centralizerSet {x} ∧ y ∉ (Subgroup.center G : Set G)) :=
    Finset.mem_filter.mpr ⟨hxT, ⟨hgself, hx⟩⟩
  have hBeq : (T.filter fun y : G => y ∈ centralizerSet {x} ∧
      y ∈ (Subgroup.center G : Set G))
      = T.filter fun y : G => y ∈ (Subgroup.center G : Set G) := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, Subgroup.mem_centralizer_iff.mpr fun w hw => by
        rw [Set.mem_singleton_iff.mp hw]
        exact Subgroup.mem_center_iff.mp h.2 x, h.2⟩
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (p := fun y : G => y ∈ (Subgroup.center G : Set G))
    (s := T.filter fun y : G => y ∈ centralizerSet {x})
  rw [Finset.filter_filter, Finset.filter_filter, hBeq, hc1] at hsplit
  have hprepos : 0 < (T.filter (fun y : G => y ∈ centralizerSet {x} ∧
      y ∉ (Subgroup.center G : Set G))).card :=
    Finset.card_pos.mpr ⟨x, hxmem⟩
  have hf0 : (transversalGraphNbrs T x).card + 1
      = (T.filter (fun y : G => y ∈ centralizerSet {x} ∧
          y ∉ (Subgroup.center G : Set G))).card := by
    rw [transversalGraphNbrs, Finset.card_erase_of_mem hxmem]
    omega
  omega

end Cocke25_1
