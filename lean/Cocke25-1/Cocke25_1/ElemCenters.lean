import Cocke25_1.Basic
import Cocke25_1.Fibers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! # Element centers and reduced generating sets

Formalization of Cocke25-1 (*A Möbius function on the Centralizer Lattice*,
arXiv:2512.13839v2), Section `sec: elems` (`lem: sub` lives in
`CentLattice.lean`):

- Proposition `prop: cent_ab`: $\mathbf{C}_G^2(S)$ is abelian iff
  $\langle S \rangle$ is abelian;
- Corollary `cor: abelian_cent`: $\mathbf{Z}(a) = \mathbf{C}_G^2(a)$ is
  abelian, indeed $\mathbf{Z}(a) = \mathbf{Z}(\mathbf{C}_G(a))$;
- Proposition `prop: g_in_Z`: $\mathbf{Z}^*(g) \subseteq \mathbf{Z}(g)$;
- key step of Lemma `lem: cen_divides_stars`: $\mathbf{C}_G(xz) =
  \mathbf{C}_G(x)$ for $z \in \mathbf{Z}(G)$;
- Propositions `prop: upper` and `prop: stars` via an abstract representative
  set $X$.

Note: mathlib master (post v4.24.0) has `Subgroup.centralizer_closure`,
`Subgroup.isMulCommutative_closure`, and `Commute.zpow_zpow_self`, which would
shorten some proofs; the pinned release lacks them (see `status.md`).
-/

namespace Cocke25_1

variable {G : Type*} [Group G]

/-- Proposition `prop: cent_ab` of Cocke25-1: $\mathbf{C}_G(\mathbf{C}_G(S))$ is
abelian if and only if $\langle S \rangle$ is abelian ("abelian" encoded as
pairwise commutativity over the carrier; encoding delta recorded in
`status.md`).

Forward direction follows the paper's bridge (tex line 362): pairwise
commutation on $\langle S \rangle$ restricts to $S$, so $S \subseteq
\mathbf{C}_G(S)$, hence $\mathbf{C}_G^2(S) \subseteq \mathbf{C}_G(S)$ by `lem:
contain`; an $x \in \mathbf{C}_G^2(S)$ then commutes with any $y \in
\mathbf{C}_G^2(S) \subseteq \mathbf{C}_G(S)$. Backward direction: pairwise
commutation on $\mathbf{C}_G^2(S)$ restricts to $S$ by extensivity
(`subset_cclosure`); each $c \in S$ then centralizes all of $\langle S \rangle$,
so $\langle S \rangle$ centralizes its own members.

Source (Section `sec: elems`, proposition `prop: cent_ab`, statement tex lines
357-359, proof tex lines 361-363):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem cclosure_abelian_iff (S : Set G) :
    (∀ x ∈ cclosure S, ∀ y ∈ cclosure S, x * y = y * x) ↔
      (∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x) := by
  constructor
  · intro h x hx y hy
    have hSS : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := fun s hs t ht =>
      h s (subset_cclosure S hs) t (subset_cclosure S ht)
    have hcent : ∀ c ∈ S, Subgroup.closure S ≤ Subgroup.centralizer {c} :=
      fun c hc =>
        (Subgroup.closure_le _).mpr fun s hs =>
          Subgroup.mem_centralizer_iff.mpr fun z hz =>
            by
              rw [Set.mem_singleton_iff.mp hz]
              exact (hSS s hs c hc).symm
    have hM : S ⊆ centralizerSet (↑(Subgroup.closure S) : Set G) := fun c hc =>
      Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (Subgroup.mem_centralizer_iff.mp ((hcent c hc) hu) c rfl).symm
    have hK : Subgroup.closure S ≤
        Subgroup.centralizer (↑(Subgroup.closure S) : Set G) :=
      (Subgroup.closure_le _).mpr hM
    exact Subgroup.mem_centralizer_iff.mp (hK hy) x hx
  · intro h x hx y hy
    have hSS : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := fun s hs t ht =>
      h s (Subgroup.subset_closure hs) t (Subgroup.subset_closure ht)
    have hSCS : S ⊆ centralizerSet S := fun s hs =>
      Subgroup.mem_centralizer_iff.mpr fun t ht => hSS t ht s hs
    have hx' : x ∈ centralizerSet S := centralizerSet_mono hSCS hx
    exact Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hy) x hx'

/-- Corollary `cor: abelian_cent` of Cocke25-1: the element center
$\mathbf{Z}(a) = \mathbf{C}_G(\mathbf{C}_G(a))$ is abelian ("Since
$\mathbf{C}_G(\mathbf{C}_G(a))$ is abelian", tex line 371), via `prop: cent_ab`
with $S = \{a\}$: $\langle \{a\} \rangle$ consists of powers of $a$
(`Subgroup.mem_closure_singleton`), which commute since $a$ commutes with
itself (`Commute.zpow_zpow`).

Source (Section `sec: elems`, corollary `cor: abelian_cent`, tex lines
367-371):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem elementCenter_abelian (a : G) :
    ∀ x ∈ elementCenter a, ∀ y ∈ elementCenter a, x * y = y * x :=
  (cclosure_abelian_iff {a}).mpr <| by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_closure_singleton.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.mp hy
    exact Commute.zpow_zpow (Commute.refl a) m n

/-- Proposition `prop: g_in_Z` of Cocke25-1: $\mathbf{Z}^*(g) \subseteq
\mathbf{Z}(g)$ ("If $x \in \mathbf{Z}^*(g)$, then $x \in \mathbf{Z}(x) =
\mathbf{Z}(g)$", tex line 382), with $x \in \mathbf{Z}(x)$ by extensivity.

Source (Section `sec: elems`, proposition `prop: g_in_Z`, statement tex lines
377-379, proof tex lines 381-383):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem elementCenterClass_subset_elementCenter (g : G) :
    elementCenterClass g ⊆ elementCenter g := fun x hx =>
  hx ▸ subset_cclosure {x} (Set.mem_singleton_iff.mpr rfl)

/-! ### Toward `lem: cen_divides_stars` -/

/-- Key algebraic step of Lemma `lem: cen_divides_stars` of Cocke25-1
("$\mathbf{C}_G(x) = \mathbf{C}_G(xz)$ for every $z \in \mathbf{Z}(G)$", tex
line 416): multiplying an element by a central one does not change its element
centralizer. Cancellation after re-associating with $z$ on the right.

Source (Section `sec: Moby`, lemma `lem: cen_divides_stars`, proof tex line
416):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem centralizerSet_mul_center (x : G) {z : G} (hz : z ∈ Subgroup.center G) :
    centralizerSet {x * z} = centralizerSet {x} := by
  have hzc : ∀ w : G, w * z = z * w := Subgroup.mem_center_iff.mp hz
  ext y
  simp only [centralizerSet, SetLike.mem_coe, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  have hinj : Function.Injective fun t : G => t * z := fun a b hab => by
    simpa only [mul_inv_cancel_right] using congrArg (fun t => t * z⁻¹) hab
  constructor
  · intro h
    refine hinj ?_
    calc (x * y) * z = x * (y * z) := mul_assoc x y z
      _ = x * (z * y) := by rw [hzc y]
      _ = (x * z) * y := (mul_assoc x z y).symm
      _ = y * (x * z) := h
      _ = y * x * z := (mul_assoc y x z).symm
  · intro h
    calc (x * z) * y = x * (z * y) := mul_assoc x z y
      _ = x * (y * z) := by rw [hzc y]
      _ = x * y * z := (mul_assoc x y z).symm
      _ = y * x * z := by rw [h]
      _ = y * (x * z) := mul_assoc y x z

/-- Multiplying by a central element preserves the $\mathbf{Z}^*$ class: for
$x \in \mathbf{Z}^*(g)$ and $z \in \mathbf{Z}(G)$ one has $xz \in
\mathbf{Z}^*(g)$ ("if $x \in \mathbf{Z}^*(g)$, then $x\,\mathbf{Z}(G) \subseteq
\mathbf{Z}^*(g)$ ... $\mathbf{C}_G(x) = \mathbf{C}_G(xz)$", tex line 416); the
converse holds by symmetry of the same identity.

Source (Section `sec: Moby`, lemma `lem: cen_divides_stars`, proof tex line
416):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem mem_elementCenterClass_mul_center {g x z : G}
    (hx : x ∈ elementCenterClass g) (hz : z ∈ Subgroup.center G) :
    x * z ∈ elementCenterClass g :=
  Set.mem_setOf.mpr <| by
    unfold elementCenter cclosure
    rw [centralizerSet_mul_center x hz]
    exact hx

/-! ### `prop: upper` and `prop: stars` (Section `sec: elems`)

The representative set $X$ (tex line 318) is kept abstract: any $X \subseteq G$
meeting every $\mathbf{Z}^*$-equivalence class, encoded as
`hX : ∀ y : G, ∃ x ∈ X, elementCenter x = elementCenter y`. -/

/-- The set $U_H^* = \{ x \in X \mid H \subseteq \mathbf{C}_G(x) \}$ ("The $U$
stands for `upper'", tex line 320). -/
def upperStars (X H : Set G) : Set G :=
  {x | x ∈ X ∧ H ⊆ centralizerSet {x}}

/-- The restricted fiber $\mathfrak{F}_H^* = \{ T \subseteq X \mid
\mathbf{C}_G(T) = H \}$ (tex line 318). -/
def starFiber (X H : Set G) : Set (Set G) :=
  {T | T ⊆ X ∧ centralizerSet T = H}

theorem mem_upperStars {X H : Set G} {x : G} :
    x ∈ upperStars X H ↔ x ∈ X ∧ H ⊆ centralizerSet {x} := Iff.rfl

theorem mem_starFiber {X H T : Set G} :
    T ∈ starFiber X H ↔ T ⊆ X ∧ centralizerSet T = H := Iff.rfl

theorem starFiber_subset_X {H X T : Set G} (hT : T ∈ starFiber X H) : T ⊆ X :=
  (mem_starFiber.mp hT).1

theorem starFiber_eq {H X T : Set G} (hT : T ∈ starFiber X H) :
    centralizerSet T = H :=
  (mem_starFiber.mp hT).2
/-- Helper used throughout Section `sec: elems` ("$H = \mathbf{C}_G(\mathbf{C}_G(H))
= \bigcap_{x \in \mathbf{C}_G(H)} \mathbf{C}_G(x)$", tex line 328):
$\mathbf{C}_G(T)$ is determined by the singleton centralizers of its elements. -/
theorem centralizerSet_eq_iInter_singletons (T : Set G) :
    centralizerSet T = {x | ∀ t ∈ T, x ∈ centralizerSet {t}} := by
  ext x
  constructor
  · intro hx t ht
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
      rw [Set.mem_singleton_iff.mp hw]
      exact Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hx) t ht
  · intro hx w hw
    exact Subgroup.mem_centralizer_iff.mp (hx w hw) w rfl

/-- Bridge between the two directions of `prop: Galois` for singleton tests:
$S \subseteq \mathbf{C}_G(\{x\}) \iff x \in \mathbf{C}_G(S)$. -/
theorem subset_singleton_centralizerSet_iff {S : Set G} {x : G} :
    S ⊆ centralizerSet {x} ↔ x ∈ centralizerSet S :=
  (centralizer_galois_self_iff {x} S).trans
    ⟨fun h => h rfl, fun h => Set.singleton_subset_iff.mpr h⟩

/-- Proposition `prop: upper` of Cocke25-1: for $H \in \mathfrak{C}(G)$,
$H = \mathbf{C}_G(U_H^*)$. Forward direction: members of $U_H^*$ lie in
$\mathbf{C}_G(H)$ ("$x \in \mathbf{C}_G(H) \iff H = \mathbf{C}_G(\mathbf{C}_G(H))
\subseteq \mathbf{C}_G(x)$", tex line 330), and $H = \mathbf{C}_G^2(H)$
commutes with all of them. Backward direction: given $t \in \mathbf{C}_G(H)$,
its representative $x \in X$ has the same singleton centralizer (`prop:
equiv_C-CC` route), so $y \in \mathbf{C}_G(U_H^*)$ commutes with $t$ (tex lines
333-334).

Source (Section `sec: elems`, proposition `prop: upper`, statement tex lines
322-324, proof tex lines 326-335):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem centralizerSet_upper {H : Set G} (hH : H ∈ centralizers G)
    {X : Set G} (hX : ∀ y : G, ∃ x ∈ X, elementCenter x = elementCenter y) :
    H = centralizerSet (upperStars X H) := by
  have hHeq : cclosure H = H := hH
  apply Set.eq_of_subset_of_subset
  · intro x hx u hu
    rw [mem_upperStars] at hu
    obtain ⟨-, hu2⟩ := hu
    have hxu : x ∈ centralizerSet {u} := hu2 hx
    have hcu : u ∈ centralizerSet H :=
      ((centralizer_galois_self_iff {u} H).mp hu2) rfl
    rw [← hHeq] at hx
    exact Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hx) u hcu
  · intro y hy
    rw [← hHeq]
    show y ∈ centralizerSet (centralizerSet H)
    refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
    obtain ⟨x, hxX, hxc⟩ := hX t
    have hxt : centralizerSet {x} = centralizerSet {t} :=
      centralizerSet_eq_iff_cclosure_eq.mpr hxc
    have hxU : x ∈ upperStars X H :=
      mem_upperStars.mpr ⟨hxX, fun w hw => by
        rw [hxt]
        refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
        rw [Set.mem_singleton_iff.mp hz]
        exact (Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp ht) w hw).symm⟩
    have hxy : x * y = y * x :=
      Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hy) x hxU
    have hyCx : y ∈ centralizerSet {t} := by
      rw [← hxt]
      exact Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact hxy
    exact Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hyCx) t rfl

/-- Proposition `prop: stars`, item (1), closure half of Cocke25-1:
$\mathfrak{F}_H^*$ is closed under arbitrary nonempty unions — via `prop:
cent_union_int_1` item (1), as in the paper's proof (tex line 350, citing
Proposition `prop: cent_union_int_1`). Family nonemptiness explicit (encoding
delta; see `status.md`).

Source (Section `sec: elems`, proposition `prop: stars`, statement tex lines
339-344, proof tex lines 347-350):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem starFiber_sUnion_mem {H X : Set G} {W : Set (Set G)}
    (hne : W.Nonempty) (hW : ∀ T ∈ W, T ∈ starFiber X H) :
    ⋃₀ W ∈ starFiber X H := by
  refine ⟨Set.sUnion_subset fun T hT => starFiber_subset_X (hW T hT), ?_⟩
  rw [centralizerSet_sUnion]
  obtain ⟨W0, hW0⟩ := hne
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro x hx
    have hx0 : x ∈ centralizerSet W0 :=
      (Set.mem_sInter.mp hx) (centralizerSet W0) ⟨W0, hW0, rfl⟩
    rwa [starFiber_eq (hW W0 hW0)] at hx0
  · intro x hx Y hY
    obtain ⟨T, hT, rfl⟩ := hY
    rw [starFiber_eq (hW T hT)]
    exact hx

/-- Proposition `prop: stars`, item (1), union half of Cocke25-1:
$\bigcup_{T \in \mathfrak{F}_H^*} T = U_H^*$ — "$U_H^* \subseteq
\mathfrak{F}_H^*$" holds by `prop: upper`, and the containment argument is that
of tex line 350.

Source (Section `sec: elems`, proposition `prop: stars`, statement tex line
342, proof tex lines 347-351):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem sUnion_starFiber_eq {H : Set G} (hH : H ∈ centralizers G)
    {X : Set G} (hX : ∀ y : G, ∃ x ∈ X, elementCenter x = elementCenter y) :
    ⋃₀ (starFiber X H) = upperStars X H := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro x ⟨T, hT, hxT⟩
    refine mem_upperStars.mpr ⟨starFiber_subset_X hT hxT, ?_⟩
    intro w hw
    rw [← starFiber_eq hT] at hw
    exact centralizerSet_mono (Set.singleton_subset_iff.mpr hxT) hw
  · exact Set.subset_sUnion_of_mem <| by
      rw [mem_starFiber]
      exact ⟨fun t ht => ht.1, (centralizerSet_upper hH hX).symm⟩

/-- Proposition `prop: stars`, item (2) of Cocke25-1:
$U_{H \vee K}^* = U_H^* \cap U_K^*$ ("$H \vee K \subseteq \mathbf{C}_G(x)$ iff
$x \in \mathbf{C}_G(H \vee K) = \mathbf{C}_G(H) \cap \mathbf{C}_G(K)$", tex
line 352): $\mathbf{C}_G(H \vee K) = \mathbf{C}_G(\mathbf{C}_G(H) \cap
\mathbf{C}_G(K)) = \mathbf{C}_G(H) \cap \mathbf{C}_G(K)$: the join is defined
as $\mathbf{C}_G(\mathbf{C}_G(H) \cap \mathbf{C}_G(K))$, and that intersection
lies in $\mathfrak{C}(G)$ by meet closure, so one application of
$\mathbf{C}_G$ recovers it (fixed-point property).

Source (Section `sec: elems`, proposition `prop: stars`, statement tex line
343, proof tex line 352):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem upperStars_sup (H K : ↥(centralizers G)) {X : Set G} :
    upperStars X ((H ⊔ K : ↥(centralizers G)) : Set G)
      = upperStars X H.val ∩ upperStars X K.val := by
  have hJ : centralizerSet H.val ∩ centralizerSet K.val ∈ centralizers G :=
    inter_mem_centralizers (centralizerSet_mem_centralizers _)
      (centralizerSet_mem_centralizers _)
  have heq : centralizerSet ((H ⊔ K : ↥(centralizers G)) : Set G)
      = centralizerSet H.val ∩ centralizerSet K.val := hJ
  ext x
  constructor
  · rintro ⟨hxX, hsub⟩
    have hxJK : x ∈ centralizerSet ((H ⊔ K : ↥(centralizers G)) : Set G) :=
      subset_singleton_centralizerSet_iff.mp hsub
    rw [heq] at hxJK
    refine ⟨mem_upperStars.mpr ⟨hxX, ?_⟩, mem_upperStars.mpr ⟨hxX, ?_⟩⟩
    · exact subset_singleton_centralizerSet_iff.mpr hxJK.1
    · exact subset_singleton_centralizerSet_iff.mpr hxJK.2
  · rintro ⟨⟨hxX, hH⟩, ⟨hxKX, hK⟩⟩
    have hxJK : x ∈ centralizerSet ((H ⊔ K : ↥(centralizers G)) : Set G) := by
      rw [heq]
      exact ⟨subset_singleton_centralizerSet_iff.mp hH,
        subset_singleton_centralizerSet_iff.mp hK⟩
    exact mem_upperStars.mpr ⟨hxX, subset_singleton_centralizerSet_iff.mpr hxJK⟩


/-! ### `thm: z_stars` -/

/-- Index-form bridge for `thm: z_stars`: for $H \in \mathfrak{C}(G)$,
$\mathbf{Z}(x) \subseteq H \iff \mathbf{C}_G(H) \subseteq \mathbf{C}_G(\{x\})$
— `prop: cent_basic` item (3) applied at $S := \mathbf{Z}(x) \in \mathfrak{C}(G)$,
using $\mathbf{C}_G(\mathbf{Z}(x)) = \mathbf{C}_G^3(\{x\}) =
\mathbf{C}_G(\{x\})$ (`cor: triple_C`). -/
theorem subset_elementCenter_iff {H : Set G} (hH : H ∈ centralizers G) {x : G} :
    elementCenter x ⊆ H ↔ centralizerSet H ⊆ centralizerSet {x} := by
  constructor
  · intro h
    have hCtr : centralizerSet (centralizerSet (centralizerSet {x}))
      = centralizerSet {x} :=
    centralizerSet_triple {x}
    have h1 : centralizerSet H ⊆
        centralizerSet (centralizerSet (centralizerSet {x})) :=
      centralizerSet_mono h
    rwa [hCtr] at h1
  · intro h
    have hHeq : cclosure H = H := hH
    show cclosure {x} ⊆ H
    intro z hz
    rw [← hHeq]
    show z ∈ centralizerSet (centralizerSet H)
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hy' : y ∈ centralizerSet {x} := h hy
    exact Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hz) y hy'

/-- Distinctness clause of `thm: z_stars`: classes over distinct element centers
are disjoint ("…as the $\mathbf{Z}^*(x)$'s are equivalence classes", tex line
398). -/
theorem elementCenterClass_disjoint {x y : G}
    (hne : elementCenter x ≠ elementCenter y) :
    Disjoint (elementCenterClass x) (elementCenterClass y) := by
  rw [Set.disjoint_iff]
  intro w hw
  exact hne (hw.1.symm.trans hw.2)

/-- Theorem `thm: z_stars` of Cocke25-1, first union form: every centralizer is
the union of the element-center classes it contains,
$H = \bigcup_{\mathbf{Z}(x) \subseteq H} \mathbf{Z}^*(x)$.
($\subseteq$: each $\mathbf{Z}^*(x) \subseteq \mathbf{Z}(x) \subseteq H$ by
`prop: g_in_Z`; $\supseteq$: $g \in H$ gives
$\mathbf{C}_G(H) \subseteq \mathbf{C}_G(\{g\})$ and $g \in \mathbf{Z}^*(g)$.)

Source (Section `sec: elems`, theorem `thm: z_stars`, statement tex lines
387-389, proof tex lines 391-397):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem zstars_eq {H : Set G} (hH : H ∈ centralizers G) :
    H = ⋃₀ (elementCenterClass '' {x : G | elementCenter x ⊆ H}) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro x hx
    have hxprop : elementCenter x ⊆ H :=
      (subset_elementCenter_iff hH).mpr
        (centralizerSet_mono (Set.singleton_subset_iff.mpr hx))
    have hxcls : x ∈ elementCenterClass x := rfl
    have himg : elementCenterClass x ∈
        elementCenterClass '' {y : G | elementCenter y ⊆ H} :=
      ⟨x, hxprop, rfl⟩
    exact Set.mem_sUnion_of_mem hxcls himg
  · rintro x ⟨Y, hY, hxY⟩
    obtain ⟨x0, hx0S, rfl⟩ := hY
    exact hx0S (elementCenterClass_subset_elementCenter x0 hxY)

/-- Theorem `thm: z_stars`, second union form: the same union indexed by
$\mathbf{C}_G(H) \subseteq \mathbf{C}_G(x)$ ("That … follows by Corollary
`cor: bij`", tex line 392 — dually via `prop: cent_basic` item (3)).

Source (Section `sec: elems`, theorem `thm: z_stars`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
lines 387-399. -/
theorem zstars_eq_centralizerForm {H : Set G} (hH : H ∈ centralizers G) :
    H = ⋃₀ (elementCenterClass ''
        {x : G | centralizerSet H ⊆ centralizerSet {x}}) := by
  have hiff : ∀ x : G,
      elementCenter x ⊆ H ↔ centralizerSet H ⊆ centralizerSet {x} :=
    fun x => subset_elementCenter_iff hH
  refine Eq.trans (zstars_eq hH) ?_
  have hset : {x : G | elementCenter x ⊆ H}
      = {x : G | centralizerSet H ⊆ centralizerSet {x}} :=
    Set.ext fun x => hiff x
  rw [hset]


/-! ### `cor: z_stars_fin`

The finite corollary of `thm: z_stars`: a centralizer $H$ splits as
$\mathbf{Z}(G)$ together with one $\mathbf{Z}^*$-class per non-central element
center contained in $H$. The representative list is kept as a hypothesis
(decomposition and disjointness clauses of `cor: z_stars_fin`, tex lines
403-405); its existence for finite $G$ is the introduction form of `intro:
z_stars_fin` (tex lines 304-306). -/

/-- Note preceding the definition of $\mathbf{Z}^*$: "$x$ is central iff
$\mathbf{Z}(x) = \mathbf{Z}(G)$". Forward: $x \in \mathbf{Z}(x)$ by
extensivity. Backward: $x$ central makes every $w$ commute with $\{x\}$, so
$\mathbf{C}_G(\{x\}) = G$ and $\mathbf{Z}(x) = \mathbf{C}_G(G) =
\mathbf{Z}(G)$ element-wise. Underlies "Note that $\mathbf{Z}^*(z) =
\mathbf{Z}(G)$ for $z \in \mathbf{Z}(G)$" (tex line 375, formalized next as
`elementCenterClass_center`) and the case split in `cor: z_stars_fin`.

Source (Section `sec: elems`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
line 375. -/
theorem elementCenter_eq_center_iff (x : G) :
    elementCenter x = (Subgroup.center G : Set G) ↔ x ∈ Subgroup.center G := by
  constructor
  · intro h
    have hx : x ∈ elementCenter x := subset_cclosure {x} rfl
    rwa [h] at hx
  · intro hx
    have hcomm : ∀ w : G, w * x = x * w := Subgroup.mem_center_iff.mp hx
    show centralizerSet (centralizerSet {x}) = (Subgroup.center G : Set G)
    ext w
    constructor
    · intro hw
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have hyx : y ∈ centralizerSet {x} :=
        Subgroup.mem_centralizer_iff.mpr fun v hv => by
          rw [Set.mem_singleton_iff.mp hv]
          exact hcomm y |>.symm
      exact Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hw) y hyx
    · intro hw
      exact Subgroup.mem_centralizer_iff.mpr fun y _ =>
        Subgroup.mem_center_iff.mp hw y

/-- Tex line 375: "Note that $\mathbf{Z}^*(z) = \mathbf{Z}(G)$ for $z \in
\mathbf{Z}(G)$", via `elementCenter_eq_center_iff`.

Source (Section `sec: elems`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
line 375. -/
theorem elementCenterClass_center {z : G} (hz : z ∈ Subgroup.center G) :
    elementCenterClass z = (Subgroup.center G : Set G) := by
  ext w
  constructor
  · intro hw
    exact (elementCenter_eq_center_iff w).mp <|
      hw.trans ((elementCenter_eq_center_iff z).mpr hz)
  · intro hw
    show elementCenter w = elementCenter z
    exact ((elementCenter_eq_center_iff w).mpr hw).trans
      ((elementCenter_eq_center_iff z).mpr hz).symm

/-- $\mathbf{Z}(G) \subseteq H$ for $H \in \mathfrak{C}(G)$: a central $z$
commutes with all of $\mathbf{C}_G(H)$, so $z \in
\mathbf{C}_G(\mathbf{C}_G(H)) = H$. Used for the $\mathbf{Z}(G)$ summand of
`cor: z_stars_fin`. -/
theorem center_le_of_mem_centralizers {H : Set G} (hH : H ∈ centralizers G) :
    (Subgroup.center G : Set G) ⊆ H := by
  have hHeq : cclosure H = H := hH
  intro z hz
  rw [← hHeq]
  show z ∈ centralizerSet (centralizerSet H)
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  exact Subgroup.mem_center_iff.mp hz y

/-- Corollary `cor: z_stars_fin` of Cocke25-1, decomposition clause: given
representatives $g_1,\dots,g_t \in G \setminus \mathbf{Z}(G)$ whose element
centers are distinct and comprise exactly the non-central element centers
contained in $H$, $$H = (\bigcup_{g \in s} \mathbf{Z}^*(g)) \cup \mathbf{Z}(G).$$
Proof: substitute the index set of `thm: z_stars` (`zstars_eq`), splitting at
$\mathbf{Z}(y) = \mathbf{Z}(G)$ ("comprise all of the non-central element
centers contained in $H$", tex line 404); the $\supseteq$ direction uses
$\mathbf{Z}^*(g) \subseteq \mathbf{Z}(g) \subseteq H$ (`prop: g_in_Z`,
`hs_sub`) and $\mathbf{Z}(G) \subseteq H$. Finiteness of $G$ is not needed for
this clause — only for the existence of representatives
(`exists_zstars_reps`, tex lines 304-306).

Source (Section `sec: elems`, corollary `cor: z_stars_fin`, statement tex lines
403-405):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem zstars_fin_eq {H : Set G} (hH : H ∈ centralizers G) {s : Finset G}
    (_hs_nc : ∀ g ∈ s, g ∉ (Subgroup.center G : Set G))
    (hs_sub : ∀ g ∈ s, elementCenter g ⊆ H)
    (_hs_dist : ∀ g ∈ s, ∀ k ∈ s, elementCenter g = elementCenter k → g = k)
    (hs_cov : ∀ x : G, x ∉ (Subgroup.center G : Set G) → elementCenter x ⊆ H →
      ∃ g ∈ s, elementCenter g = elementCenter x) :
    H = (⋃ g ∈ (↑s : Set G), elementCenterClass g) ∪
      (Subgroup.center G : Set G) :=
  calc H = ⋃₀ (elementCenterClass '' {y : G | elementCenter y ⊆ H}) := zstars_eq hH
    _ = (⋃ g ∈ (↑s : Set G), elementCenterClass g) ∪
        (Subgroup.center G : Set G) := by
        refine Set.eq_of_subset_of_subset ?_ ?_
        · rintro x ⟨_, ⟨y, hyprop, rfl⟩, hx⟩
          rcases eq_or_ne (elementCenter y) (Subgroup.center G : Set G) with hc | hc
          · refine Or.inr ?_
            rw [← elementCenterClass_center ((elementCenter_eq_center_iff y).mp hc)]
            exact hx
          · have hync : y ∉ (Subgroup.center G : Set G) := fun hmem =>
              hc ((elementCenter_eq_center_iff y).mpr hmem)
            obtain ⟨g, hgs, hgc⟩ := hs_cov y hync hyprop
            refine Or.inl (Set.mem_iUnion₂.mpr ⟨g, hgs, ?_⟩)
            show elementCenter x = elementCenter g
            rw [hgc]
            exact hx
        · rintro x (hx | hx)
          · obtain ⟨g, hgs, hgcls⟩ := Set.mem_iUnion₂.mp hx
            exact Set.mem_sUnion_of_mem hgcls ⟨g, hs_sub g hgs, rfl⟩
          · refine Set.mem_sUnion_of_mem
              (show x ∈ elementCenterClass x from rfl) ⟨x, ?_, rfl⟩
            show elementCenter x ⊆ H
            rw [(elementCenter_eq_center_iff x).mpr hx]
            exact center_le_of_mem_centralizers hH

/-- Corollary `cor: z_stars_fin` of Cocke25-1, disjointness clause: "and this
union is disjoint" (tex lines 404-405). Each $\mathbf{Z}^*(g)$ ($g$
non-central) misses $\mathbf{Z}(G)$ — otherwise $g \in \mathbf{Z}(g) =
\mathbf{Z}(G)$ — and distinct indices give disjoint classes as equivalence
classes ("a union over distinct equivalence classes is a disjoint union", tex
line 398).

Source (Section `sec: elems`, corollary `cor: z_stars_fin`, statement tex lines
403-405; disjointness mechanism from theorem `thm: z_stars`, tex line 398):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem zstars_fin_disjoint {s : Finset G}
    (hs_nc : ∀ g ∈ s, g ∉ (Subgroup.center G : Set G))
    (hs_dist : ∀ g ∈ s, ∀ k ∈ s, elementCenter g = elementCenter k → g = k) :
    (∀ g ∈ s, Disjoint (elementCenterClass g) (Subgroup.center G : Set G)) ∧
      ∀ g ∈ s, ∀ k ∈ s, g ≠ k → Disjoint (elementCenterClass g) (elementCenterClass k) := by
  constructor
  · intro g hgs
    rw [Set.disjoint_iff]
    rintro w ⟨hwg, hwc⟩
    exfalso
    refine hs_nc g hgs ?_
    refine (elementCenter_eq_center_iff g).mp ?_
    rw [← hwg]
    exact (elementCenter_eq_center_iff w).mpr hwc
  · intro g hgs k hks hne
    refine elementCenterClass_disjoint fun heq => hne ?_
    exact hs_dist g hgs k hks heq

/-- Theorem `intro: z_stars_fin` of Cocke25-1, introduction form ("There exist
elements $g_1, \dots, g_t$ in $G \setminus \mathbf{Z}(G)$ so that
$\mathbf{Z}(g_1), \dots, \mathbf{Z}(g_t)$ are distinct and comprise all of the
non-central element centers contained in $H$", cf. tex lines 304-306 and 404):
for a finite group there always exists a finite representative set $s$.
Representatives are chosen canonically by minimizing an embedding $G
\hookrightarrow \mathrm{Fin}\,n$ within each class inside $\{x \mid x \notin
\mathbf{Z}(G), \mathbf{Z}(x) \subseteq H\}$, avoiding any choice beyond
`Classical.choice`; neither $H \in \mathfrak{C}(G)$ nor nonabelianity is needed
(encoding delta; see `status.md`). Combine with `zstars_fin_eq` /
`zstars_fin_disjoint` for the full statement.

Source (Introduction, theorem `intro: z_stars_fin`, statement tex lines
304-306; corollary `cor: z_stars_fin`, tex lines 403-405):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem exists_zstars_reps [Finite G] {H : Set G} :
    ∃ s : Finset G,
      (∀ g ∈ s, g ∉ (Subgroup.center G : Set G)) ∧
      (∀ g ∈ s, elementCenter g ⊆ H) ∧
      (∀ g ∈ s, ∀ k ∈ s, elementCenter g = elementCenter k → g = k) ∧
      (∀ x : G, x ∉ (Subgroup.center G : Set G) → elementCenter x ⊆ H →
        ∃ g ∈ s, elementCenter g = elementCenter x) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set rank : G → ℕ := fun x => (Fintype.equivFin G x : ℕ) with hrank_def
  have hrank_inj : Function.Injective rank := fun a b hab =>
    (Fintype.equivFin G).injective (Fin.val_injective hab)
  set T : Finset G := Finset.univ.filter
    (fun x => x ∉ (Subgroup.center G : Set G) ∧ elementCenter x ⊆ H) with hT_def
  have hTmem : ∀ g ∈ T, g ∉ (Subgroup.center G : Set G) ∧ elementCenter g ⊆ H :=
    fun g hg => (Finset.mem_filter.mp hg).2
  refine ⟨T.filter
    (fun g => ∀ k ∈ T, elementCenter k = elementCenter g → rank g ≤ rank k),
    ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact hTmem g (Finset.mem_filter.mp hg).1 |>.1
  · intro g hg
    exact hTmem g (Finset.mem_filter.mp hg).1 |>.2
  · intro g hg k hk heq
    have hgT : g ∈ T := (Finset.mem_filter.mp hg).1
    have hkT : k ∈ T := (Finset.mem_filter.mp hk).1
    have h1 : rank g ≤ rank k := (Finset.mem_filter.mp hg).2 k hkT heq.symm
    have h2 : rank k ≤ rank g := (Finset.mem_filter.mp hk).2 g hgT heq
    exact hrank_inj (le_antisymm h1 h2)
  · intro x hxc hsub
    have hxT : x ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxc, hsub⟩
    set T' : Finset G := T.filter (fun k => elementCenter k = elementCenter x)
    have hxT' : x ∈ T' := Finset.mem_filter.mpr ⟨hxT, rfl⟩
    have hne : (T'.image rank).Nonempty :=
      ⟨rank x, Finset.mem_image.mpr ⟨x, hxT', rfl⟩⟩
    obtain ⟨m, hmT', hmrank⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
    have hmT : m ∈ T := (Finset.mem_filter.mp hmT').1
    have hmZx : elementCenter m = elementCenter x := (Finset.mem_filter.mp hmT').2
    have hbound : ∀ k ∈ T', rank m ≤ rank k := fun k hk => by
      rw [hmrank]
      exact (Finset.isLeast_min' _ hne).2 (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    refine ⟨m, Finset.mem_filter.mpr ⟨hmT, ?_⟩, hmZx⟩
    intro k hkT hkeq
    exact hbound k (Finset.mem_filter.mpr ⟨hkT, hkeq.trans hmZx⟩)

/-! ### `lem: cen_divides_stars` -/

open scoped Pointwise in
/-- Lemma `lem: cen_divides_stars` of Cocke25-1, coset clause: "$\mathbf{Z}^*(g)$
times $\mathbf{Z}(G)$ is itself" — "Note that if $x \in \mathbf{Z}^*(g)$, then
$x\,\mathbf{Z}(G) \subseteq \mathbf{Z}^*(g)$. This is true because
$\mathbf{C}_G(x) = \mathbf{C}_G(xz)$ for every $z \in \mathbf{Z}(G)$" (tex line
416, via `mem_elementCenterClass_mul_center`); the reverse containment holds by
the identity element. Equivalently, $\mathbf{Z}^*(g)$ "can be expressed as a
union of cosets of $\mathbf{Z}(G)$ in $G$" (tex lines 412, 416-417).

Source (Section `sec: Moby`, lemma `lem: cen_divides_stars`, statement tex lines
411-413, proof tex line 416):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem elementCenterClass_mul_center (g : G) :
    elementCenterClass g * Subgroup.center G = elementCenterClass g := by
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨x, hx, z, hz, rfl⟩ := Set.mem_mul.mp hy
    exact mem_elementCenterClass_mul_center hx hz
  · exact Set.mem_mul.mpr ⟨y, hy, 1, Subgroup.one_mem _, mul_one y⟩

open scoped Pointwise in
/-- Lemma `lem: cen_divides_stars` of Cocke25-1, cardinality clause:
$$|\mathbf{Z}^*(g)| = |\mathbf{Z}(G)| \cdot \#\{\text{cosets of }
\mathbf{Z}(G)\text{ meeting }\mathbf{Z}^*(g)\},$$ where the second factor is the
image of $\mathbf{Z}^*(g)$ under the quotient projection — "the number of
elements of a transversal for $\mathbf{Z}(G)$ in $G$ that lie in
$\mathbf{Z}^*(g)$" (tex line 412). Direct application of mathlib's fiber
formula `Subgroup.card_mul_eq_card_subgroup_mul_card_quotient` to
`elementCenterClass_mul_center`.

Source (Section `sec: Moby`, lemma `lem: cen_divides_stars`, statement tex lines
411-413, proof tex lines 415-418):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem natCard_elementCenterClass_eq [Finite G] (g : G) :
    Nat.card (elementCenterClass g)
      = Nat.card (Subgroup.center G) *
        Nat.card ((elementCenterClass g).image (↑) : Set (G ⧸ Subgroup.center G)) := by
  rw [← Subgroup.card_mul_eq_card_subgroup_mul_card_quotient,
    elementCenterClass_mul_center]

open scoped Pointwise in
/-- Lemma `lem: cen_divides_stars` of Cocke25-1, divisibility clause:
"$|\mathbf{Z}(G)|$ divides $|\mathbf{Z}^*(g)|$" (tex line 412) — immediate from
`natCard_elementCenterClass_eq`.

Source (Section `sec: Moby`, lemma `lem: cen_divides_stars`, statement tex lines
411-413):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem natCard_center_dvd_natCard_elementCenterClass [Finite G] (g : G) :
    Nat.card (Subgroup.center G) ∣ Nat.card (elementCenterClass g) := by
  exact ⟨_, natCard_elementCenterClass_eq g⟩


end Cocke25_1
