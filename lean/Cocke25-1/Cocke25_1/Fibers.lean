import Cocke25_1.CentLattice
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! # Fibers of the centralizer map and union/intersection formulas

Formalization of Cocke25-1 (*A Möbius function on the Centralizer Lattice*,
arXiv:2512.13839v2):

- Proposition `prop: cent_union_int_1` (Section `sec: basic`): the centralizer
  of a union is the intersection of centralizers, and unions of centralizers
  sit inside the centralizer of the intersection;
- Proposition `prop: equiv_C-CC` (Section `sec: elems`): equal element
  centralizers are equivalent to equal double centralizers;
- Proposition `prop: unique_cent` (Section `sec: op`): fibers
  $\mathfrak{F}_{\mathbf{C}_G(S)}$ are closed under arbitrary unions and their
  union is $\mathbf{C}_G(\mathbf{C}_G(S))$;
- Proposition `prop:join_nice` (Section `sec: op`): writing $H = \mathbf{C}_G(A)$
  and $K = \mathbf{C}_G(B)$ with $A, B \in \mathfrak{C}(G)$, the lattice join is
  $H \vee K = \mathbf{C}_G(A \cap B)$.
-/

namespace Cocke25_1

variable {G : Type*} [Group G]

/-- Proposition `prop: equiv_C-CC` of Cocke25-1: $\mathbf{C}_G(x) =
\mathbf{C}_G(y)$ if and only if $\mathbf{C}_G(\mathbf{C}_G(x)) =
\mathbf{C}_G(\mathbf{C}_G(y))$, proved as in the paper by applying
$\mathbf{C}_G(\cdot)$ and reducing with $\mathbf{C}_G(\mathbf{C}_G(\mathbf{C}_G(\cdot)))
= \mathbf{C}_G(\cdot)$ (`cor: triple_C`).

Source (Section `sec: elems`, proposition `prop: equiv_C-CC`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
lines 310-316 (statement at 310-312, proof at 314-316). -/
theorem centralizerSet_eq_iff_cclosure_eq {x y : G} :
    centralizerSet {x} = centralizerSet {y} ↔
      cclosure {x} = cclosure {y} := by
  constructor
  · intro h
    show centralizerSet (centralizerSet {x}) = centralizerSet (centralizerSet {y})
    exact congrArg centralizerSet h
  · intro h
    have h' : centralizerSet (centralizerSet {x}) =
        centralizerSet (centralizerSet {y}) := h
    calc centralizerSet {x}
        = centralizerSet (centralizerSet (centralizerSet {x})) :=
          (centralizerSet_triple _).symm
      _ = centralizerSet (centralizerSet (centralizerSet {y})) := by rw [h']
      _ = centralizerSet {y} := centralizerSet_triple _

/-- Proposition `prop: cent_union_int_1`, item (1) of Cocke25-1:
$\mathbf{C}_G\left(\bigcup_{S \in \mathfrak{S}} S\right) =
\bigcap_{S \in \mathfrak{S}} \mathbf{C}_G(S)$. The paper's hypothesis that
$\mathfrak{S}$ be nonempty is unnecessary for the element-wise argument and is
dropped (encoding delta; see `status.md`).

Source (Section `sec: basic`, `prop: cent_union_int_1`, statement tex lines
114-119, proof tex lines 122-130):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem centralizerSet_sUnion (𝓢 : Set (Set G)) :
    centralizerSet (⋃₀ 𝓢) = ⋂₀ (centralizerSet '' 𝓢) := by
  ext x
  constructor
  · intro hx Y hY
    obtain ⟨T, hT, rfl⟩ := hY
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hx) w
        (Set.mem_sUnion_of_mem hw hT)
  · intro hx
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    obtain ⟨T, hT, hwT⟩ := hw
    have hxT : x ∈ centralizerSet T :=
      (Set.mem_sInter.mp hx) (centralizerSet T) ⟨T, hT, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hxT) w hwT

/-- Proposition `prop: cent_union_int_1`, item (2) of Cocke25-1:
$\bigcup_{S \in \mathfrak{S}} \mathbf{C}_G(S) \subseteq
\mathbf{C}_G\left(\bigcap_{S \in \mathfrak{S}} S\right)$, via `lem: contain`
applied to $\bigcap_{S \in \mathfrak{S}} S \subseteq S'$ (tex line 138).
Nonemptiness again unnecessary.

Source (Section `sec: basic`, `prop: cent_union_int_1`, statement tex line 118,
proof tex lines 132-138):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem sUnion_centralizerSet_subset (𝓢 : Set (Set G)) :
    ⋃₀ (centralizerSet '' 𝓢) ⊆ centralizerSet (⋂₀ 𝓢) := by
  rintro x ⟨T, hT, hxT⟩
  obtain ⟨U, hU, rfl⟩ := hT
  refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
  exact Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hxT) w
    ((Set.mem_sInter.mp hw) U hU)

/-- The fiber $\mathfrak{F}_{\mathbf{C}_G(S)} = \{ T \subseteq G \mid
\mathbf{C}_G(T) = \mathbf{C}_G(S) \}$ of the centralizer map over
$\mathbf{C}_G(S)$ (tex line 267). -/
def centralizerFiber (S : Set G) : Set (Set G) :=
  {T | centralizerSet T = centralizerSet S}

/-- Proposition `prop: unique_cent` of Cocke25-1 (closure half):
$\mathfrak{F}_{\mathbf{C}_G(S)}$ is closed under arbitrary unions. The paper's
proof takes $\mathfrak{W} \subseteq \mathfrak{F}$ arbitrary; for the
$\bigcap_{W} \mathbf{C}_G(W) = \mathbf{C}_G(S)$ step a nonempty $\mathfrak{W}$ is
needed (the empty family intersects to everything), so it is an explicit
hypothesis here (encoding delta; see `status.md`).

Source (Section `sec: op`, `prop: unique_cent`, statement tex lines 271-273,
proof tex lines 275-278):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem centralizerFiber_sUnion_mem {S : Set G} {𝓦 : Set (Set G)}
    (hne : 𝓦.Nonempty) (h𝓦 : ∀ T ∈ 𝓦, centralizerSet T = centralizerSet S) :
    centralizerSet (⋃₀ 𝓦) = centralizerSet S := by
  rw [centralizerSet_sUnion]
  obtain ⟨W0, hW0⟩ := hne
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro x hx
    have hx0 : x ∈ centralizerSet W0 :=
      (Set.mem_sInter.mp hx) (centralizerSet W0) ⟨W0, hW0, rfl⟩
    rwa [h𝓦 W0 hW0] at hx0
  · intro x hx Y hY
    obtain ⟨T, hT, rfl⟩ := hY
    rw [h𝓦 T hT]
    exact hx

/-- Proposition `prop: unique_cent` of Cocke25-1 (union half):
$\bigcup_{T \in \mathfrak{F}_{\mathbf{C}_G(S)}} T =
\mathbf{C}_G(\mathbf{C}_G(S))$: the fiber member $\mathbf{C}_G(\mathbf{C}_G(S))$
itself ("By Corollary \ref{cor: triple_C} ... $A \in \mathfrak{F}$", tex line
276) bounds the union from above via extensivity (tex line 278).

Source (Section `sec: op`, `prop: unique_cent`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
lines 271-279. -/
theorem sUnion_centralizerFiber_eq (S : Set G) :
    ⋃₀ (centralizerFiber S) = cclosure S := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨T, hT, hxT⟩
    have hsub : cclosure T = cclosure S := by
      unfold cclosure
      rw [hT]
    exact hsub ▸ subset_cclosure T hxT
  · have hmem : cclosure S ∈ centralizerFiber S := by
      show centralizerSet (cclosure S) = centralizerSet S
      exact centralizerSet_triple S
    exact Set.subset_sUnion_of_mem hmem

/-- Proposition `prop:join_nice` of Cocke25-1: writing $H = \mathbf{C}_G(A)$ and
$K = \mathbf{C}_G(B)$ with $A, B \in \mathfrak{C}(G)$, the join of the
centralizer lattice satisfies $H \vee K = \mathbf{C}_G(A \cap B)$ ("since $A, B
\in \mathfrak{C}(G)$", tex line 291: $\mathbf{C}_G(H) = A$,
$\mathbf{C}_G(K) = B$).

Source (Section `sec: op`, `prop:join_nice`, statement tex lines 285-287, proof
tex lines 289-292):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem sup_eq_centralizerSet_inter {A B : Set G}
    (hA : A ∈ centralizers G) (hB : B ∈ centralizers G)
    (H K : ↥(centralizers G))
    (hHA : H.val = centralizerSet A) (hKB : K.val = centralizerSet B) :
    (H ⊔ K).val = centralizerSet (A ∩ B) := by
  have hAeq : centralizerSet (centralizerSet A) = A := hA
  have hBeq : centralizerSet (centralizerSet B) = B := hB
  rw [show (H ⊔ K).val =
      centralizerSet (centralizerSet H.val ∩ centralizerSet K.val) from rfl,
    hHA, hKB, hAeq, hBeq]

/-- Proposition `prop: cent_union_int`, item (1) of Cocke25-1:
$\mathbf{C}_G(\langle \bigcup_{S \in \mathfrak{S}} S \rangle) =
\bigcap_{S \in \mathfrak{S}} \mathbf{C}_G(S)$; the middle equality
$\mathbf{C}_G(\bigcup \mathfrak{S}) = \mathbf{C}_G(\langle \cdot \rangle)$ is
exactly `lem: sub` (`centralizerSet_closure`), and the right one is `prop:
cent_union_int_1` item (1) ("Much of this has been proven in Proposition
\ref{prop: cent_union_int_1}", tex line 160).

Source (Section `sec: basic`, proposition `prop: cent_union_int`, statement tex
lines 151-156, proof tex lines 159-162):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem centralizerSet_closure_sUnion (𝓢 : Set (Set G)) :
    centralizerSet (↑(Subgroup.closure (⋃₀ 𝓢)) : Set G)
      = ⋂₀ (centralizerSet '' 𝓢) :=
  (centralizerSet_closure _).trans (centralizerSet_sUnion 𝓢)

/-- Proposition `prop: cent_union_int`, item (2), second containment of
Cocke25-1: $\langle \bigcup_{S} \mathbf{C}_G(S) \rangle \subseteq
\mathbf{C}_G(\bigcap_{S} S)$ — "$\mathbf{C}_G(\bigcap \mathfrak{S})$ is a
subgroup of $G$ that contains the set $\bigcup \mathbf{C}_G(S)$", so also its
generated subgroup (tex line 164); uses `prop: cent_union_int_1` item (2).
(The containment $\bigcup \subseteq \langle \cdot \rangle$ is
`Subgroup.subset_closure`; the paper's nonempty hypothesis is again unused.)

Source (Section `sec: basic`, proposition `prop: cent_union_int`, statement tex
line 155, proof tex lines 162-164):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem closure_sUnion_centralizerSet_subset (𝓢 : Set (Set G)) :
    (Subgroup.closure (⋃₀ (centralizerSet '' 𝓢)) : Set G) ⊆
      centralizerSet (⋂₀ 𝓢) :=
  (Subgroup.closure_le _).mpr (sUnion_centralizerSet_subset 𝓢)

end Cocke25_1
