import Cocke25_1.Galois
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! # The centralizer lattice $\mathfrak{C}(G)$

Formalization of the (unlabeled) theorem opening Section `sec: op` of Cocke25-1
(*A Möbius function on the Centralizer Lattice*, arXiv:2512.13839v2): for
$\mathfrak{C}(G) = \{\mathbf{C}_G(H) \mid H \in \mathcal{P}(G)\}$,

1. $\mathfrak{C}(G)$ is a lattice;
2. the map $\mathbf{C}_G(\cdot) : \mathfrak{C}(G) \to \mathfrak{C}(G)$ is an
   inclusion-reversing bijection;
3. $\mathbf{C}_G(\mathbf{C}_G(H)) = H$ for all $H \in \mathfrak{C}(G)$;

together with Proposition `prop: cent_basic` and Corollary `cor: bij`.
-/

namespace Cocke25_1

variable {G : Type*} [Group G]

/-- The centralizer $\mathbf{C}_G(S)$ of a subset $S \subseteq G$, as a subset of
$G$ (the carrier of mathlib's `Subgroup.centralizer`). -/
def centralizerSet (S : Set G) : Set G := (Subgroup.centralizer S : Set G)

/-- The closure operator $\mathbf{C}_G(\mathbf{C}_G(\cdot))$ on $\mathcal{P}(G)$
(Section `sec: op`, tex line 180: "one of our main observations is that
$\mathbf{C}_G(\mathbf{C}_G(\cdot))$ is a closure operator on $\mathcal{P}(G)$"). -/
def cclosure (S : Set G) : Set G := centralizerSet (centralizerSet S)

/-- $\mathfrak{C}(G)$, the set of all centralizers in $G$ (tex line 183:
$\{\mathbf{C}_G(H) \mid H \in \mathcal{P}(G)\}$), characterized as the fixed points
of $\mathbf{C}_G(\mathbf{C}_G(\cdot))$ by `prop: cent_basic` item (1). -/
def centralizers (G : Type*) [Group G] : Set (Set G) := {T | cclosure T = T}

theorem mem_centralizers (T : Set G) :
    T ∈ centralizers G ↔ centralizerSet (centralizerSet T) = T := Iff.rfl

/-- Lemma `lem: contain` of Cocke25-1 (`prop: cent_basic` item (2)):
$\mathbf{C}_G$ is order-reversing, $S \subseteq T \implies \mathbf{C}_G(T)
\subseteq \mathbf{C}_G(S)$.

Source (Section "Basic definitions", `lem: contain`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
lines 105-107; restated at tex lines 211 and 243. -/
theorem centralizerSet_mono {S T : Set G} (h : S ⊆ T) :
    centralizerSet T ⊆ centralizerSet S := fun _x hx =>
  Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hx) y (h hy)

/-- Extensivity of the closure operator: $S \subseteq \mathbf{C}_G(\mathbf{C}_G(S))$
(closure-operator axiom (Extensive), tex line 199). -/
theorem subset_cclosure (S : Set G) : S ⊆ cclosure S := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun _w hw =>
    (Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hw) x hx).symm

/-- Corollary `cor: triple_C` transported to `centralizerSet`:
$\mathbf{C}_G(\mathbf{C}_G(\mathbf{C}_G(S))) = \mathbf{C}_G(S)$. -/
theorem centralizerSet_triple (S : Set G) :
    centralizerSet (centralizerSet (centralizerSet S)) = centralizerSet S :=
  congrArg (fun H : Subgroup G => (H : Set G)) (triple_C_centralizer S)

/-- Gap lemma **G2**: $\mathbf{C}_G(S \cup T) = \mathbf{C}_G(S) \cap \mathbf{C}_G(T)$.
Mathlib has this only for its set-valued `Set.centralizer`
(/home/chz/src/mathlib4/Mathlib/Algebra/Group/Center.lean:171), not at the carrier
level of `Subgroup.centralizer`. -/
theorem centralizerSet_union (S T : Set G) :
    centralizerSet (S ∪ T) = centralizerSet S ∩ centralizerSet T := by
  ext x
  simp only [Set.mem_inter_iff, centralizerSet, SetLike.mem_coe,
    Subgroup.mem_centralizer_iff]
  constructor
  · exact fun h => ⟨fun z hz => h z (Or.inl hz), fun z hz => h z (Or.inr hz)⟩
  · rintro ⟨h1, h2⟩ z (hz | hz)
    · exact h1 z hz
    · exact h2 z hz

theorem centralizerSet_mem_centralizers (S : Set G) :
    centralizerSet S ∈ centralizers G := by
  rw [mem_centralizers]
  show centralizerSet (centralizerSet (centralizerSet S)) = centralizerSet S
  rw [centralizerSet_triple]

/-- Proposition `prop: cent_basic`, item (1) of Cocke25-1: $S =
\mathbf{C}_G(\mathbf{C}_G(S))$ if and only if $S \in \mathfrak{C}(G)$ (image form,
following the paper's proof: "So $S = \mathbf{C}_G(T)$ ... By Corollary
\ref{cor: triple_C}", tex lines 248-249).

Source (Section `sec: op`, proposition `prop: cent_basic`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
lines 242 (statement), 248-249 (proof). -/
theorem mem_centralizers_iff (T : Set G) :
    T ∈ centralizers G ↔ ∃ S : Set G, centralizerSet S = T := by
  constructor
  · intro h
    exact ⟨centralizerSet T, h⟩
  · rintro ⟨S, hS⟩
    rw [← hS]
    exact centralizerSet_mem_centralizers S

/-- Proposition `prop: cent_basic`, item (3) of Cocke25-1: for $T \in
\mathfrak{C}(G)$ one has $S \subseteq T$ if and only if $\mathbf{C}_G(T)
\subseteq \mathbf{C}_G(S)$.

Source (Section `sec: op`, `prop: cent_basic`, statement tex line 244, proof
tex lines 251-255). -/
theorem subset_comm_of_mem_centralizers {T : Set G} (hT : T ∈ centralizers G)
    (S : Set G) :
    S ⊆ T ↔ centralizerSet T ⊆ centralizerSet S := by
  constructor
  · exact centralizerSet_mono
  · intro h
    calc S ⊆ centralizerSet (centralizerSet S) := subset_cclosure S
      _ ⊆ centralizerSet (centralizerSet T) := centralizerSet_mono h
      _ = T := hT

/-- Theorem part (3) of Cocke25-1 (`sec: op`, unlabeled theorem): for $H \in
\mathfrak{C}(G)$, $\mathbf{C}_G(\mathbf{C}_G(H)) = H$.

Source (Section `sec: op`, theorem tex lines 182-189, item at tex line 187). -/
theorem cclosure_eq_of_mem_centralizers {T : Set G} (hT : T ∈ centralizers G) :
    centralizerSet (centralizerSet T) = T := hT

/-- Gap lemma **G1** (meet closure): intersection of two members of
$\mathfrak{C}(G)$ is a member. The paper credits the meet/join formulas to
Schmidt's lattice work (`sch70`, `sch_book`) without proof (tex line 263);
proved here element-wise from `lem: contain` and `cor: triple_C`. -/
theorem inter_mem_centralizers {A B : Set G}
    (hA : A ∈ centralizers G) (hB : B ∈ centralizers G) : A ∩ B ∈ centralizers G := by
  have hA' : centralizerSet (centralizerSet A) = A := hA
  have hB' : centralizerSet (centralizerSet B) = B := hB
  have key : centralizerSet (centralizerSet A ∪ centralizerSet B) = A ∩ B := by
    rw [centralizerSet_union, hA', hB']
  show cclosure (A ∩ B) = A ∩ B
  rw [← key]
  show centralizerSet (centralizerSet (centralizerSet
      (centralizerSet A ∪ centralizerSet B))) =
    centralizerSet (centralizerSet A ∪ centralizerSet B)
  exact centralizerSet_triple _

/-- Gap lemma **G1** (join closure): $\mathbf{C}_G(\mathbf{C}_G(A) \cap
\mathbf{C}_G(B)) \in \mathfrak{C}(G)$ for $A, B \in \mathfrak{C}(G)$ (join formula
of tex line 263, credited to Schmidt's lattice work; proved here). -/
theorem join_mem_centralizers {A B : Set G}
    (_hA : A ∈ centralizers G) (_hB : B ∈ centralizers G) :
    centralizerSet (centralizerSet A ∩ centralizerSet B) ∈ centralizers G :=
  centralizerSet_mem_centralizers _

instance instLatticeCentralizers : Lattice ↥(centralizers G) where
  inf A B := ⟨A ∩ B, inter_mem_centralizers A.property B.property⟩
  sup A B :=
    ⟨centralizerSet (centralizerSet A.val ∩ centralizerSet B.val),
      join_mem_centralizers A.property B.property⟩
  inf_le_left := fun A B => by
    show (A.val ∩ B.val : Set G) ⊆ A.val
    exact Set.inter_subset_left
  inf_le_right := fun A B => by
    show (A.val ∩ B.val : Set G) ⊆ B.val
    exact Set.inter_subset_right
  le_inf := fun A B C h1 h2 => by
    have h1' : (A.val : Set G) ⊆ B.val := h1
    have h2' : (A.val : Set G) ⊆ C.val := h2
    exact Set.subset_inter h1' h2'
  le_sup_left := fun A B => by
    show (A.val : Set G) ⊆ centralizerSet (centralizerSet A.val ∩ centralizerSet B.val)
    exact (subset_cclosure A.val).trans (centralizerSet_mono Set.inter_subset_left)
  le_sup_right := fun A B => by
    show (B.val : Set G) ⊆ centralizerSet (centralizerSet A.val ∩ centralizerSet B.val)
    exact (subset_cclosure B.val).trans (centralizerSet_mono Set.inter_subset_right)
  sup_le := fun A B C h1 h2 => by
    have h1' : (A.val : Set G) ⊆ C.val := h1
    have h2' : (B.val : Set G) ⊆ C.val := h2
    have hsub : centralizerSet C.val ⊆
        centralizerSet A.val ∩ centralizerSet B.val :=
      Set.subset_inter (centralizerSet_mono h1') (centralizerSet_mono h2')
    show centralizerSet (centralizerSet A.val ∩ centralizerSet B.val) ⊆ C.val
    calc centralizerSet (centralizerSet A.val ∩ centralizerSet B.val)
        ⊆ centralizerSet (centralizerSet C.val) := centralizerSet_mono hsub
      _ = C.val := C.property

/-- Lemma `lem: sub` of Cocke25-1, second half:
$\mathbf{C}_G(S) = \mathbf{C}_G(\langle S \rangle)$. The containment
$\supseteq$: $S \subseteq \langle S \rangle$ and `lem: contain`
(`centralizerSet_mono`). The containment $\subseteq$: $\langle S \rangle$
lands in $\mathbf{C}_G(\{x\})$ for each $x \in \mathbf{C}_G(S)$ ("It follows
inductively", tex line 148). The first half of the lemma
($\mathbf{C}_G(S)$ is a subgroup) is definitional here: mathlib's
`Subgroup.centralizer S` *is* a subgroup. (Mathlib master's
`Subgroup.centralizer_closure` would give this directly; the pinned v4.24.0
lacks it.)

Source (Section `sec: basic`, lemma `lem: sub`, tex lines 141-148):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex -/
theorem centralizerSet_closure (S : Set G) :
    centralizerSet (↑(Subgroup.closure S) : Set G) = centralizerSet S := by
  apply Set.eq_of_subset_of_subset
  · exact fun _ hx w hw =>
      Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hx) w
        (Subgroup.subset_closure hw)
  · intro x hx
    -- $S \subseteq \mathbf{C}_G(\{x\})$, so $\langle S \rangle \leq \mathbf{C}_G(\{x\})$
    have hSK : S ≤ Subgroup.centralizer {x} := fun s hs =>
      Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        exact (Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp hx) s hs).symm
    have hK : Subgroup.closure S ≤ Subgroup.centralizer {x} :=
      (Subgroup.closure_le _).mpr hSK
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hK hw) x rfl).symm

/-- Corollary `cor: bij` / Theorem parts (2)-(3) machinery of Cocke25-1: the map
$\mathbf{C}_G(\cdot)$ restricted to $\mathfrak{C}(G)$, landing in
$\mathfrak{C}(G)$ ($\mathbf{C}_G(T) \in \mathfrak{C}(G)$ by `cor: triple_C`,
via `centralizerSet_mem_centralizers`). -/
def centralizerSelfMap (T : ↥(centralizers G)) : ↥(centralizers G) :=
  ⟨centralizerSet T.val, centralizerSet_mem_centralizers _⟩

/-- Theorem part (3) / Corollary `cor: bij` inverse clause ("with inverse given by
$\mathbf{C}_G(\cdot)$", tex line 260): the restriction of $\mathbf{C}_G$ to
$\mathfrak{C}(G)$ is an involution. -/
theorem centralizerSelfMap_map (T : ↥(centralizers G)) :
    centralizerSelfMap (centralizerSelfMap T) = T := by
  apply Subtype.ext
  exact T.property

/-- Theorem part (2) of Cocke25-1: $\mathbf{C}_G : \mathfrak{C}(G) \to
\mathfrak{C}(G)$ is inclusion-reversing ("an inclusion reversing bijection",
tex line 186). -/
theorem centralizerSelfMap_antitone :
    Antitone (centralizerSelfMap (G := G)) := fun _ _ h =>
  centralizerSet_mono h

/-- Corollary `cor: bij` of Cocke25-1: $\mathbf{C}_G(\cdot) : \mathfrak{C}(G)
\to \mathfrak{C}(G)$ is a bijection.

Source (Section `sec: op`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
lines 259-261. -/
theorem centralizerSelfMap_bijective :
    Function.Bijective (centralizerSelfMap (G := G)) :=
  ⟨Function.Involutive.injective centralizerSelfMap_map, fun y =>
    ⟨centralizerSelfMap y, centralizerSelfMap_map y⟩⟩

end Cocke25_1
