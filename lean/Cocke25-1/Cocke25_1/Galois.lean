import Mathlib.GroupTheory.Subgroup.Centralizer

/-! # The centralizer Galois connection and triple-centralizer collapse

Formalization of the chain `prop: Galois` -> `prop: triple_g` -> `cor: triple_C`
from Cocke25-1 (*A Möbius function on the Centralizer Lattice*,
arXiv:2512.13839v2), Section "The map $\mathbf{C}_G(\cdot)$ and the centralizer
lattice" (`sec: op`).
-/

namespace Cocke25_1

/-- Proposition `prop: Galois` of Cocke25-1: the pair
$(\mathbf{C}_G(\cdot), \mathbf{C}_G(\cdot))$ is an order-reversing Galois
connection between $\mathcal{P}(G)$ and itself.

Encoded as the paper's displayed equivalence
$T \subseteq \mathbf{C}_G(S) \leftrightarrow S \subseteq \mathbf{C}_G(T)$;
both sides say, in the paper's words, "that every element of $S$ commutes with
every element of $T$". Mathlib's monotone `GaloisConnection` would require an
`OrderDual` transport, so the plain iff is used (see `status.md`, "Encoding
deltas").

Source (Section "The map $\mathbf{C}_G(\cdot)$ and the centralizer lattice",
`sec: op`, paragraph introducing Galois connections, then the proposition):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
lines 206-214 (statement at 206-208). -/
theorem centralizer_galois_self_iff {G : Type*} [Group G] (S T : Set G) :
    T ⊆ (Subgroup.centralizer S : Set G) ↔ S ⊆ (Subgroup.centralizer T : Set G) := by
  constructor
  · intro h s hs
    rw [SetLike.mem_coe]
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp (h ht)) s hs).symm
  · intro h t ht
    rw [SetLike.mem_coe]
    exact Subgroup.mem_centralizer_iff.mpr fun s hs =>
      (Subgroup.mem_centralizer_iff.mp (SetLike.mem_coe.mp (h hs)) t ht).symm

/-- Proposition `prop: triple_g` of Cocke25-1: for an order-reversing self-map
$g$ of a poset such that the pair $(g,g)$ is a Galois connection, one has
$g(g(g(S))) = g(S)$ for every $S$.

The hypothesis "(g,g) is an order-reversing Galois connection" is encoded as
the equivalence `∀ a b, b ≤ g a ↔ a ≤ g b`; the concluding equality uses
antisymmetry, hence `PartialOrder` (the paper says poset).

Source (Section `sec: op`, paragraph following `prop: Galois`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
lines 216-228 (statement at 219-221). -/
theorem triple_g {P : Type*} [PartialOrder P] {g : P → P}
    (hg : ∀ a b, b ≤ g a ↔ a ≤ g b) (x : P) : g (g (g x)) = g x := by
  have unit : ∀ x : P, x ≤ g (g x) := fun x => (hg x (g x)).mp le_rfl
  have anti_mono : ∀ a b : P, a ≤ b → g b ≤ g a := by
    intro a b h
    exact (hg a (g b)).mpr (le_trans h (unit b))
  exact le_antisymm (anti_mono _ _ (unit x)) ((hg (g x) (g (g x))).mp le_rfl)

/-- Corollary `cor: triple_C` of Cocke25-1: for $G$ a group and $S \subseteq G$,
$\mathbf{C}_G(\mathbf{C}_G(\mathbf{C}_G(S))) = \mathbf{C}_G(S)$.

Proved element-wise from `Subgroup.mem_centralizer_iff`, using that
$S \subseteq \mathbf{C}_G(\mathbf{C}_G(S))$ (mathlib
`Set.subset_centralizer_centralizer`) in the form "any $z \in S$ commutes with
every member of $\mathbf{C}_G(S)$".

Source (Section `sec: op`, corollary following `prop: triple_g`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
lines 229-237 (statement at 229-231). -/
theorem triple_C_centralizer {G : Type*} [Group G] (S : Set G) :
    Subgroup.centralizer (Subgroup.centralizer (Subgroup.centralizer S : Set G) : Set G) =
      Subgroup.centralizer S := by
  ext x
  constructor
  · intro hx z hz
    refine Subgroup.mem_centralizer_iff.mp hx z
      (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    exact (Subgroup.mem_centralizer_iff.mp hy z hz).symm
  · intro hx y hy
    exact (Subgroup.mem_centralizer_iff.mp hy x hx).symm

end Cocke25_1
