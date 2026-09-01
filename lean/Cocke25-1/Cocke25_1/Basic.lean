import Cocke25_1.CentLattice

/-! # Basic definitions for the Cocke25-1 formalization

The centralizer operator $\mathbf{C}_G$ is mathlib's `Subgroup.centralizer` on
`Set G`; see `CentLattice.lean` for `centralizerSet`, `cclosure`, `centralizers`,
and `Fibers.lean` for fibers. Definitions below are the element-center notions
of Section `sec: elems`. Each docstring cites the paper definition by full path
+ line (see skills/FORMALIZE.md).
-/

namespace Cocke25_1

variable {G : Type*} [Group G]

/-- The element center $\mathbf{Z}(a) := \mathbf{C}_G(\mathbf{C}_G(a))$ of
$a \in G$. The paper defines it right after Corollary `cor: abelian_cent`,
noting $\mathbf{C}_G(\mathbf{C}_G(a)) = \mathbf{Z}(\mathbf{C}_G(a))$.

Source (Section `sec: elems`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
line 371. -/
def elementCenter (a : G) : Set G := cclosure {a}

/-- The equivalence class $\mathbf{Z}^*(g) := \{ x \in G \mid \mathbf{Z}(x) =
\mathbf{Z}(g) \}$ (equivalently $\{ x \mid \mathbf{C}_G(x) = \mathbf{C}_G(g)\}$,
see `mem_elementCenterClass_iff`). The paper calls these classes $\mathbf{Z}^*$;
$\mathbf{Z}^*(z) = \mathbf{Z}(G)$ for $z \in \mathbf{Z}(G)$ (tex line 375).

Source (Section `sec: elems`):
/home/chz/src/gamskil/docs/arxiv/2512.13839v2/cent_lattice_2025_Lewis_ml_sub__2_.tex
line 373. -/
def elementCenterClass (g : G) : Set G := {x | elementCenter x = elementCenter g}

end Cocke25_1
