import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Logic.Function.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-!
# Basic definitions for the McCulloch26-1 formalization

The paper's k-fold factorization definition (tex lines 98-103) is encoded as
unique representation: every element of `G` is an ordered product choosing one
factor from each of `A 0, ..., A (k-1)` in exactly one way, which is equivalent
to bijectivity of the multiplication map `A_1 × ⋯ × A_k → G`.

Ordered products are `List.prod (List.ofFn f)` (mathlib's pattern for products
in a noncommutative monoid; `Finset.prod` needs `CommMonoid`).

Source: /home/chz/src/gamskil/docs/arxiv/2607.20569v3/Some_Answers_Factorization.tex
-/

open Set Function

variable {G : Type*} [Group G]

/-- The ordered product of a family of subsets `A : Fin n → Set G`: all elements
of `G` obtainable by choosing one element from each set, multiplied in index
order. -/
def setSeqProd {n : ℕ} (A : Fin n → Set G) : Set G :=
  {x | ∃ f : ∀ i, A i, (List.ofFn fun i => (f i : G)).prod = x}

/-- The family `A` is an `n`-fold factorization of `G` (tex lines 98-103):
every group element has a unique representation as such an ordered product. -/
def IsFactorization {n : ℕ} (A : Fin n → Set G) : Prop :=
  ∀ x : G, ∃! f : ∀ i, A i, (List.ofFn fun i => (f i : G)).prod = x

/-- Splitting an ordered product over `Fin (n + 2)` into first, middle, and
last factors. -/
theorem prod_first_mid_last {M : Type*} [Monoid M] {n : ℕ} (F : Fin (n + 2) → M) :
    (List.ofFn F).prod =
      F 0 * ((List.ofFn fun j : Fin n => F (Fin.castSucc j).succ).prod) *
        F (Fin.last (n + 1)) := by
  have h1 : (List.ofFn F).prod =
      F 0 * (List.ofFn (fun i : Fin (n + 1) => F i.succ)).prod := by
    rw [List.ofFn_succ, List.prod_cons]
  rw [h1]
  have h2 : (List.ofFn fun i : Fin (n + 1) => F i.succ).prod =
      (List.ofFn fun j : Fin n => F (Fin.castSucc j).succ).prod *
        F (Fin.last n).succ := by
    rw [List.ofFn_succ' (f := fun i : Fin (n + 1) => F i.succ), List.prod_concat]
  rw [h2, mul_assoc]
  have hlast : (Fin.last n).succ = Fin.last (n + 1) := rfl
  rw [hlast]

theorem setSeqProd_decomp {n : ℕ} {A : Fin (n + 2) → Set G} {x : G}
    (hx : x ∈ setSeqProd A) :
    ∃ c₀ y c₁, c₀ ∈ A 0 ∧ y ∈ setSeqProd (fun j : Fin n => A (Fin.castSucc j).succ) ∧
      c₁ ∈ A (Fin.last (n + 1)) ∧ x = c₀ * y * c₁ := by
  obtain ⟨f, hf⟩ := hx
  rw [prod_first_mid_last (fun i => (f i : G))] at hf
  refine ⟨(f 0 : G), _, (f (Fin.last (n + 1)) : G), (f 0).2, ⟨fun j => f _, rfl⟩,
    (f (Fin.last (n + 1))).2, hf.symm⟩
