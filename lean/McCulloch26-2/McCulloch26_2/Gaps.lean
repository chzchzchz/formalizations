import Mathlib.Data.ZMod.Aut
import McCulloch26_2.Basic

/-!
# Gap lemmas of the McCulloch26-2 formalization

The two facts the paper uses but does not prove, kept as explicit `Prop`
-valued gap statements so that every conditional bridge theorem records its
dependence (skills/FORMALIZE.md gap protocol). Nothing in this project proves
them; both are open rows of `status.md`.

## References

* `RheaFormula` — Proposition `prop: form` (paper lines 131-135), cited by
  the paper to Hillar-Rhea, Amer. Math. Monthly 114 (2007), 917-923
  ([aut], bibliography line 198).
  Source: /home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines
  131-135.
* `CoprimeSplit` — `Aut(G × H) = Aut(G) × Aut(H)` for coprime orders, used at
  paper line 172 and line 181 via the fundamental theorem of finite abelian
  groups. Source: /home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex
  line 131.
-/

namespace McCulloch26_2

/-- **Gap lemma G1** — the Hillar-Rhea formula over the real automorphism
group of the modeled group `Π_i Z_{p^{f i}}` (paper lines 131-135; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 131-135).
Statement only; proving it would require counting units of matrix rings over
`Z/p^k`, which mathlib does not provide. -/
def RheaFormula (p : ℕ) {n : ℕ} (f : Fin n → ℕ) : Prop :=
  Nat.card (AddAut ((i : Fin n) → ZMod (p ^ f i))) = AutFormula p f

/-- **Gap lemma G2** — coprime-order splitting of automorphism groups
(paper line 131; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex line 131).
Statement only; candidate route is Hom-triviality between coprime finite
abelian groups. -/
-- Structured framework for CoprimeSplit deferred (FORMALIZE.md G2).
-- The full arithmetic and homomorphism framework is open; statement kept as `CoprimeSplit` Prop below.


def CoprimeSplit (A B : Type*) [AddCommGroup A] [AddCommGroup B] [Fintype A]
    [Fintype B] : Prop :=
  Nat.Coprime (Nat.card A) (Nat.card B) →
    Nat.card (AddAut (A × B)) = Nat.card (AddAut A) * Nat.card (AddAut B)

/-- Under gap lemma G1 for every sequence, the modeled group's automorphism
count is exactly the formula value. -/
theorem rhea_card {p : ℕ} {n : ℕ} {f : Fin n → ℕ}
    (H : ∀ {m : ℕ} (g : Fin m → ℕ), Sorted g → RheaFormula p g) (hs : Sorted f) :
    RheaFormula p f := H f hs

/-- Under gap lemma G1, the actual group's ratio equals the data-level
`autRatio`; this transfers every unconditional data-level classification to
the corresponding concrete group. -/
theorem group_ratio_of_rhea {p : ℕ} {n : ℕ} {f : Fin n → ℕ} (hs : Sorted f)
    (H : ∀ {m : ℕ} (g : Fin m → ℕ), Sorted g → RheaFormula p g) :
    (((Nat.card (AddAut ((i : Fin n) → ZMod (p ^ f i))) : ℕ) : ℚ)) /
        (((GroupCard p f : ℕ) : ℚ)) = autRatio p f := by
  unfold autRatio GroupCard
  rw [H f hs]

end McCulloch26_2
