import McCulloch26_2.Thm3.Helpers
import McCulloch26_2.Thm3.Branch1
import McCulloch26_2.Thm3.Branch2
import McCulloch26_2.Thm3.Branch3

/-!
# Theorem 3 of McCulloch26-2

No odd prime can equal `|Aut(G)|/|G|` for a finite abelian group `G`.
-/

namespace McCulloch26_2

open scoped Nat

variable {N : ℕ}

theorem thm3 (pp : Fin N → ℕ) (nn : Fin N → ℕ)
    (ff : ∀ i, Fin (nn i) → ℕ)
    (hpp : ∀ i, (pp i).Prime) (hs : ∀ i, Sorted (ff i))
    (hpos : ∀ i, Pos (ff i)) (hN : ∀ i, 0 < nn i)
    (hd : Function.Injective pp) (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) :
    TotalRatio pp nn ff ≠ (p : ℚ) := by
  intro hEq
  by_cases h2_odd : ∃ i j : Fin N, i ≠ j ∧ Odd (pp i) ∧ Odd (pp j)
  · obtain ⟨i, j, hij, hi, hj⟩ := h2_odd
    exact thm3_branch_two_odd_components pp nn ff hpp hs hpos hN hd p hp hodd
      hij hi hj hEq
  · by_cases h1_odd : ∃ j : Fin N, Odd (pp j)
    · have h_single : ∃ j : Fin N, Odd (pp j) ∧ ∀ i, Odd (pp i) → i = j := by
        obtain ⟨j, hj⟩ := h1_odd
        refine ⟨j, hj, fun i hi => ?_⟩
        by_contra hij; exact h2_odd ⟨i, j, hij, hi, hj⟩
      exact thm3_branch_one_odd_component pp nn ff hpp hs hpos hN hd p hp hodd
        h_single hEq
    · have h_none : ∀ i, ¬ Odd (pp i) := fun i h => h1_odd ⟨i, h⟩
      have h_eq2 : ∀ i, pp i = 2 := fun i => by
        rcases (Nat.Prime.eq_two_or_odd' (hpp i)) with h | h
        · exact h
        · exact absurd h (h_none i)
      exact thm3_branch_no_odd_components pp nn ff hpp hs hpos hN hd p hp hodd
        h_eq2 hEq

end McCulloch26_2
