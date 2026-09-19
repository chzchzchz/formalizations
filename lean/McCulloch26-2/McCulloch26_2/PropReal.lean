import McCulloch26_2.PropClass

/-!
# Proposition 2.2 of McCulloch26-2: explicit ratios

The four families realizing small ratios (paper lines 139-147). Items are
stated at the data level over the modeled groups; the shifts by `+1` /
`+2` avoid truncated subtraction so that every `m : ℕ` is covered.

## References

Source: /home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines
139-147 (the unlabeled Proposition following `prop: form`).
-/

namespace McCulloch26_2

/-- All four block indices of a strictly increasing pair are the entries
themselves, stated at numeral indices. -/
theorem block_self_pair {a b : ℕ} (h : a < b) :
    BlockTop (![a, b] : Fin 2 → ℕ) 0 = 0 ∧ BlockBot (![a, b] : Fin 2 → ℕ) 0 = 0
      ∧ BlockTop (![a, b] : Fin 2 → ℕ) 1 = 1
      ∧ BlockBot (![a, b] : Fin 2 → ℕ) 1 = 1 := by
  refine ⟨block_top_eq_self (![a, b] : Fin 2 → ℕ) 0 (by
      intro s hs
      fin_cases s
      · simp at hs
      · rw [show (![a, b] : Fin 2 → ℕ) ⟨1, by norm_num⟩ = b from rfl,
          show (![a, b] : Fin 2 → ℕ) 0 = a from rfl]
        exact h.ne'),
    block_bot_eq_self (![a, b] : Fin 2 → ℕ) 0 (by
      intro s hs
      fin_cases s <;> simp at hs),
    block_top_eq_self (![a, b] : Fin 2 → ℕ) 1 (by
      intro s hs
      fin_cases s <;> simp at hs),
    block_bot_eq_self (![a, b] : Fin 2 → ℕ) 1 (by
      intro s hs
      fin_cases s
      · rw [show (![a, b] : Fin 2 → ℕ) ⟨0, by norm_num⟩ = a from rfl,
          show (![a, b] : Fin 2 → ℕ) 1 = b from rfl]
        exact h.ne
      · simp at hs)⟩

/-- All six block indices of a strictly increasing triple are the entries
themselves, stated at numeral indices. -/
theorem block_self_triple {a b c : ℕ} (h1 : a < b) (h2 : b < c) :
    BlockTop (![a, b, c] : Fin 3 → ℕ) 0 = 0 ∧ BlockBot (![a, b, c] : Fin 3 → ℕ) 0 = 0
      ∧ BlockTop (![a, b, c] : Fin 3 → ℕ) 1 = 1
      ∧ BlockBot (![a, b, c] : Fin 3 → ℕ) 1 = 1
      ∧ BlockTop (![a, b, c] : Fin 3 → ℕ) 2 = 2
      ∧ BlockBot (![a, b, c] : Fin 3 → ℕ) 2 = 2 := by
  refine ⟨block_top_eq_self (![a, b, c] : Fin 3 → ℕ) 0 (by
      intro s hs
      fin_cases s
      · simp at hs
      · rw [show (![a, b, c] : Fin 3 → ℕ) ⟨1, by norm_num⟩ = b from rfl,
          show (![a, b, c] : Fin 3 → ℕ) 0 = a from rfl]
        exact h1.ne'
      · rw [show (![a, b, c] : Fin 3 → ℕ) ⟨2, by norm_num⟩ = c from rfl,
          show (![a, b, c] : Fin 3 → ℕ) 0 = a from rfl]
        exact (h1.trans h2).ne'),
    block_bot_eq_self (![a, b, c] : Fin 3 → ℕ) 0 (by
      intro s hs
      fin_cases s <;> simp at hs),
    block_top_eq_self (![a, b, c] : Fin 3 → ℕ) 1 (by
      intro s hs
      fin_cases s
      · simp at hs
      · simp at hs
      · rw [show (![a, b, c] : Fin 3 → ℕ) ⟨2, by norm_num⟩ = c from rfl,
          show (![a, b, c] : Fin 3 → ℕ) 1 = b from rfl]
        exact h2.ne'),
    block_bot_eq_self (![a, b, c] : Fin 3 → ℕ) 1 (by
      intro s hs
      fin_cases s
      · rw [show (![a, b, c] : Fin 3 → ℕ) ⟨0, by norm_num⟩ = a from rfl,
          show (![a, b, c] : Fin 3 → ℕ) 1 = b from rfl]
        exact h1.ne
      · simp at hs
      · simp at hs),
    block_top_eq_self (![a, b, c] : Fin 3 → ℕ) 2 (by
      intro s hs
      fin_cases s <;> simp at hs),
    block_bot_eq_self (![a, b, c] : Fin 3 → ℕ) 2 (by
      intro s hs
      fin_cases s
      · rw [show (![a, b, c] : Fin 3 → ℕ) ⟨0, by norm_num⟩ = a from rfl,
          show (![a, b, c] : Fin 3 → ℕ) 2 = c from rfl]
        exact (h1.trans h2).ne
      · rw [show (![a, b, c] : Fin 3 → ℕ) ⟨1, by norm_num⟩ = b from rfl,
          show (![a, b, c] : Fin 3 → ℕ) 2 = c from rfl]
        exact h2.ne
      · simp at hs)⟩

/-- Item 1 of Proposition 2.2 (paper line 142; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 139-147):
`Z_{2^{m+1}} × Z_{2^{m+2}}` has ratio `2^{2m}` (the paper's `2^{2(i-1)}`
with `i = m+1 ≥ 1`). -/
theorem prop_real_1_1 (m : ℕ) :
    autRatio 2 (![m + 1, m + 2] : Fin 2 → ℕ) = (2 : ℚ) ^ (2 * m) := by
  have hab : (m + 1 : ℕ) < m + 2 := by omega
  obtain ⟨bt0, bb0, bt1, bb1⟩ := block_self_pair hab
  have hP1 : ProdOne 2 (![m + 1, m + 2] : Fin 2 → ℕ) = 2 := by
    unfold ProdOne
    rw [Fin.prod_univ_two, bt0, bt1]
    norm_num
  have hP2 : ProdTwo 2 (![m + 1, m + 2] : Fin 2 → ℕ) = 2 ^ (m + 1) := by
    unfold ProdTwo
    rw [Fin.prod_univ_two, bt0, bt1,
      show (![m + 1, m + 2] : Fin 2 → ℕ) 0 = m + 1 from rfl,
      show (![m + 1, m + 2] : Fin 2 → ℕ) 1 = m + 2 from rfl]
    norm_num
  have bb0v : (BlockBot (![m + 1, m + 2] : Fin 2 → ℕ) 0).val = 0 := by
    rw [bb0]; rfl
  have bb1v : (BlockBot (![m + 1, m + 2] : Fin 2 → ℕ) 1).val = 1 := by
    rw [bb1]; rfl
  have hP3 : ProdThree 2 (![m + 1, m + 2] : Fin 2 → ℕ) = 2 ^ (3 * m + 1) := by
    unfold ProdThree
    rw [Fin.prod_univ_two, bb0v, bb1v,
      show (![m + 1, m + 2] : Fin 2 → ℕ) 0 = m + 1 from rfl,
      show (![m + 1, m + 2] : Fin 2 → ℕ) 1 = m + 2 from rfl,
      show (m + 1 - 1) * (2 - 0) = 2 * m from by omega,
      show (m + 2 - 1) * (2 - 1) = m + 1 from by omega,
      ← Nat.pow_add]
    congr 1
    ring
  have hGC : GroupCard 2 (![m + 1, m + 2] : Fin 2 → ℕ) = 2 ^ (2 * m + 3) := by
    unfold GroupCard
    rw [Fin.sum_univ_two,
      show (![m + 1, m + 2] : Fin 2 → ℕ) 0 = m + 1 from rfl,
      show (![m + 1, m + 2] : Fin 2 → ℕ) 1 = m + 2 from rfl]
    congr 1
    ring
  have hAF : AutFormula 2 (![m + 1, m + 2] : Fin 2 → ℕ) = 2 ^ (4 * m + 3) := by
    rw [show AutFormula 2 (![m + 1, m + 2] : Fin 2 → ℕ)
          = ProdOne 2 (![m + 1, m + 2] : Fin 2 → ℕ) * ProdTwo 2 (![m + 1, m + 2] : Fin 2 → ℕ)
            * ProdThree 2 (![m + 1, m + 2] : Fin 2 → ℕ) from rfl,
      hP1, hP2, hP3]
    have e1 : ((2:ℕ) * 2 ^ (m + 1) = 2 ^ (m + 2)) := by
      rw [show ((2:ℕ) ^ (m + 2) = 2 * 2 ^ (m + 1)) from by
        rw [Nat.pow_succ']]
    rw [e1, ← Nat.pow_add]
    congr 1
    ring
  unfold autRatio
  rw [hAF, hGC]
  have hb : (((2:ℕ) ^ (2 * m + 3) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ (by norm_num : (2:ℕ) ≠ 0)
  have key : (((2:ℕ) ^ (4 * m + 3) : ℕ) : ℚ)
      = (2:ℚ) ^ (2 * m) * (((2:ℕ) ^ (2 * m + 3) : ℕ) : ℚ) := by
    push_cast [Nat.cast_pow]
    rw [← pow_add]
    congr 1
    ring
  rw [key, mul_comm]
  exact mul_div_cancel_left₀ _ hb

end McCulloch26_2
