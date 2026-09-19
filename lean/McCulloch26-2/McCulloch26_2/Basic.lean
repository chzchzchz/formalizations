import Mathlib.Tactic

/-!
# Exponent-sequence model for McCulloch26-2

A finite abelian `p`-group type is modeled by its sorted exponent sequence
`f : Fin n → ℕ`, standing for `G ≅ Z_{p^{f 0}} × ⋯ × Z_{p^{f (n-1)}}`.
This file defines sortedness, positivity, the block indices of
Proposition `prop: form`, the three products of the Hillar-Rhea formula, the
group order, and the ratio `|Aut(G)| / |G|`.

## References

Proposition `prop: form` (the formula for `|Aut(G)|`), its block indices
`d_r = max{s : e_s = e_r}`, `c_r = min{s : e_s = e_r}`, and the positivity /
sortedness conventions `1 ≤ e_1 ≤ ⋯ ≤ e_n` are from Ryan McCulloch,
*An answer regarding automorphisms of finite abelian groups*, arXiv:2603.29299.
Source: /home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 131-135
(cited there to Hillar-Rhea, Amer. Math. Monthly 114 (2007), 917-923,
bibliography line 198).
-/

namespace McCulloch26_2

/-- Sortedness of an exponent sequence (paper line 134: `1 ≤ e_1 ≤ ⋯ ≤ e_n`;
source: /home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines
133-135). -/
def Sorted {n : ℕ} (f : Fin n → ℕ) : Prop := ∀ i j : Fin n, (i : ℕ) ≤ j → f i ≤ f j

/-- Positivity of an exponent sequence (paper line 134: `1 ≤ e_i`; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 133-135). -/
def Pos {n : ℕ} (f : Fin n → ℕ) : Prop := ∀ i, 0 < f i

variable {n : ℕ}

/-- Block top index of `r`: the paper's `d_r = max{s : e_s = e_r}`
(paper line 134; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 133-135),
as a zero-based index. -/
def BlockTop (f : Fin n → ℕ) (r : Fin n) : Fin n :=
  (Finset.univ.filter fun s => f s = f r).max'
    ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, rfl⟩⟩

/-- Block bottom index of `r`: the paper's `c_r = min{s : e_s = e_r}`
(paper line 134; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 133-135),
as a zero-based index. -/
def BlockBot (f : Fin n → ℕ) (r : Fin n) : Fin n :=
  (Finset.univ.filter fun s => f s = f r).min'
    ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, rfl⟩⟩

/-- `BlockTop` carries the same value as `r` (it lies in the filtered block). -/
theorem block_top_self (f : Fin n → ℕ) (r : Fin n) : f (BlockTop f r) = f r :=
  (Finset.mem_filter.mp (Finset.max'_mem (Finset.univ.filter fun s => f s = f r)
    ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, rfl⟩⟩)).2

/-- Any index with the same value sits below the block top
(`d_r = max{s : e_s = e_r}`). -/
theorem le_block_top (f : Fin n → ℕ) {s r : Fin n} (h : f s = f r) : s ≤ BlockTop f r :=
  Finset.le_max' _ s (Finset.mem_filter.mpr ⟨Finset.mem_univ s, h⟩)

/-- `BlockBot` carries the same value as `r`. -/
theorem block_bot_self (f : Fin n → ℕ) (r : Fin n) : f (BlockBot f r) = f r :=
  (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter fun s => f s = f r)
    ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, rfl⟩⟩)).2

/-- The block bottom sits below any same-valued index
(`c_r = min{s : e_s = e_r}`). -/
theorem block_bot_le (f : Fin n → ℕ) {s r : Fin n} (h : f s = f r) : BlockBot f r ≤ s :=
  Finset.min'_le _ s (Finset.mem_filter.mpr ⟨Finset.mem_univ s, h⟩)

/-- The block top is never below `r`. -/
theorem block_top_ge (f : Fin n → ℕ) (r : Fin n) : r ≤ BlockTop f r :=
  le_block_top f rfl

/-- The block bottom is never above `r`. -/
theorem block_bot_le' (f : Fin n → ℕ) (r : Fin n) : BlockBot f r ≤ r :=
  block_bot_le f rfl

/-- If no later index shares `r`'s value, `r` is its own block top. -/
theorem block_top_eq_self (f : Fin n → ℕ) (r : Fin n)
    (h : ∀ s, r < s → f s ≠ f r) : BlockTop f r = r := by
  unfold BlockTop
  refine le_antisymm ?_ (le_block_top f rfl)
  refine Finset.max'_le (Finset.univ.filter fun s => f s = f r)
    ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, rfl⟩⟩ r ?_
  intro s hs
  by_contra hge
  push_neg at hge
  have hval : (r : ℕ) < (s : ℕ) := by have := s.isLt; omega
  exact h s (Fin.lt_iff_val_lt_val.mpr hval) (Finset.mem_filter.mp hs).2

/-- If no earlier index shares `r`'s value, `r` is its own block bottom. -/
theorem block_bot_eq_self (f : Fin n → ℕ) (r : Fin n)
    (h : ∀ s, s < r → f s ≠ f r) : BlockBot f r = r := by
  unfold BlockBot
  refine le_antisymm (block_bot_le f rfl) ?_
  refine Finset.le_min' (Finset.univ.filter fun s => f s = f r)
    ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, rfl⟩⟩ r ?_
  intro s hs
  by_contra hle
  push_neg at hle
  have hval : (s : ℕ) < (r : ℕ) := by have := s.isLt; omega
  exact h s (Fin.lt_iff_val_lt_val.mpr hval) (Finset.mem_filter.mp hs).2

/-- On a constant pair every block top is the second index. -/
theorem block_top_pair_const {a : ℕ} {f : Fin 2 → ℕ} (hv : ∀ k, f k = a) (k : Fin 2) :
    BlockTop f k = ⟨1, by norm_num⟩ := by
  unfold BlockTop
  refine le_antisymm
    (Finset.max'_le (Finset.univ.filter fun s => f s = f k)
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, rfl⟩⟩ ⟨1, by norm_num⟩
      fun s _ => Fin.le_def.2 (by fin_cases s <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
          omega))
    (le_block_top f ((hv ⟨1, by norm_num⟩).trans (hv k).symm))

/-- On a constant pair every block bottom is the first index. -/
theorem block_bot_pair_const {a : ℕ} {f : Fin 2 → ℕ} (hv : ∀ k, f k = a) (k : Fin 2) :
    BlockBot f k = 0 := by
  have heq : f 0 = f k := by rw [hv 0, hv k]
  have h0mem : (0 : Fin 2) ∈ Finset.univ.filter (fun s => f s = f k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ 0, heq⟩
  unfold BlockBot
  refine le_antisymm (block_bot_le f heq)
    (Finset.le_min' _ ⟨0, h0mem⟩ (0 : Fin 2) fun s _ => s.zero_le)

/-- On a constant triple every block top is the third index. -/
theorem block_top_triple_const {a : ℕ} {f : Fin 3 → ℕ} (hv : ∀ k, f k = a) (k : Fin 3) :
    BlockTop f k = ⟨2, by norm_num⟩ := by
  unfold BlockTop
  refine le_antisymm
    (Finset.max'_le (Finset.univ.filter fun s => f s = f k)
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, rfl⟩⟩ ⟨2, by norm_num⟩
      fun s _ => Fin.le_def.2 (by fin_cases s <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;>
          omega))
    (le_block_top f ((hv ⟨2, by norm_num⟩).trans (hv k).symm))

/-- On a constant triple every block bottom is the first index. -/
theorem block_bot_triple_const {a : ℕ} {f : Fin 3 → ℕ} (hv : ∀ k, f k = a) (k : Fin 3) :
    BlockBot f k = 0 := by
  have heq : f 0 = f k := by rw [hv 0, hv k]
  have h0mem : (0 : Fin 3) ∈ Finset.univ.filter (fun s => f s = f k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ 0, heq⟩
  unfold BlockBot
  refine le_antisymm (block_bot_le f heq)
    (Finset.le_min' _ ⟨0, h0mem⟩ (0 : Fin 3) fun s _ => s.zero_le)

/-! ### The Hillar-Rhea products -/

/-- First product `∏_{k=1}^n (p^{d_k} - p^{k-1})` of Proposition `prop: form`
(paper line 134; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 133-135).
The one-indexed `d_k` and `k - 1` are `(BlockTop f k).val + 1` and
`(k : ℕ)` here. -/
def ProdOne (p : ℕ) {n : ℕ} (f : Fin n → ℕ) : ℕ :=
  ∏ k : Fin n, (p ^ ((BlockTop f k).val + 1) - p ^ (k : ℕ))

/-- Second product `∏_{j=1}^n p^{e_j (n - d_j)}` of Proposition `prop: form`
(paper line 134; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 133-135),
with exponents collected as powers of `p`. -/
def ProdTwo (p : ℕ) {n : ℕ} (f : Fin n → ℕ) : ℕ :=
  ∏ j : Fin n, p ^ (f j * (n - 1 - (BlockTop f j).val))

/-- Third product `∏_{i=1}^n p^{(e_i - 1)(n - c_i + 1)}` of Proposition
`prop: form` (paper line 134; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 133-135),
with exponents collected as powers of `p`. -/
def ProdThree (p : ℕ) {n : ℕ} (f : Fin n → ℕ) : ℕ :=
  ∏ i : Fin n, p ^ ((f i - 1) * (n - (BlockBot f i).val))

/-- The value of Proposition `prop: form`: the formula for `|Aut(G)|`
(paper lines 133-135; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 133-135). -/
def AutFormula (p : ℕ) {n : ℕ} (f : Fin n → ℕ) : ℕ :=
  ProdOne p f * ProdTwo p f * ProdThree p f

/-- The group order `|G| = p^{e_1 + ⋯ + e_n}` (paper line 169 writes
`a = Σ_{i} e_i k_i`; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex line 169). -/
def GroupCard (p : ℕ) {n : ℕ} (f : Fin n → ℕ) : ℕ := p ^ (∑ i : Fin n, f i)

/-- The ratio `|Aut(G)| / |G|` of the paper (abstract, paper line 94;
source: /home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex line 94). -/
def autRatio (p : ℕ) {n : ℕ} (f : Fin n → ℕ) : ℚ := AutFormula p f / GroupCard p f

/-! ### Value-level corollaries of the constant-sequence lemmas -/

theorem block_top_pair_const_val {a : ℕ} {f : Fin 2 → ℕ} (hv : ∀ k, f k = a)
    (k : Fin 2) : (BlockTop f k).val = 1 := by
  rw [block_top_pair_const hv k]

theorem block_bot_pair_const_val {a : ℕ} {f : Fin 2 → ℕ} (hv : ∀ k, f k = a)
    (k : Fin 2) : (BlockBot f k).val = 0 := by
  rw [block_bot_pair_const hv k]
  rfl

theorem block_top_triple_const_val {a : ℕ} {f : Fin 3 → ℕ} (hv : ∀ k, f k = a)
    (k : Fin 3) : (BlockTop f k).val = 2 := by
  rw [block_top_triple_const hv k]

theorem block_bot_triple_const_val {a : ℕ} {f : Fin 3 → ℕ} (hv : ∀ k, f k = a)
    (k : Fin 3) : (BlockBot f k).val = 0 := by
  rw [block_bot_triple_const hv k]
  rfl
