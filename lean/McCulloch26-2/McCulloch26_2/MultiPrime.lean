import McCulloch26_2.PropReal

/-!
# Multi-prime decompositions; Theorems 1 and 2 (data level)

The paper multiplies per-prime ratios across the fundamental-theorem
decomposition (paper line 172: `|Aut(G)|/|G| = Π_i |Aut(G_i)|/|G_i|`), which
is definitional at the data level since distinct primes never interact.

## References

Source: /home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines
115-125 (Theorems 1-3) and line 172 (the multiplicativity argument).
-/

namespace McCulloch26_2

open scoped Nat

variable {N : ℕ}

/-- Total ratio of a decomposition into components `(pp i, ff i)` with
distinct primes; models the ratio of `G₁ × ⋯ × G_N` from the paper's
reduction (paper line 172; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex line 172). -/
def TotalRatio (pp : Fin N → ℕ) (nn : Fin N → ℕ) (ff : ∀ i : Fin N, Fin (nn i) → ℕ) : ℚ :=
  ∏ i : Fin N, autRatio (pp i) (ff i)

/-- Pointwise divisibility lifts to products. -/
theorem prod_dvd_prod_of_pointwise {ι : Type*} (s : Finset ι) (d g : ι → ℕ)
    (h : ∀ i ∈ s, d i ∣ g i) : ∏ i ∈ s, d i ∣ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dvd_rfl
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx]
    exact Nat.mul_dvd_mul (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The reduced denominator of a finite product of rationals divides the
product of the reduced denominators. -/
theorem den_prod_dvd {ι : Type*} (s : Finset ι) (r : ι → ℚ) :
    (∏ i ∈ s, r i).den ∣ ∏ i ∈ s, (r i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx]
    exact Nat.dvd_trans (Rat.mul_den_dvd _ _) (Nat.mul_dvd_mul_left _ ih)

theorem coprime_primes_ne {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (h : a ≠ b) :
    Nat.Coprime a b := by
  refine Nat.coprime_iff_gcd_eq_one.mpr ?_
  have h1 : Nat.gcd a b ∣ a := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd a b ∣ b := Nat.gcd_dvd_right _ _
  rcases ha.eq_one_or_self_of_dvd _ h1 with hg | hg
  · exact hg
  · exfalso
    rw [hg] at h2
    rcases hb.eq_one_or_self_of_dvd _ h2 with hc | hc
    · exact ha.ne_one hc
    · exact h hc

/-- A product of pairwise distinct primes is squarefree. -/
theorem squarefree_prod_distinct {ι : Type*} (s : Finset ι) (pp : ι → ℕ)
    (hpp : ∀ i ∈ s, (pp i).Prime)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → pp i ≠ pp j) :
    Squarefree (∏ i ∈ s, pp i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    have hcop : (pp x).Coprime (∏ i ∈ s, pp i) :=
      Nat.Coprime.prod_right fun j hj =>
        have hxj : x ≠ j := fun heq => hx (heq ▸ hj)
        coprime_primes_ne (hpp x (Finset.mem_insert_self x s))
          (hpp j (Finset.mem_insert_of_mem hj))
          (hdist x (Finset.mem_insert_self x s) j
            (Finset.mem_insert_of_mem hj) hxj)
    refine (Nat.squarefree_mul hcop).mpr
      ⟨(hpp x (Finset.mem_insert_self x s)).squarefree,
        ih (fun i hi => hpp i (Finset.mem_insert_of_mem hi)) ?_⟩
    intro i hi j hj hij hcon
    exact absurd hcon (hdist i (Finset.mem_insert_of_mem hi) j
      (Finset.mem_insert_of_mem hj) hij)

/-- **Theorem 1** (`Intro thm 1`) of McCulloch26-2, data level: the reduced
denominator of the total ratio of a decomposition into distinct-prime
components is squarefree. Paper lines 115-117 with argument at line 172;
source: /home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines
115-117, 172. -/
theorem thm1_data {N : ℕ} (pp : Fin N → ℕ) (nn : Fin N → ℕ)
    (ff : ∀ i : Fin N, Fin (nn i) → ℕ)
    (hpp : ∀ i, (pp i).Prime) (hd : Function.Injective pp)
    (hs : ∀ i, Sorted (ff i)) (hpos : ∀ i, Pos (ff i)) (hN : ∀ i, 0 < nn i) :
    Squarefree (TotalRatio pp nn ff).den := by
  have hcomp : ∀ i : Fin N, (autRatio (pp i) (ff i)).den ∣ pp i := fun i =>
    den_autRatio_dvd (hpp i) (hs i) (hpos i) (hN i)
  have hdvd1 : (TotalRatio pp nn ff).den ∣ ∏ i : Fin N, (autRatio (pp i) (ff i)).den :=
    den_prod_dvd _ (fun i => autRatio (pp i) (ff i))
  have hdvd : (TotalRatio pp nn ff).den ∣ ∏ i : Fin N, pp i :=
    hdvd1.trans (prod_dvd_prod_of_pointwise Finset.univ
      (fun i => (autRatio (pp i) (ff i)).den) (fun i => pp i)
      fun i _ => hcomp i)
  exact Squarefree.squarefree_of_dvd hdvd (squarefree_prod_distinct _ pp
    (fun i _ => hpp i)
    (fun i _hi j _hj hij hcon => absurd (hd hcon) hij))

/-! ### Small sortedness / positivity helpers for explicit sequences -/

theorem sorted_pair_succ (v : ℕ) : Sorted (![v, v + 1] : Fin 2 → ℕ) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have vi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  have vj : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
  have e0 : (![v, v + 1] : Fin 2 → ℕ) 0 = v := rfl
  have e1 : (![v, v + 1] : Fin 2 → ℕ) 1 = v + 1 := rfl
  rcases vi with hv | hv
  · rw [show i = 0 from Fin.val_injective hv]
    rcases vj with hw | hw
    · rw [show j = 0 from Fin.val_injective hw]; try omega
    · rw [show j = 1 from Fin.val_injective hw]; try omega
  · rw [show i = 1 from Fin.val_injective hv]
    rcases vj with hw | hw
    · rw [show j = 0 from Fin.val_injective hw]; try omega
    · rw [show j = 1 from Fin.val_injective hw]; try omega

theorem pos_pair_succ (v : ℕ) (hv : 0 < v) : Pos (![v, v + 1] : Fin 2 → ℕ) := by
  intro i
  have hi := i.isLt
  have vi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  have e0 : (![v, v + 1] : Fin 2 → ℕ) 0 = v := rfl
  have e1 : (![v, v + 1] : Fin 2 → ℕ) 1 = v + 1 := rfl
  rcases vi with hw | hw
  · rw [show i = 0 from Fin.val_injective hw]; try omega
  · rw [show i = 1 from Fin.val_injective hw]; try omega

theorem sorted_triple_inc (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    Sorted (![a, b, c] : Fin 3 → ℕ) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have vi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by omega
  have vj : (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 := by omega
  have e0 : (![a, b, c] : Fin 3 → ℕ) 0 = a := rfl
  have e1 : (![a, b, c] : Fin 3 → ℕ) 1 = b := rfl
  have e2 : (![a, b, c] : Fin 3 → ℕ) 2 = c := rfl
  rcases vi with hv | hv | hv
  · rw [show i = 0 from Fin.val_injective hv]
    rcases vj with hw | hw | hw
    · rw [show j = 0 from Fin.val_injective hw]; try omega
    · rw [show j = 1 from Fin.val_injective hw]; try omega
    · rw [show j = 2 from Fin.val_injective hw]; try omega
  · rw [show i = 1 from Fin.val_injective hv]
    rcases vj with hw | hw | hw
    · rw [show j = 0 from Fin.val_injective hw]; try omega
    · rw [show j = 1 from Fin.val_injective hw]; try omega
    · rw [show j = 2 from Fin.val_injective hw]; try omega
  · rw [show i = 2 from Fin.val_injective hv]
    rcases vj with hw | hw | hw
    · rw [show j = 0 from Fin.val_injective hw]; try omega
    · rw [show j = 1 from Fin.val_injective hw]; try omega
    · rw [show j = 2 from Fin.val_injective hw]; try omega

theorem pos_triple_inc (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Pos (![a, b, c] : Fin 3 → ℕ) := by
  intro i
  have hi := i.isLt
  have vi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by omega
  have ea : (![a, b, c] : Fin 3 → ℕ) 0 = a := rfl
  have eb : (![a, b, c] : Fin 3 → ℕ) 1 = b := rfl
  have ec : (![a, b, c] : Fin 3 → ℕ) 2 = c := rfl
  rcases vi with hv | hv | hv
  · rw [show i = 0 from Fin.val_injective hv]; first | exact ha | omega
  · rw [show i = 1 from Fin.val_injective hv]; first | exact hb | omega
  · rw [show i = 2 from Fin.val_injective hv]; first | exact hc | omega

theorem injective_fin_one {q : ℕ} : Function.Injective (fun _ : Fin 1 => q) := by
  intro a b _
  fin_cases a
  fin_cases b
  rfl

set_option maxHeartbeats 1600000 in
/-- Item 2 of Proposition 2.2 (paper line 143; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 139-147):
`Z_2 × Z_{2^{m+2}} × Z_{2^{m+3}}` has ratio `2^{2m+5}` (the paper's
`2^{2i+1}` with `i = m+2 ≥ 2`). -/
theorem prop_real_1_2 (m : ℕ) :
    autRatio 2 (![1, m + 2, m + 3] : Fin 3 → ℕ) = (2 : ℚ) ^ (2 * m + 5) := by
  have hseq0 : (![1, m + 2, m + 3] : Fin 3 → ℕ) 0 = 1 := rfl
  have hseq1 : (![1, m + 2, m + 3] : Fin 3 → ℕ) 1 = m + 2 := rfl
  have hseq2 : (![1, m + 2, m + 3] : Fin 3 → ℕ) 2 = m + 3 := rfl
  obtain ⟨bt0, bb0, bt1, bb1, bt2, bb2⟩ :=
    block_self_triple (a := 1) (b := m + 2) (c := m + 3) (by omega) (by omega)
  have bb0v : (BlockBot (![1, m + 2, m + 3] : Fin 3 → ℕ) 0).val = 0 := by
    rw [bb0]; rfl
  have bb1v : (BlockBot (![1, m + 2, m + 3] : Fin 3 → ℕ) 1).val = 1 := by
    rw [bb1]; rfl
  have bb2v : (BlockBot (![1, m + 2, m + 3] : Fin 3 → ℕ) 2).val = 2 := by
    rw [bb2]; rfl
  have hP1 : ProdOne 2 (![1, m + 2, m + 3] : Fin 3 → ℕ) = 8 := by
    unfold ProdOne
    rw [Fin.prod_univ_three, bt0, bt1, bt2]
    have z0 : ((0 : Fin 3) : ℕ) = 0 := rfl
    have z1 : ((1 : Fin 3) : ℕ) = 1 := rfl
    have z2 : ((2 : Fin 3) : ℕ) = 2 := rfl
    norm_num
  have hP2 : ProdTwo 2 (![1, m + 2, m + 3] : Fin 3 → ℕ) = 2 ^ (m + 4) := by
    unfold ProdTwo
    have z0 : ((0 : Fin 3) : ℕ) = 0 := rfl
    have z1 : ((1 : Fin 3) : ℕ) = 1 := rfl
    have z2 : ((2 : Fin 3) : ℕ) = 2 := rfl
    rw [Fin.prod_univ_three, bt0, bt1, bt2, hseq0, hseq1, hseq2, z0, z1, z2,
      show ((m + 3) * (Nat.succ 2 - 1 - 2) = 0) from by norm_num,
      show ((1 : ℕ) * (Nat.succ 2 - 1 - 0) = 2) from by norm_num,
      show ((m + 2) * (Nat.succ 2 - 1 - 1) = m + 2) from by ring]
    norm_num
    rw [show ((4 : ℕ) * 2 ^ (m + 2) = 2 ^ (m + 4)) from by
      rw [show ((4 : ℕ) = 2 ^ 2) from by norm_num, ← Nat.pow_add]
      congr 1
      omega]
  have hP3 : ProdThree 2 (![1, m + 2, m + 3] : Fin 3 → ℕ) = 2 ^ (3 * m + 4) := by
    unfold ProdThree
    rw [Fin.prod_univ_three, bb0v, bb1v, bb2v, hseq0, hseq1, hseq2,
      show ((1 - 1) * (Nat.succ 2 - 0) = 0) from by norm_num]
    norm_num
    rw [← Nat.pow_add]
    congr 1
    omega
  have hGC : GroupCard 2 (![1, m + 2, m + 3] : Fin 3 → ℕ) = 2 ^ (2 * m + 6) := by
    unfold GroupCard
    rw [Fin.sum_univ_three, hseq0, hseq1, hseq2]
    congr 1
    ring
  have hAF : AutFormula 2 (![1, m + 2, m + 3] : Fin 3 → ℕ) = 2 ^ (4 * m + 11) := by
    have hprod : AutFormula 2 (![1, m + 2, m + 3] : Fin 3 → ℕ)
        = ProdOne 2 (![1, m + 2, m + 3] : Fin 3 → ℕ)
          * ProdTwo 2 (![1, m + 2, m + 3] : Fin 3 → ℕ)
          * ProdThree 2 (![1, m + 2, m + 3] : Fin 3 → ℕ) := rfl
    have e8 : ((8 : ℕ) * 2 ^ (m + 4) = 2 ^ (m + 7)) := by
      rw [show ((8 : ℕ) = 2 ^ 3) from by norm_num, ← Nat.pow_add]
      congr 1
      omega
    rw [hprod, hP1, hP2, hP3, e8, ← Nat.pow_add]
    congr 1
    ring
  unfold autRatio
  rw [hAF, hGC]
  have hb : (((2:ℕ) ^ (2 * m + 6) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ (by norm_num : (2:ℕ) ≠ 0)
  have kmul : (2:ℚ) ^ (2 * m + 5) * (2:ℚ) ^ (2 * m + 6) = (2:ℚ) ^ (4 * m + 11) := by
    rw [← pow_add]
    congr 1
    omega
  rw [div_eq_iff hb]
  rw [Nat.cast_pow, Nat.cast_pow]
  exact kmul.symm

/-! ### Theorem 2 (data level): every power of 2 is realized -/

/-- A decomposition is a list of `(p, es)` pairs: the prime `p` and the
exponent sequence `es` of its $p$-part. -/
abbrev Decomp := List (ℕ × List ℕ)

/-- A nonempty exponent list viewed as a `Fin`-indexed sequence. -/
def listVec (es : List ℕ) : Fin es.length → ℕ := fun i => es.getD (i : ℕ) 0

theorem listVec_single (v : ℕ) : listVec [v] = (![v] : Fin 1 → ℕ) := by
  funext k
  have hk := k.isLt
  have hl : ([v].length : ℕ) = 1 := rfl
  have hm : (0 : ℕ) < [v].length := by rw [hl]; decide
  have hz : (k : ℕ) = 0 := by omega
  have hkeq : k = ⟨0, hm⟩ := Fin.ext hz
  subst hkeq
  rfl

theorem listVec_pair (a b : ℕ) : listVec [a, b] = (![a, b] : Fin 2 → ℕ) := by
  funext k
  have hk := k.isLt
  have hl : ([a, b].length : ℕ) = 2 := rfl
  have h0 : (0 : ℕ) < [a, b].length := by rw [hl]; decide
  have h1 : (1 : ℕ) < [a, b].length := by rw [hl]; decide
  rcases Nat.lt_or_ge (k : ℕ) 1 with h | h
  · have hz : (k : ℕ) = 0 := by omega
    have hkeq : k = ⟨0, h0⟩ := Fin.ext hz
    subst hkeq
    rfl
  · have hz : (k : ℕ) = 1 := by omega
    have hkeq : k = ⟨1, h1⟩ := Fin.ext hz
    subst hkeq
    rfl

theorem listVec_triple (a b c : ℕ) : listVec [a, b, c] = (![a, b, c] : Fin 3 → ℕ) := by
  funext k
  have hk := k.isLt
  have hl : ([a, b, c].length : ℕ) = 3 := rfl
  have h0 : (0 : ℕ) < [a, b, c].length := by rw [hl]; decide
  have h1 : (1 : ℕ) < [a, b, c].length := by rw [hl]; decide
  have h2 : (2 : ℕ) < [a, b, c].length := by rw [hl]; decide
  rcases Nat.lt_or_ge (k : ℕ) 1 with h | h
  · have hz : (k : ℕ) = 0 := by omega
    have hkeq : k = ⟨0, h0⟩ := Fin.ext hz
    subst hkeq
    rfl
  · rcases Nat.lt_or_ge (k : ℕ) 2 with h2 | h2
    · have hz : (k : ℕ) = 1 := by omega
      have hkeq : k = ⟨1, by omega⟩ := Fin.ext hz
      subst hkeq
      rfl
    · have hz : (k : ℕ) = 2 := by omega
      have hkeq : k = ⟨2, by omega⟩ := Fin.ext hz
      subst hkeq
      rfl

/-- Total ratio of a list decomposition (paper line 172: the total ratio is
the product of the per-prime ratios). -/
def TotalRatioL (L : Decomp) : ℚ :=
  (L.map fun c => autRatio c.1 (listVec c.2)).prod

/-- **Theorem 2** (`Intro thm 2`) of McCulloch26-2, data level: every power of
2 occurs as the total ratio of some explicit decomposition. Even powers come
from item 1 of Proposition 2.2, odd powers `≥ 32` from item 2, and `2`, `8`
from the cross-prime witnesses of items 3 and 4. Paper lines 119-121 with
proof sketch at line 137; source:
/home/chz/src/gamskil/docs/arxiv/2603.29299/An_Answer.tex lines 119-121, 137. -/
theorem sorted_single (l : Fin 1 → ℕ) : Sorted l := by
  intro i j _
  have hi := i.isLt
  have hj := j.isLt
  have h : i = j := Fin.val_injective (by omega)
  subst h
  exact le_refl _

theorem pos_single {l : Fin 1 → ℕ} (hv : 0 < l 0) : Pos l := by
  intro i
  have hi := i.isLt
  have h0 : ((0 : Fin 1) : ℕ) = 0 := rfl
  have hz : i = (0 : Fin 1) := Fin.val_injective (by omega)
  subst hz
  exact hv

theorem thm2_data :
    ∀ k : ℕ, ∃ L : Decomp,
      (∀ c ∈ L, c.1.Prime) ∧
      (∀ c ∈ L, Sorted (listVec c.2)) ∧
      (∀ c ∈ L, Pos (listVec c.2)) ∧
      TotalRatioL L = (2 : ℚ) ^ k := by
  intro k
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨t, ht⟩
  · -- even: item 1 with `Z_{2^{m+1}} × Z_{2^{m+2}}`
    refine ⟨[(2, [m + 1, m + 2])], ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      exact hc.symm ▸ Nat.prime_two
    · intro c hc
      rw [List.mem_singleton] at hc
      rw [hc, listVec_pair]
      exact sorted_pair_succ _
    · intro c hc
      rw [List.mem_singleton] at hc
      rw [hc, listVec_pair]
      exact pos_pair_succ _ (by norm_num)
    simp only [TotalRatioL, List.map_cons, List.prod_singleton, List.map_nil,
      List.prod_nil]
    rw [listVec_pair, prop_real_1_1 m, hm]
    congr 1
    omega
  · rcases Nat.lt_or_ge k 5 with hk | hk
    · have h13 : k = 1 ∨ k = 3 := by omega
      rcases h13 with rfl | rfl
      · -- k = 1: Z_2 × Z_3 × Z_9 has total ratio 2 (item 3)
        refine ⟨[(2, [1]), (3, [1, 2])], ?_, ?_, ?_, ?_⟩
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hmem
          · exact Nat.prime_two
          · rw [List.mem_singleton] at hmem
            exact hmem.symm ▸ Nat.prime_three
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hmem
          · rw [listVec_single]
            exact sorted_single _
          · rw [List.mem_singleton] at hmem
            rw [hmem, listVec_pair]
            exact sorted_pair_succ 1
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hmem
          · rw [listVec_single]
            exact pos_single (by norm_num)
          · rw [List.mem_singleton] at hmem
            rw [hmem, listVec_pair]
            exact pos_pair_succ 1 (by norm_num)
        simp only [TotalRatioL, List.map_cons, List.prod_singleton, List.map_nil,
          List.prod_nil]
        rw [listVec_single, listVec_pair,
          ratio_case_cyclic Nat.prime_two (pos_single (by norm_num)),
          ratio_case_two_dist Nat.prime_three rfl (by norm_num)]
        norm_num [pow_one]
      · -- k = 3: Z_2 × Z_5 × Z_25 has total ratio 8 (item 4)
        refine ⟨[(2, [1]), (5, [1, 2])], ?_, ?_, ?_, ?_⟩
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hmem
          · exact Nat.prime_two
          · rw [List.mem_singleton] at hmem
            exact hmem.symm ▸ Nat.prime_five
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hmem
          · rw [listVec_single]
            exact sorted_single _
          · rw [List.mem_singleton] at hmem
            rw [hmem, listVec_pair]
            exact sorted_pair_succ 1
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hmem
          · rw [listVec_single]
            exact pos_single (by norm_num)
          · rw [List.mem_singleton] at hmem
            rw [hmem, listVec_pair]
            exact pos_pair_succ 1 (by norm_num)
        simp only [TotalRatioL, List.map_cons, List.prod_singleton, List.map_nil,
          List.prod_nil]
        rw [listVec_single, listVec_pair,
          ratio_case_cyclic Nat.prime_two (pos_single (by norm_num)),
          ratio_case_two_dist Nat.prime_five rfl (by norm_num)]
        norm_num [pow_one]
    · -- k = 2t+1 ≥ 5: item 2 with shifted exponents
      refine ⟨[(2, [1, (t - 2) + 2, (t - 2) + 3])], ?_, ?_, ?_, ?_⟩
      · intro c hc
        rw [List.mem_singleton] at hc
        exact hc.symm ▸ Nat.prime_two
      · intro c hc
        rw [List.mem_singleton] at hc
        rw [hc, listVec_triple]
        exact sorted_triple_inc 1 ((t - 2) + 2) ((t - 2) + 3) (by omega) (by omega)
      · intro c hc
        rw [List.mem_singleton] at hc
        rw [hc, listVec_triple]
        refine pos_triple_inc 1 ((t - 2) + 2) ((t - 2) + 3) (by omega) ?_ (by omega)
        have ht5 : 5 ≤ k := hk
        omega
      simp only [TotalRatioL, List.map_cons, List.prod_singleton, List.map_nil,
        List.prod_nil]
      rw [listVec_triple, prop_real_1_2 (t - 2), ht]
      congr 1
      omega

end McCulloch26_2
