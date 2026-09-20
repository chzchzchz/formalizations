import McCulloch26_1.Basic

/-!
# Lemma 2.2 (`lem: e`) of McCulloch26-1

Left/right translation of the end sets preserves factorization, so a
factorization may be assumed to have identity-containing end sets.

Source: /home/chz/src/gamskil/docs/arxiv/2607.20569v3/Some_Answers_Factorization.tex
lines 122-126 (statement), proof transcribed from the printed argument.
-/

open Set

variable {G : Type*} [Group G]

/-- The family whose first set is left-translated by `g` (tex line 123). -/
def endTranslateL (g : G) {n : ℕ} (A : Fin (n + 1) → Set G) : Fin (n + 1) → Set G :=
  fun i => if i = 0 then (fun x => g * x) '' (A i) else A i

/-- The family whose last set is right-translated by `h` (tex line 123). -/
def endTranslateR (h : G) {n : ℕ} (A : Fin (n + 1) → Set G) : Fin (n + 1) → Set G :=
  fun i => if i = Fin.last n then (fun x => x * h) '' (A i) else A i

/-- Both-end translation `(g A_1) · A_2 ⋯ A_{k-1} · (A_k h)` of tex lines
122-123; length ≥ 2 keeps the two translated indices distinct. -/
def endTranslate (g h : G) {n : ℕ} (A : Fin (n + 2) → Set G) : Fin (n + 2) → Set G :=
  endTranslateL g (endTranslateR h A)

theorem prod_update_left (c : G) {n : ℕ} (v : Fin (n + 1) → G) :
    (List.ofFn fun i => if i = 0 then c * v i else v i).prod =
      c * (List.ofFn v).prod := by
  conv_lhs => rw [List.ofFn_succ]
  conv_rhs => rw [List.ofFn_succ]
  simp [mul_assoc]

theorem prod_update_right (c : G) {n : ℕ} (v : Fin (n + 1) → G) :
    (List.ofFn fun i => if i = Fin.last n then v i * c else v i).prod =
      (List.ofFn v).prod * c := by
  conv_lhs => rw [List.ofFn_succ']
  conv_rhs => rw [List.ofFn_succ']
  simp [Fin.castSucc_ne_last, mul_assoc]

theorem mem_endTranslateL {g : G} {n : ℕ} {A : Fin (n + 1) → Set G} {i : Fin (n + 1)}
    {y : G} (hy : y ∈ A i) : (if i = 0 then g * y else y) ∈ endTranslateL g A i := by
  by_cases hi : i = 0
  · subst hi
    unfold endTranslateL
    rw [if_pos rfl, if_pos rfl]
    exact mem_image_of_mem _ hy
  · unfold endTranslateL
    rw [if_neg hi, if_neg hi]
    exact hy

theorem mem_endTranslateR {h : G} {n : ℕ} {A : Fin (n + 1) → Set G} {i : Fin (n + 1)}
    {y : G} (hy : y ∈ A i) :
    (if i = Fin.last n then y * h else y) ∈ endTranslateR h A i := by
  by_cases hi : i = Fin.last n
  · subst hi
    unfold endTranslateR
    rw [if_pos rfl, if_pos rfl]
    exact mem_image_of_mem _ hy
  · unfold endTranslateR
    rw [if_neg hi, if_neg hi]
    exact hy

theorem mem_endTranslateL_inv {g : G} {n : ℕ} {A : Fin (n + 1) → Set G}
    {i : Fin (n + 1)} {y : G} (hy : y ∈ endTranslateL g A i) :
    (if i = 0 then g⁻¹ * y else y) ∈ A i := by
  unfold endTranslateL at hy
  by_cases hi : i = 0
  · have hset : (if i = 0 then (fun x => g * x) '' A i else A i)
        = (fun x => g * x) '' A i := if_pos hi
    rw [hset] at hy
    rw [if_pos hi]
    obtain ⟨z, hz, heq⟩ := hy
    rw [← heq]
    simpa using hz
  · have hset : (if i = 0 then (fun x => g * x) '' A i else A i) = A i :=
      if_neg hi
    rw [hset] at hy
    rw [if_neg hi]
    exact hy

theorem mem_endTranslateR_inv {h : G} {n : ℕ} {A : Fin (n + 1) → Set G}
    {i : Fin (n + 1)} {y : G} (hy : y ∈ endTranslateR h A i) :
    (if i = Fin.last n then y * h⁻¹ else y) ∈ A i := by
  unfold endTranslateR at hy
  by_cases hi : i = Fin.last n
  · have hset : (if i = Fin.last n then (fun x => x * h) '' A i else A i)
        = (fun x => x * h) '' A i := if_pos hi
    rw [hset] at hy
    rw [if_pos hi]
    obtain ⟨z, hz, heq⟩ := hy
    rw [← heq]
    simpa using hz
  · have hset : (if i = Fin.last n then (fun x => x * h) '' A i else A i) =
        A i := if_neg hi
    rw [hset] at hy
    rw [if_neg hi]
    exact hy

theorem isFactorization_endTranslateL (g : G) {n : ℕ} (A : Fin (n + 1) → Set G)
    (hfac : IsFactorization A) : IsFactorization (endTranslateL g A) := by
  intro x
  obtain ⟨v, hv, hvu⟩ := hfac (g⁻¹ * x)
  set u : Fin (n + 1) → G := fun i => if i = 0 then g * (v i : G) else (v i : G) with hudef
  have humem : ∀ i, u i ∈ endTranslateL g A i := fun i => mem_endTranslateL (v i).2
  have huprod : (List.ofFn u).prod = x := by
    rw [hudef]
    have hp := prod_update_left g fun i => (v i : G)
    rw [hp, hv]
    group
  refine ⟨fun i => ⟨u i, humem i⟩, huprod, ?_⟩
  intro w hw
  have hwm : ∀ i, (if i = 0 then g⁻¹ * (w i : G) else (w i : G)) ∈ A i :=
    fun i => mem_endTranslateL_inv (w i).2
  have hprodw :
      (List.ofFn fun i => if i = 0 then g⁻¹ * (w i : G) else (w i : G)).prod =
        g⁻¹ * x := by
    have hpw := prod_update_left g⁻¹ fun i => (w i : G)
    rw [hpw, hw]
  have hEq := hvu (fun i => ⟨if i = 0 then g⁻¹ * (w i : G) else (w i : G),
    hwm i⟩) hprodw
  apply funext
  intro i
  by_cases h0 : i = 0
  · apply Subtype.ext
    have hcval : (g⁻¹ * ↑(w i) : G) = (v i : G) := by
      have t := congrArg Subtype.val (congrFun hEq i)
      simpa [h0] using t
    have huival : u i = g * (v i : G) := by
      show (if i = 0 then g * (v i : G) else (v i : G)) = g * (v i : G)
      rw [if_pos h0]
    calc (↑(w i) : G) = g * (g⁻¹ * ↑(w i)) := by group
      _ = g * (v i : G) := by rw [hcval]
      _ = u i := huival.symm
  · apply Subtype.ext
    have hcval : ((w i : G)) = (v i : G) := by
      have t := congrArg Subtype.val (congrFun hEq i)
      simpa [h0] using t
    have huival : u i = (v i : G) := by
      show (if i = 0 then g * (v i : G) else (v i : G)) = (v i : G)
      rw [if_neg h0]
    calc (↑(w i) : G) = (v i : G) := hcval
      _ = u i := huival.symm

theorem isFactorization_endTranslateR (h : G) {n : ℕ} (A : Fin (n + 1) → Set G)
    (hfac : IsFactorization A) : IsFactorization (endTranslateR h A) := by
  intro x
  obtain ⟨v, hv, hvu⟩ := hfac (x * h⁻¹)
  set u : Fin (n + 1) → G := fun i =>
    if i = Fin.last n then (v i : G) * h else (v i : G) with hudef
  have humem : ∀ i, u i ∈ endTranslateR h A i := fun i => mem_endTranslateR (v i).2
  have huprod : (List.ofFn u).prod = x := by
    rw [hudef]
    have hp := prod_update_right h fun i => (v i : G)
    rw [hp, hv]
    group
  refine ⟨fun i => ⟨u i, humem i⟩, huprod, ?_⟩
  intro w hw
  have hwm : ∀ i,
      (if i = Fin.last n then (w i : G) * h⁻¹ else (w i : G)) ∈ A i :=
    fun i => mem_endTranslateR_inv (w i).2
  have hprodw :
      (List.ofFn fun i =>
          if i = Fin.last n then (w i : G) * h⁻¹ else (w i : G)).prod =
        x * h⁻¹ := by
    have hpw := prod_update_right h⁻¹ fun i => (w i : G)
    rw [hpw, hw]
  have hEq := hvu (fun i =>
    ⟨if i = Fin.last n then (w i : G) * h⁻¹ else (w i : G), hwm i⟩) hprodw
  apply funext
  intro i
  by_cases h0 : i = Fin.last n
  · apply Subtype.ext
    have hcval : ((↑(w i) * h⁻¹ : G)) = (v i : G) := by
      have t := congrArg Subtype.val (congrFun hEq i)
      simpa [h0] using t
    have huival : u i = (v i : G) * h := by
      show (if i = Fin.last n then (v i : G) * h else (v i : G)) = (v i : G) * h
      rw [if_pos h0]
    calc (↑(w i) : G) = ((↑(w i) * h⁻¹) * h) := by group
      _ = (v i : G) * h := by rw [hcval]
      _ = u i := huival.symm
  · apply Subtype.ext
    have hcval : ((w i : G)) = (v i : G) := by
      have t := congrArg Subtype.val (congrFun hEq i)
      simpa [h0] using t
    have huival : u i = (v i : G) := by
      show (if i = Fin.last n then (v i : G) * h else (v i : G)) = (v i : G)
      rw [if_neg h0]
    calc (↑(w i) : G) = (v i : G) := hcval
      _ = u i := huival.symm
/-- Lemma 2.2 (`lem: e`, tex lines 122-126): translating the first set left by
`g` and the last set right by `h` again yields a factorization. -/
theorem isFactorization_endTranslate (g h : G) {n : ℕ} (A : Fin (n + 2) → Set G)
    (hfac : IsFactorization A) : IsFactorization (endTranslate g h A) :=
  isFactorization_endTranslateL g _ (isFactorization_endTranslateR h A hfac)

theorem endTranslate_apply_zero (g h : G) {n : ℕ} (A : Fin (n + 2) → Set G) :
    endTranslate g h A 0 = (fun x => g * x) '' (A 0) := by
  have hne : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro hcon
    have hv := congrArg Fin.val hcon
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  simp [endTranslate, endTranslateL, endTranslateR, hne]

theorem endTranslate_apply_last (g h : G) {n : ℕ} (A : Fin (n + 2) → Set G) :
    endTranslate g h A (Fin.last (n + 1)) =
      (fun x => x * h) '' (A (Fin.last (n + 1))) := by
  have hne : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := by
    intro hcon
    have hv := congrArg Fin.val hcon
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  simp [endTranslate, endTranslateL, endTranslateR, hne]

theorem card_endTranslate_zero (g h : G) {n : ℕ} (A : Fin (n + 2) → Set G) :
    Nat.card ↥(endTranslate g h A 0) = Nat.card ↥(A 0) := by
  rw [endTranslate_apply_zero]
  exact Nat.card_congr (Equiv.Set.image (Equiv.mulLeft g) (A 0)
    (fun a b hab => by
      have h2 : g * a = g * b := hab
      rwa [mul_right_inj] at h2)).symm

theorem card_endTranslate_last (g h : G) {n : ℕ} (A : Fin (n + 2) → Set G) :
    Nat.card ↥(endTranslate g h A (Fin.last (n + 1))) =
      Nat.card ↥(A (Fin.last (n + 1))) := by
  rw [endTranslate_apply_last]
  exact Nat.card_congr
    (Equiv.Set.image (Equiv.mulRight h) (A (Fin.last (n + 1)))
      (fun a b hab => by
        have h2 : a * h = b * h := hab
        rwa [mul_left_inj] at h2)).symm
