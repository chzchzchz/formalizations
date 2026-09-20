import McCulloch26_1.Basic
import McCulloch26_1.Lem_2_2_EndTranslate

/-!
# Gap lemmas for McCulloch26-1

Gap lemmas are results the paper leans on without proving. Per the project
conventions they are stated here explicitly, cited, and tracked in `status.md`;
nothing depending on an open gap reaches `done`.

The gap was Lemma 2.1(i)-(ii) of the paper (tex lines 112-118), whose printed
proof lives in Bergman20 (`[berg]`, cited at tex line 110). That proof is now
transcribed here, closing the gap. Scope: the conclusion holds for the END
factors only. Bergman20 proves exactly those two parts (its Lemma `L.div2`
parts (i)-(ii)), and remarks that replacing "normal subgroup" by "subgroup"
for middle factors probably fails (tex lines 305-315), while Theorem 2.3 only
ever applies the lemma at the two ends.
-/

open Set Function

variable {G : Type*} [Group G]

/-- The difference set `s⁻¹s = {x⁻¹y | x, y ∈ s}` of tex line 115. -/
def diffSet (s : Set G) : Set G :=
  (fun p : G × G => p.1⁻¹ * p.2) '' (s ×ˢ s)

/-- The right difference set `ss⁻¹ = {xy⁻¹ | x, y ∈ s}`, used by
Lemma 2.1(ii) / Bergman20 `L.div2` (ii) for the last factor
(/home/chz/src/gamskil/docs/arxiv/2003.12866/main.tex lines 227-233). -/
def diffSetR (s : Set G) : Set G :=
  (fun p : G × G => p.1 * p.2⁻¹) '' (s ×ˢ s)

/-! ### Product-splitting infrastructure

Generic `Monoid` lemmas splitting an ordered product at its first or last
position; they play the role of the informal grouping steps in Bergman20's
proofs of `L.div` (lines 121-128) and `L.div2` (lines 242-283).
-/

section ListProd
variable {M : Type*} [Monoid M]

/-- Split off the first factor of an ordered product. -/
theorem list_prod_split_first {n : ℕ} (F : Fin (n + 1) → M) :
    (List.ofFn F).prod = F 0 * (List.ofFn fun j : Fin n => F j.succ).prod := by
  rw [List.ofFn_succ, List.prod_cons]

/-- Split off the last factor of an ordered product. -/
theorem list_prod_split_last {n : ℕ} (F : Fin (n + 1) → M) :
    (List.ofFn F).prod =
      (List.ofFn fun j : Fin n => F j.castSucc).prod * F (Fin.last n) := by
  rw [List.ofFn_succ', List.prod_concat]

/-- Value of `j.succ` minus one recovers `j`. -/
theorem fin_val_sub_succ {n : ℕ} (j : Fin n) :
    ((j.succ : Fin (n + 1)).val - 1 : ℕ) = j.val := by
  simp only [Fin.val_succ]
  omega

/-- The choice function picking `a` at index `0` and `u j` at index `j.succ`. -/
def consFn {n : ℕ} (a : M) (u : Fin n → M) : Fin (n + 1) → M :=
  fun i => if h : i.val = 0 then a else u ⟨i.val - 1, by have := i.isLt; omega⟩

@[simp] theorem consFn_zero {n : ℕ} (a : M) (u : Fin n → M) :
    consFn (a := a) (u := u) 0 = a := by
  have h0 : ((0 : Fin (n + 1)).val : ℕ) = 0 := rfl
  unfold consFn
  rw [dif_pos h0]

@[simp] theorem consFn_succ {n : ℕ} (a : M) (u : Fin n → M) (j : Fin n) :
    consFn (a := a) (u := u) j.succ = u j := by
  unfold consFn
  rw [dif_neg (by have := j.isLt; simp only [Fin.val_succ]; omega)]
  apply congrArg u
  apply Fin.val_injective
  simp [Fin.val_succ]

/-- Ordered product of the family `consFn a u`. -/
theorem list_prod_consFn {n : ℕ} (a : M) (u : Fin n → M) :
    (List.ofFn (consFn a u)).prod = a * (List.ofFn u).prod := by
  rw [List.ofFn_succ, List.prod_cons, consFn_zero]
  have hf : (fun i : Fin n => consFn a u i.succ) = u := funext fun j => consFn_succ a u j
  rw [hf]

/-- The choice function picking `u j` at index `j.castSucc` and `a` at the
last index. -/
def snocFn {n : ℕ} (u : Fin n → M) (a : M) : Fin (n + 1) → M :=
  fun i => if h : i.val = n then a else u ⟨i.val, by have := i.isLt; omega⟩

@[simp] theorem snocFn_castSucc {n : ℕ} (u : Fin n → M) (a : M) (j : Fin n) :
    snocFn (u := u) (a := a) j.castSucc = u j := by
  have hd : ¬((j.castSucc : Fin (n + 1)).val = n) :=
    show ¬(j.val = n) from Nat.ne_of_lt j.isLt
  unfold snocFn
  rw [dif_neg hd]
  apply congrArg u
  exact Fin.ext rfl

@[simp] theorem snocFn_last {n : ℕ} (u : Fin n → M) (a : M) :
    snocFn (u := u) (a := a) (Fin.last n) = a := by
  unfold snocFn
  rw [dif_pos (Fin.val_last n)]

/-- Ordered product of the family `snocFn u a`. -/
theorem list_prod_snocFn {n : ℕ} (u : Fin n → M) (a : M) :
    (List.ofFn (snocFn u a)).prod = (List.ofFn u).prod * a := by
  rw [List.ofFn_succ', List.prod_concat, snocFn_last]
  have hf : (fun i : Fin n => snocFn u a i.castSucc) = u :=
    funext fun j => snocFn_castSucc u a j
  rw [hf]
end ListProd

/-! ### Bergman20 Lemma `L.div` (first- and last-factor forms)

Source: /home/chz/src/gamskil/docs/arxiv/2003.12866/main.tex, Lemma `L.div`
statement lines 113-119, proof lines 121-128. The printed proof: every right
coset of `H = ⟨A⟩` is a disjoint union of sets `A b` (`b ∈ B`), each of size
`card A`, hence `card H` is a multiple of `card A`. We realize the count as a
bijection between `P` and `A 0` times the tails whose product lands in `P`:
the forward map reads (first factor, tail) off the unique representation;
disjointness of the pieces makes it injective, and uniqueness of
representations makes the candidate `(a, w) ↦ a * (tail product w)` invert it.
The mirrored last-factor form replaces right cosets by left cosets ("The
statement about B is seen in the same way", line 127).
-/

/-- First-factor divisibility: in a factorization `A 0 ⋯ A n`, `Nat.card (A 0)`
divides the cardinality of any subgroup `P` containing `A 0`. Transcription of
/home/chz/src/gamskil/docs/arxiv/2003.12866/main.tex lines 113-128 (Lemma
`L.div`, combined with the grouping observation at lines 105-111). -/
theorem nat_card_dvd_of_first_subset {n : ℕ} {A : Fin (n + 1) → Set G}
    (hfac : IsFactorization A) (P : Subgroup G) (hsubP : ∀ x ∈ A 0, x ∈ P) :
    Nat.card ↥(A 0) ∣ Nat.card ↥P := by
  classical
  set T : Type _ := {w : ∀ j : Fin n, A j.succ //
    (List.ofFn fun j : Fin n => (w j : G)).prod ∈ P}
  -- chosen representation of every element of `P` in the factorization
  set R : ↥P → ∀ i : Fin (n + 1), A i := fun x => Classical.choose (hfac (x : G))
  have hRp : ∀ x : ↥P, (List.ofFn fun i => ((R x i : G))).prod = (x : G) :=
    fun x => (Classical.choose_spec (hfac (x : G))).1
  have htail_mem : ∀ x : ↥P,
      (List.ofFn fun j : Fin n => (R x j.succ : G)).prod ∈ P := by
    intro x
    have hx : (x : G) = ↑(R x 0) *
        (List.ofFn fun j : Fin n => (R x j.succ : G)).prod :=
      (hRp x).symm.trans (list_prod_split_first fun i => (R x i : G))
    have h₀ : (↑(R x 0) : G) ∈ P := hsubP _ (R x 0).2
    have hval : (List.ofFn fun j : Fin n => (R x j.succ : G)).prod
        = (↑(R x 0) : G)⁻¹ * (x : G) := by rw [hx]; group
    rw [hval]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h₀) x.2
  suffices key : Nat.card ↥P = Nat.card (↥(A 0) × T) by
    rw [Nat.card_prod] at key
    exact ⟨Nat.card T, key⟩
  refine Nat.card_eq_of_bijective
    (f := fun x : ↥P =>
      ((⟨(R x 0 : G), (R x 0).2⟩,
        ⟨fun j => ⟨R x j.succ, (R x j.succ).2⟩, htail_mem x⟩) : ↥(A 0) × T))
      ?_
  constructor
  · -- injective: read both representations off the pair and compare
    intro x y hxy
    have h0 : (R x 0 : G) = (R y 0 : G) :=
      congrArg Subtype.val (congrArg Prod.fst hxy)
    have htw : (⟨fun j => ⟨R x j.succ, (R x j.succ).2⟩, htail_mem x⟩ : T)
        = ⟨fun j => ⟨R y j.succ, (R y j.succ).2⟩, htail_mem y⟩ :=
      congrArg Prod.snd hxy
    have htail : (fun j : Fin n => (R x j.succ : G)) =
        (fun j : Fin n => (R y j.succ : G)) := by
      have hh := congrArg Subtype.val htw
      exact funext fun j => congrArg Subtype.val (congrFun hh j)
    apply Subtype.ext
    have hx : (x : G) = (↑(R x 0) : G) *
        (List.ofFn fun j : Fin n => (R x j.succ : G)).prod :=
      (hRp x).symm.trans (list_prod_split_first fun i => (R x i : G))
    have hy : (y : G) = (↑(R y 0) : G) *
        (List.ofFn fun j : Fin n => (R y j.succ : G)).prod :=
      (hRp y).symm.trans (list_prod_split_first fun i => (R y i : G))
    rw [hx, hy, h0, htail]
  · -- surjective: rebuild from the unique representation of `a * tail`
    rintro ⟨a, w⟩
    set q : ↥P := ⟨(a : G) * (List.ofFn fun j : Fin n => (w.1 j : G)).prod,
      Subgroup.mul_mem _ (hsubP _ a.2) w.2⟩ with hq
    refine ⟨q, ?_⟩
    obtain ⟨g, hgprod, hgu⟩ := hfac (q : G)
    have m₁ : ∀ i : Fin (n + 1),
        consFn (a : G) (fun j : Fin n => (w.1 j : G)) i ∈ A i := by
      intro i
      by_cases hi : i.val = 0
      · have hi0 : i = 0 := Fin.ext hi
        rw [hi0]
        simpa using a.2
      · obtain ⟨j, rfl⟩ : ∃ j : Fin n, i = j.succ :=
          ⟨⟨i.val - 1, by have := i.isLt; omega⟩,
            Fin.ext (by simp only [Fin.val_succ]; omega)⟩
        rw [consFn_succ]
        exact (w.1 j).2
    have hcval : (List.ofFn fun i =>
            ((⟨consFn (a : G) (fun j : Fin n => (w.1 j : G)) i, m₁ i⟩ : A i) : G)).prod
        = (q : G) := by
      rw [list_prod_consFn]
    have hgc : g = Classical.choose (hfac (q : G)) :=
      (Classical.choose_spec (hfac (q : G))).2 g hgprod
    have hRq : R q
        = fun i => ⟨consFn (a : G) (fun j : Fin n => (w.1 j : G)) i, m₁ i⟩ :=
      hgc.symm.trans (hgu _ hcval).symm
    have hv : (↑(R q 0) : G) = (a : G) := by
      have hp := congrFun hRq 0
      simp only [consFn_zero] at hp
      exact congrArg Subtype.val hp
    refine Prod.ext (Subtype.ext hv) ?_
    apply Subtype.ext
    apply funext
    intro j
    have hp := congrFun hRq j.succ
    simp only [consFn_succ] at hp
    simpa using hp

/-- Last-factor divisibility: in a factorization `A 0 ⋯ A n`, `Nat.card` of the
last factor divides the cardinality of any subgroup `P` containing it. Mirror
of `/home/chz/src/gamskil/docs/arxiv/2003.12866/main.tex` lines 113-128 with
right cosets replaced by left cosets ("The statement about B is seen in the
same way", line 127). -/
theorem nat_card_dvd_of_last_subset {n : ℕ} {A : Fin (n + 1) → Set G}
    (hfac : IsFactorization A) (P : Subgroup G)
    (hsubP : ∀ x ∈ A (Fin.last n), x ∈ P) :
    Nat.card ↥(A (Fin.last n)) ∣ Nat.card ↥P := by
  classical
  set T : Type _ := {w : ∀ j : Fin n, A j.castSucc //
    (List.ofFn fun j : Fin n => (w j : G)).prod ∈ P}
  set R : ↥P → ∀ i : Fin (n + 1), A i := fun x => Classical.choose (hfac (x : G))
  have hRp : ∀ x : ↥P, (List.ofFn fun i => ((R x i : G))).prod = (x : G) :=
    fun x => (Classical.choose_spec (hfac (x : G))).1
  have hhead_mem : ∀ x : ↥P,
      (List.ofFn fun j : Fin n => (R x j.castSucc : G)).prod ∈ P := by
    intro x
    have hx : (x : G) = (List.ofFn fun j : Fin n => (R x j.castSucc : G)).prod *
        ↑(R x (Fin.last n)) :=
      (hRp x).symm.trans (list_prod_split_last fun i => (R x i : G))
    have hl : (↑(R x (Fin.last n)) : G) ∈ P := hsubP _ (R x (Fin.last n)).2
    have hval : (List.ofFn fun j : Fin n => (R x j.castSucc : G)).prod
        = (x : G) * (↑(R x (Fin.last n)) : G)⁻¹ := by rw [hx]; group
    rw [hval]
    exact Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ hl)
  suffices key : Nat.card ↥P = Nat.card (↥(A (Fin.last n)) × T) by
    rw [Nat.card_prod] at key
    exact ⟨Nat.card T, key⟩
  refine Nat.card_eq_of_bijective
    (f := fun x : ↥P =>
      ((⟨(R x (Fin.last n) : G), (R x (Fin.last n)).2⟩,
        ⟨fun j => ⟨R x j.castSucc, (R x j.castSucc).2⟩, hhead_mem x⟩) :
          ↥(A (Fin.last n)) × T))
      ?_
  constructor
  · intro x y hxy
    have hl : (R x (Fin.last n) : G) = (R y (Fin.last n) : G) :=
      congrArg Subtype.val (congrArg Prod.fst hxy)
    have htw : (⟨fun j => ⟨R x j.castSucc, (R x j.castSucc).2⟩, hhead_mem x⟩ : T)
        = ⟨fun j => ⟨R y j.castSucc, (R y j.castSucc).2⟩, hhead_mem y⟩ :=
      congrArg Prod.snd hxy
    have hhead : (fun j : Fin n => (R x j.castSucc : G)) =
        (fun j : Fin n => (R y j.castSucc : G)) := by
      have hh := congrArg Subtype.val htw
      exact funext fun j => congrArg Subtype.val (congrFun hh j)
    apply Subtype.ext
    have hx : (x : G) = (List.ofFn fun j : Fin n => (R x j.castSucc : G)).prod *
        ↑(R x (Fin.last n)) :=
      (hRp x).symm.trans (list_prod_split_last fun i => (R x i : G))
    have hy : (y : G) = (List.ofFn fun j : Fin n => (R y j.castSucc : G)).prod *
        ↑(R y (Fin.last n)) :=
      (hRp y).symm.trans (list_prod_split_last fun i => (R y i : G))
    rw [hx, hy, hhead, hl]
  · rintro ⟨b, w⟩
    set q : ↥P := ⟨(List.ofFn fun j : Fin n => (w.1 j : G)).prod * (b : G),
      Subgroup.mul_mem _ w.2 (hsubP _ b.2)⟩ with hq
    refine ⟨q, ?_⟩
    obtain ⟨g, hgprod, hgu⟩ := hfac (q : G)
    have m₂ : ∀ i : Fin (n + 1),
        snocFn (fun j : Fin n => (w.1 j : G)) (b : G) i ∈ A i := by
      intro i
      by_cases hi : (i : ℕ) = n
      · have hil : i = Fin.last n := Fin.ext hi
        rw [hil]
        simpa using b.2
      · obtain ⟨j, rfl⟩ : ∃ j : Fin n, i = (j.castSucc : Fin (n + 1)) :=
          ⟨⟨i.val, by have := i.isLt; omega⟩, Fin.ext rfl⟩
        rw [snocFn_castSucc]
        exact (w.1 j).2
    have hcval : (List.ofFn fun i =>
            ((⟨snocFn (fun j : Fin n => (w.1 j : G)) (b : G) i, m₂ i⟩ : A i) : G)).prod
        = (q : G) := by
      rw [list_prod_snocFn]
    have hgc : g = Classical.choose (hfac (q : G)) :=
      (Classical.choose_spec (hfac (q : G))).2 g hgprod
    have hRq : R q
        = fun i => ⟨snocFn (fun j : Fin n => (w.1 j : G)) (b : G) i, m₂ i⟩ :=
      hgc.symm.trans (hgu _ hcval).symm
    have hv : (↑(R q (Fin.last n)) : G) = (b : G) := by
      have hp := congrFun hRq (Fin.last n)
      simp only [snocFn_last] at hp
      exact congrArg Subtype.val hp
    refine Prod.ext (Subtype.ext hv) ?_
    apply Subtype.ext
    apply funext
    intro j
    have hp := congrFun hRq j.castSucc
    simp only [snocFn_castSucc] at hp
    simpa using hp

/-- A factorization has nonempty factors whenever the index is valid. -/
theorem isFactorization_nonempty {n : ℕ} {A : Fin n → Set G}
    (hfac : IsFactorization A) (i : Fin n) : (A i).Nonempty := by
  obtain ⟨f, -⟩ := hfac 1
  exact ⟨f i, (f i).2⟩

theorem card_dvd_card_closure_diffSet_first {n : ℕ} {A : Fin (n + 1) → Set G}
    (hfac : IsFactorization A) :
    Nat.card ↥(A 0) ∣ Nat.card ↥(Subgroup.closure (diffSet (A 0))) := by
  classical
  obtain ⟨g₀, hg₀mem⟩ := isFactorization_nonempty hfac (0 : Fin (n + 1))
  -- translate the first factor left by g₀⁻¹ (Bergman20 `L.e_in`, lines 132-143;
  -- our realization: isFactorization_endTranslateL)
  have hBfac : IsFactorization (endTranslateL (g₀⁻¹ : G) A) :=
    isFactorization_endTranslateL _ A hfac
  have hB0 : endTranslateL (g₀⁻¹ : G) A 0 = (fun x => g₀⁻¹ * x) '' A 0 := by
    simp [endTranslateL]
  -- divisibility for the translated family (Bergman20 `L.div`, lines 113-128)
  have hdvd := nat_card_dvd_of_first_subset hBfac
    (Subgroup.closure ((fun x => g₀⁻¹ * x) '' A 0))
    (fun _ hx => Subgroup.subset_closure hx)
  rw [hB0] at hdvd
  -- left multiplication is a permutation, so the translate has the same size
  have himg : Nat.card ↥((fun x => g₀⁻¹ * x) '' A 0) = Nat.card ↥(A 0) :=
    Nat.card_image_equiv (Equiv.mulLeft (g₀⁻¹ : G))
  rw [himg] at hdvd
  -- identify the generated subgroups (Bergman20 lines 248-255)
  have hcl : Subgroup.closure ((fun x => g₀⁻¹ * x) '' A 0)
      = Subgroup.closure (diffSet (A 0)) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y ⟨x, hx, rfl⟩
      exact Subgroup.subset_closure ⟨(g₀, x), ⟨hg₀mem, hx⟩, by group⟩
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [diffSet, Set.mem_image] at hy
      obtain ⟨p, hp, hpval⟩ := hy
      have hv : p.1⁻¹ * p.2 = y := hpval
      rw [← hv]
      have m₁ : g₀⁻¹ * p.1 ∈ Subgroup.closure ((fun x => g₀⁻¹ * x) '' A 0) :=
        Subgroup.subset_closure ⟨p.1, hp.1, rfl⟩
      have m₂ : g₀⁻¹ * p.2 ∈ Subgroup.closure ((fun x => g₀⁻¹ * x) '' A 0) :=
        Subgroup.subset_closure ⟨p.2, hp.2, rfl⟩
      have hval : p.1⁻¹ * p.2 = (g₀⁻¹ * p.1)⁻¹ * (g₀⁻¹ * p.2) := by group
      rw [hval]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ m₁) m₂
  rwa [hcl] at hdvd

/-- **Gap lemma, closed** — Lemma 2.1(ii) of McCulloch26-1 (tex lines 112-118):
in a factorization, the cardinality of the last factor divides the order of
the subgroup generated by its difference set. Mirror of part (i) ("holds by
the same reasoning"): /home/chz/src/gamskil/docs/arxiv/2003.12866/main.tex
line 266, using `A_k A_k⁻¹` in place of `A_1⁻¹ A_1` (lines 227-233). -/
theorem card_dvd_card_closure_diffSet_last {n : ℕ} {A : Fin (n + 1) → Set G}
    (hfac : IsFactorization A) :
    Nat.card ↥(A (Fin.last n)) ∣ Nat.card ↥(Subgroup.closure
      (diffSetR (A (Fin.last n)))) := by
  classical
  obtain ⟨gₗ, hgₗmem⟩ := isFactorization_nonempty hfac (Fin.last n)
  -- translate the last factor right by gₗ⁻¹ (Bergman20 `L.e_in`, lines 132-143)
  have hBfac : IsFactorization (endTranslateR (gₗ⁻¹ : G) A) :=
    isFactorization_endTranslateR _ A hfac
  have hBl : endTranslateR (gₗ⁻¹ : G) A (Fin.last n)
      = (fun x => x * gₗ⁻¹) '' A (Fin.last n) := by
    simp [endTranslateR]
  have hsub : ∀ x ∈ endTranslateR (gₗ⁻¹ : G) A (Fin.last n),
      x ∈ Subgroup.closure ((fun x => x * gₗ⁻¹) '' A (Fin.last n)) := by
    intro x hx
    rw [hBl] at hx
    exact Subgroup.subset_closure hx
  have hdvd := nat_card_dvd_of_last_subset hBfac
    (Subgroup.closure ((fun x => x * gₗ⁻¹) '' A (Fin.last n))) hsub
  rw [hBl] at hdvd
  have himg : Nat.card ↥((fun x => x * gₗ⁻¹) '' A (Fin.last n))
      = Nat.card ↥(A (Fin.last n)) :=
    Nat.card_image_equiv (Equiv.mulRight (gₗ⁻¹ : G))
  rw [himg] at hdvd
  have hcl : Subgroup.closure ((fun x => x * gₗ⁻¹) '' A (Fin.last n))
      = Subgroup.closure (diffSetR (A (Fin.last n))) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y ⟨x, hx, rfl⟩
      exact Subgroup.subset_closure ⟨(x, gₗ), ⟨hx, hgₗmem⟩, rfl⟩
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [diffSetR, Set.mem_image] at hy
      obtain ⟨p, hp, hpval⟩ := hy
      have hv : p.1 * p.2⁻¹ = y := hpval
      rw [← hv]
      have m₁ : p.1 * gₗ⁻¹ ∈ Subgroup.closure ((fun x => x * gₗ⁻¹) '' A (Fin.last n)) :=
        Subgroup.subset_closure ⟨p.1, hp.1, rfl⟩
      have m₂ : p.2 * gₗ⁻¹ ∈ Subgroup.closure ((fun x => x * gₗ⁻¹) '' A (Fin.last n)) :=
        Subgroup.subset_closure ⟨p.2, hp.2, rfl⟩
      have hval : p.1 * p.2⁻¹ = (p.1 * gₗ⁻¹) * (p.2 * gₗ⁻¹)⁻¹ := by group
      rw [hval]
      exact Subgroup.mul_mem _ m₁ (Subgroup.inv_mem _ m₂)
  rwa [hcl] at hdvd
