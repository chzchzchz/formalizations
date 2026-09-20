import McCulloch26_1.Basic

/-!
# Theorem 3.1 (`thm2`) of McCulloch26-1

A sufficient condition for k-fold factorizations: a subgroup chain
`{e} = G_0 ≤ G_1 ≤ ⋯ ≤ G_n = G` whose edge indices can be partitioned into
blocks `s_t` satisfying the paper's one-sidedness condition realizes every
compatible ordered-size factorization.  Proved by induction on `j`, extending
a factorization of `G_j` to `G_{j+1}` through a transversal of the left
cosets of `G_j` in `G_{j+1}`, mirroring the printed argument.

Encoding deltas vs. the paper (recorded in status.md): the chain is stated
with non-strict consecutive steps `G_j ≤ G_{j+1}` (strictness unused by the
proof), indices are 0-based (`edge i` connects `G_i` and `G_{i+1}`), the
total-order hypothesis `Σ a_i = |G|` and positivity of the `a_i` are dropped
(both follow from the block-product hypotheses and are never read by the
proof), and blocks are `Finset ℕ` with elements `< n`.

Source: /home/chz/src/gamskil/docs/arxiv/2607.20569v3/Some_Answers_Factorization.tex
lines 148-166 (statement), 168-190 (printed proof).
-/

open Set Function Finset
open scoped Pointwise

variable {G : Type*} [Group G]

/-- Ordered product of a choice function, the representation used by
`IsFactorization` (tex lines 98-103). -/
def reprProd {k : ℕ} {A : Fin k → Set G} (f : ∀ i, A i) : G :=
  (List.ofFn fun i => (f i : G)).prod

/-- Relativized unique-factorization invariant maintained by the chain
induction of Theorem 3.1: representations are globally unique (for every
group element, vacuously off the product set), and the product set is `P`.
At the top of the chain this upgrades to `IsFactorization` because `P = ⊤`.
Source: invariant (d.A1jA2j) of tex lines 154-157. -/
def UFac (P : Subgroup G) {k : ℕ} (A : Fin k → Set G) : Prop :=
  (∀ x : G, ∀ f f' : (∀ i, A i), reprProd f = x → reprProd f' = x → f = f') ∧
    setSeqProd A = (P : Set G)

/-! ### Index reversal (mirror of block order) -/

/-- Index reversal `i ↦ k - 1 - i` on `Fin k`, used to mirror the order of
the factor blocks. -/
def finRev {k : ℕ} (i : Fin k) : Fin k := ⟨k - 1 - i.val, by omega⟩

theorem finRev_finRev {k : ℕ} (i : Fin k) : finRev (finRev i) = i := by
  apply Fin.ext
  simp only [finRev]
  omega

theorem finRev_lt_finRev {k : ℕ} {a b : Fin k} (h : a < b) : finRev b < finRev a := by
  have h1 : a.val < b.val := Fin.lt_def.mp h
  rw [Fin.lt_def]
  simp only [finRev]
  omega

/-! ### List-product lemmas -/

/-- Mini helper: an ordered product of ones is one. -/
theorem prod_ofFn_one {M : Type*} [Monoid M] : ∀ {k : ℕ},
    (List.ofFn fun (_ : Fin k) => (1 : M)).prod = 1
  | 0 => rfl
  | k + 1 => by rw [List.ofFn_succ, List.prod_cons, prod_ofFn_one, one_mul]

/-- Splitting an ordered product around position `t`: prefix before `t`, the
coordinate at `t`, and the suffix after it.  This is the only positional
decomposition valid in a noncommutative monoid; it realizes the factorizations
`S · A_{t,j} ⋯ A_{k,j}` of tex line 160 at the level of representations. -/
theorem prod_split3 {M : Type*} [Monoid M] : ∀ {k : ℕ} (v : Fin k → M) (t : Fin k),
    (List.ofFn v).prod =
      (List.ofFn fun a => if a < t then v a else (1 : M)).prod *
        (v t * (List.ofFn fun a => if t < a then v a else (1 : M)).prod) := by
  intro k
  induction k with
  | zero => intro v t; exact t.elim0
  | succ n ih =>
      intro v t
      refine Fin.cases ?_ (fun m => ?_) t
      · rw [List.ofFn_succ, List.prod_cons]
        have hp0 : (fun a : Fin (n + 1) => if a < (0 : Fin (n + 1)) then v a else (1 : M))
            = (fun _ : Fin (n + 1) => (1 : M)) := by
          funext a
          exact if_neg (Fin.not_lt_zero a)
        rw [hp0, prod_ofFn_one, one_mul]
        rw [List.ofFn_succ, List.prod_cons]
        have hz2 : (if (0 : Fin (n + 1)) < 0 then v 0 else (1 : M)) =
            (1 : M) := if_neg (Fin.not_lt_zero _)
        rw [hz2]
        have hs : ∀ i : Fin n,
            (if (0 : Fin (n + 1)) < Fin.succ i then v i.succ else (1 : M)) = v i.succ :=
          fun i => if_pos (Fin.lt_def.2 (Nat.zero_lt_succ _))
        simp only [hs, one_mul]
      · rw [List.ofFn_succ, List.prod_cons]
        rw [List.ofFn_succ, List.prod_cons]
        rw [List.ofFn_succ, List.prod_cons]
        have hp : (0 : Fin (n + 1)) < Fin.succ m := Fin.lt_def.2 (Nat.zero_lt_succ _)
        rw [if_pos hp]
        have hneg : (if Fin.succ m < (0 : Fin (n + 1)) then v 0 else (1 : M)) = (1 : M) :=
          if_neg (Fin.not_lt_zero _)
        rw [hneg]
        have hinner : ∀ i : Fin n,
            (if Fin.succ i < Fin.succ m then v i.succ else (1 : M))
              = if i < m then v i.succ else (1 : M) := by
          intro i; simp only [Fin.succ_lt_succ_iff]
        have hinner2 : ∀ i : Fin n,
            (if Fin.succ m < Fin.succ i then v i.succ else (1 : M))
              = if m < i then v i.succ else (1 : M) := by
          intro i; simp only [Fin.succ_lt_succ_iff]
        simp only [hinner, hinner2]
        have him2 : (List.ofFn fun i : Fin n => v (Fin.succ i)).prod
            = (List.ofFn fun a : Fin n =>
                if a < m then (fun i : Fin n => v (Fin.succ i)) a else (1 : M)).prod *
                ((fun i : Fin n => v (Fin.succ i)) m *
                  (List.ofFn fun a : Fin n =>
                    if m < a then (fun i : Fin n => v (Fin.succ i)) a else (1 : M)).prod) :=
          ih (fun i => v (Fin.succ i)) m
        rw [him2, mul_assoc, one_mul]

/-- Inserting factors `γ a` before position `t` multiplies the ordered
product on the left by their product, provided the displaced coordinates
are trivial there; stripping them back out divides it.  This realizes the
normalization "we may assume S = {e}" of tex line 161 at the level of
representations. -/
theorem prod_update_lt {M : Type*} [Monoid M] : ∀ {k : ℕ} (γ w : Fin k → M) (t : Fin k),
    (List.ofFn fun a => if a < t then γ a else w a).prod =
      (List.ofFn fun a => if a < t then γ a else (1 : M)).prod *
        (List.ofFn fun a => if a < t then (1 : M) else w a).prod := by
  intro k
  induction k with
  | zero => intro γ w t; exact t.elim0
  | succ n ih =>
      intro γ w t
      refine Fin.cases ?_ (fun m => ?_) t
      · have hn : ∀ a : Fin (n + 1), ¬ a < (0 : Fin (n + 1)) := fun a => Fin.not_lt_zero a
        simp only [hn, if_false]
        rw [prod_ofFn_one, one_mul]
      · rw [List.ofFn_succ, List.prod_cons]
        rw [List.ofFn_succ, List.prod_cons]
        rw [List.ofFn_succ, List.prod_cons]
        have hp : (0 : Fin (n + 1)) < Fin.succ m := Fin.lt_def.2 (Nat.zero_lt_succ _)
        rw [if_pos hp, if_pos hp, if_pos hp]
        have hinner : ∀ i : Fin n,
            (if Fin.succ i < Fin.succ m then γ i.succ else w i.succ)
              = if i < m then γ i.succ else w i.succ := by
          intro i; simp only [Fin.succ_lt_succ_iff]
        have hinner' : ∀ i : Fin n,
            (if Fin.succ i < Fin.succ m then γ i.succ else (1 : M))
              = if i < m then γ i.succ else (1 : M) := by
          intro i; simp only [Fin.succ_lt_succ_iff]
        have hinner'' : ∀ i : Fin n,
            (if Fin.succ i < Fin.succ m then (1 : M) else w i.succ)
              = if i < m then (1 : M) else w i.succ := by
          intro i; simp only [Fin.succ_lt_succ_iff]
        simp only [hinner, hinner', hinner'']
        rw [ih (fun i => γ i.succ) (fun i => w i.succ) m, one_mul, ← mul_assoc]

/-- Reversal-with-inversion of an ordered product computes the inverse
product; used to transfer factorization facts through the mirror involution
that discharges the "all later blocks empty" branch of the one-sidedness
condition (tex lines 159-160). -/
theorem prod_mirror_inv {M : Type*} [Group M] : ∀ {k : ℕ} (F : Fin k → M),
    (List.ofFn fun i => (F (finRev i))⁻¹).prod = ((List.ofFn F).prod)⁻¹ := by
  intro k
  induction k with
  | zero => intro F; simp
  | succ n ih =>
      intro F
      have hlast : finRev (Fin.last n) = (0 : Fin (n + 1)) := Fin.ext (by
        show Fin.val (finRev (Fin.last n)) = 0
        have h2 : Fin.val (finRev (Fin.last n)) = n + 1 - 1 - n := rfl
        rw [h2]
        omega)
      have hfe : ∀ i : Fin n, finRev (Fin.castSucc i) = Fin.succ (finRev i) := fun i =>
        Fin.ext (by
          show Fin.val (finRev (Fin.castSucc i)) = Fin.val (Fin.succ (finRev i))
          have hc : Fin.val (Fin.castSucc i) = Fin.val i := rfl
          have hr : Fin.val (finRev i) = n - 1 - Fin.val i := rfl
          have hs : Fin.val (Fin.succ (finRev i)) = Fin.val (finRev i) + 1 := rfl
          have h1 : Fin.val (finRev (Fin.castSucc i))
              = n + 1 - 1 - Fin.val (Fin.castSucc i) := rfl
          rw [h1, hc, hs, hr]
          omega)
      have key := ih (fun i : Fin n => F (Fin.succ i))
      calc (List.ofFn fun i => (F (finRev i))⁻¹).prod
          = (List.ofFn fun i : Fin n => (F (finRev (Fin.castSucc i)))⁻¹).prod *
              (F (finRev (Fin.last n)))⁻¹ := by
            rw [List.ofFn_succ' (f := fun i => (F (finRev i))⁻¹), List.prod_concat]
        _ = (List.ofFn fun i : Fin n => (F (Fin.succ (finRev i)))⁻¹).prod * (F 0)⁻¹ := by
            have e1 : (F (finRev (Fin.last n)))⁻¹ = (F 0)⁻¹ :=
              congrArg (fun x : M => x⁻¹) (congrArg F hlast)
            have hfn : (fun i : Fin n => (F (finRev (Fin.castSucc i)))⁻¹)
                = (fun i : Fin n => (F (Fin.succ (finRev i)))⁻¹) :=
              funext fun i => congrArg (fun x : M => x⁻¹) (congrArg F (hfe i))
            rw [hfn, e1]
        _ = ((List.ofFn fun i : Fin n => (F (Fin.succ i))).prod)⁻¹ * (F 0)⁻¹ := by rw [key]
        _ = ((List.ofFn F).prod)⁻¹ := by rw [List.ofFn_succ, List.prod_cons, mul_inv_rev]


/-! ### Left-coset transversals -/

/-- A section of the projection onto left cosets of `H.subgroupOf K` inside
`K`, choosing one representative per coset (tex line 163: "a full set of
representatives of the left cosets"). -/
noncomputable def cosetSec (K H : Subgroup G) (q : ↥K ⧸ H.subgroupOf K) : ↥K :=
  Classical.choose (Quotient.exists_rep q)

theorem cosetSec_mk (K H : Subgroup G) (q : ↥K ⧸ H.subgroupOf K) :
    (Quotient.mk'' (cosetSec K H q) : ↥K ⧸ H.subgroupOf K) = q :=
  Classical.choose_spec (Quotient.exists_rep q)

/-- The chosen representatives, as a subset of `G`. -/
noncomputable def leftReps (K H : Subgroup G) : Set G :=
  Set.range fun q : ↥K ⧸ H.subgroupOf K => ((cosetSec K H q : ↥K) : G)

theorem mem_leftReps_iff {K H : Subgroup G} {c : G} :
    c ∈ leftReps K H ↔ ∃ q : ↥K ⧸ H.subgroupOf K, ((cosetSec K H q : ↥K) : G) = c :=
  Iff.rfl

/-- Distinct left cosets receive distinct representatives. -/
theorem leftReps_sep {K H : Subgroup G} {c c' : G} (hc : c ∈ leftReps K H)
    (hc' : c' ∈ leftReps K H) (hcc : c⁻¹ * c' ∈ H) : c = c' := by
  obtain ⟨q, rfl⟩ := hc
  obtain ⟨q', rfl⟩ := hc'
  have key : (Quotient.mk'' (cosetSec K H q) : ↥K ⧸ H.subgroupOf K)
      = Quotient.mk'' (cosetSec K H q') := by
    rw [Quotient.eq'', QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    exact hcc
  have hq : q = q' := by rw [← cosetSec_mk K H q, key, cosetSec_mk K H q']
  rw [hq]

/-- The representatives meet every coset: `K = leftReps K H · H`. -/
theorem leftReps_cover {K H : Subgroup G} (hHK : H ≤ K) :
    (K : Set G) ⊆ leftReps K H * (H : Set G) := by
  intro x hx
  set q : ↥K ⧸ H.subgroupOf K := Quotient.mk'' (⟨x, hx⟩ : ↥K) with hqx
  have hcrep : ((cosetSec K H q : ↥K) : G) ∈ leftReps K H :=
    mem_leftReps_iff.mpr ⟨q, rfl⟩
  have hrel : (Quotient.mk'' (cosetSec K H q) : ↥K ⧸ H.subgroupOf K)
      = Quotient.mk'' (⟨x, hx⟩ : ↥K) := cosetSec_mk K H q
  have hinH : ((cosetSec K H q : ↥K) : G)⁻¹ * x ∈ H := by
    have hr := Quotient.eq''.mp hrel
    rw [QuotientGroup.leftRel_apply] at hr
    exact Subgroup.mem_subgroupOf.mp hr
  have hy : ((cosetSec K H q : ↥K) : G)⁻¹ * x ∈ (H : Set G) := hinH
  have heq : ((cosetSec K H q : ↥K) : G) * (((cosetSec K H q : ↥K) : G)⁻¹ * x) = x := by group
  rw [← heq]
  exact Set.mul_mem_mul hcrep hy

theorem natCard_leftReps (K H : Subgroup G) :
    Nat.card (leftReps K H) = H.relIndex K := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  symm
  have hinj : Function.Injective
      (fun q : ↥K ⧸ H.subgroupOf K =>
        (⟨((cosetSec K H q : ↥K) : G), mem_leftReps_iff.mpr ⟨q, rfl⟩⟩ :
          ↥(leftReps K H))) := by
    intro q q' hqq
    have hcoe : ((cosetSec K H q : ↥K) : G) = ((cosetSec K H q' : ↥K) : G) := by
      simpa using congrArg Subtype.val hqq
    rw [← cosetSec_mk K H q, ← cosetSec_mk K H q']
    exact congrArg Quotient.mk'' (Subtype.ext hcoe)
  have hsurj : ∀ y : ↥(leftReps K H), ∃ q : ↥K ⧸ H.subgroupOf K,
      (⟨((cosetSec K H q : ↥K) : G), mem_leftReps_iff.mpr ⟨q, rfl⟩⟩ :
          ↥(leftReps K H)) = y := by
    rintro ⟨y, hy⟩
    obtain ⟨q, rfl⟩ := mem_leftReps_iff.mp hy
    exact ⟨q, rfl⟩
  exact Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩

/-! ### Normalizing leading singleton factors (tex lines 159-161) -/

/-- Replace every factor before block `t` by `{1}`: the "we may assume
`S = {e}`" normalization of tex line 161. -/
def normFamilyL {k : ℕ} (t : Fin k) (A : Fin k → Set G) : Fin k → Set G :=
  fun i => if i < t then ({1} : Set G) else A i

/-- Product of the singleton elements sitting before block `t`. -/
def normShift {k : ℕ} (t : Fin k) (γ : Fin k → G) : G :=
  (List.ofFn fun a => if a < t then γ a else (1 : G)).prod

theorem mem_stripNorm {k : ℕ} {A : Fin k → Set G} {t : Fin k}
    {f : ∀ i, A i} {i : Fin k} :
    (if i < t then (1 : G) else (f i : G)) ∈ normFamilyL t A i := by
  by_cases h : i < t
  · simpa [normFamilyL, h] using rfl
  · simpa [normFamilyL, h] using (f i).2

/-- Strip the coordinates before block `t` of an `A`-representation,
viewing it as a normalized-family representation. -/
def stripNorm {k : ℕ} {A : Fin k → Set G} {t : Fin k} (f : ∀ i, A i) :
    ∀ i, normFamilyL t A i := fun i =>
  ⟨if i < t then (1 : G) else (f i : G), mem_stripNorm⟩

theorem mem_insertNorm {k : ℕ} {A : Fin k → Set G} {t : Fin k} {γ : Fin k → G}
    (hγs : ∀ a : Fin k, a < t → A a = {γ a}) {w : ∀ i, normFamilyL t A i}
    {i : Fin k} : (if i < t then γ i else (w i : G)) ∈ A i := by
  by_cases h : i < t
  · rw [if_pos h, hγs i h]
    exact rfl
  · simpa [normFamilyL, h] using (w i).2

/-- Insert the singleton elements back in front of block `t`, turning a
normalized-family representation into an `A`-representation. -/
def insertNorm {k : ℕ} {A : Fin k → Set G} {t : Fin k} (γ : Fin k → G)
    (hγs : ∀ a : Fin k, a < t → A a = {γ a}) (w : ∀ i, normFamilyL t A i) :
    ∀ i, A i := fun i =>
  ⟨if i < t then γ i else (w i : G), mem_insertNorm hγs⟩

theorem normShift_mem {P : Subgroup G} {k : ℕ} {t : Fin k} {γ : Fin k → G}
    (hγ : ∀ a, a < t → γ a ∈ P) : normShift t γ ∈ P := by
  apply Submonoid.list_prod_mem
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨a, rfl⟩ := hx
  by_cases h : a < t
  · rw [if_pos h]; exact hγ a h
  · rw [if_neg h]; exact Subgroup.one_mem P

theorem mem_normFamilyL_intro {k : ℕ} {A : Fin k → Set G} {t : Fin k}
    {w : ∀ i, normFamilyL t A i} {a : Fin k} :
    (if a < t then (1 : G) else (w a : G)) ∈ normFamilyL t A a := by
  by_cases h : a < t
  · simpa [normFamilyL, h] using rfl
  · simpa [normFamilyL, h] using (w a).2

theorem mem_of_eq_set {α : Type*} {S T : Set α} (hST : S = T) {x : α}
    (hx : x ∈ S) : x ∈ T := by
  subst hST
  exact hx

theorem prod_insert_normShift {k : ℕ} {A : Fin k → Set G} {t : Fin k}
    {γ : Fin k → G} (hγs : ∀ a : Fin k, a < t → A a = {γ a})
    (w : ∀ i, normFamilyL t A i) :
    reprProd (insertNorm γ hγs w) = normShift t γ * reprProd w := by
  have hw1 : ∀ a : Fin k, a < t → (w a : G) = 1 := by
    intro a ha
    have := (w a).2
    simpa [normFamilyL, ha] using this
  have h := prod_update_lt γ (fun a => (w a : G)) t
  refine h.trans ?_
  have hv : (fun a => (if a < t then (1 : G) else (w a : G))) =
      (fun a => (w a : G)) := by
    funext a
    by_cases ha : a < t
    · rw [if_pos ha]
      exact (hw1 a ha).symm
    · rw [if_neg ha]
  exact congrArg (normShift t γ * ·)
    (congrArg (List.prod ∘ List.ofFn) hv)

theorem ufac_normL {P : Subgroup G} {k : ℕ} {A : Fin k → Set G} {t : Fin k}
    (hufac : UFac P A) (hsingle : ∀ a, a < t → ∃ g : G, g ∈ P ∧ A a = {g}) :
    UFac P (normFamilyL t A) := by
  obtain ⟨hinj, hset⟩ := hufac
  choose! γ hγ using hsingle
  have hγm : ∀ a : Fin k, a < t → γ a ∈ P := fun a ha => (hγ a ha).1
  have hγs : ∀ a : Fin k, a < t → A a = {γ a} := fun a ha => (hγ a ha).2
  constructor
  · intro x w w' hw hw'
    have e1 : reprProd (insertNorm γ hγs w) = normShift t γ * x := by
      rw [prod_insert_normShift hγs w, hw]
    have e2 : reprProd (insertNorm γ hγs w') = normShift t γ * x := by
      rw [prod_insert_normShift hγs w', hw']
    have heq := hinj _ _ _ e1 e2
    refine funext fun i => ?_
    apply Subtype.ext
    by_cases h : i < t
    · have h1 : (w i : G) = 1 := by simpa [normFamilyL, h] using (w i).2
      have h2 : (w' i : G) = 1 := by simpa [normFamilyL, h] using (w' i).2
      rw [h1, h2]
    · have hv := congrArg Subtype.val (congrFun heq i)
      have hwv : (↑(insertNorm γ hγs w i) : G) = (w i : G) := by
        simp [insertNorm, h]
      have hwv' : (↑(insertNorm γ hγs w' i) : G) = (w' i : G) := by
        simp [insertNorm, h]
      rw [← hwv, ← hwv']
      exact hv
  · ext x
    constructor
    · rintro ⟨w, rfl⟩
      have hmem : normShift t γ * reprProd w ∈ setSeqProd A :=
        ⟨insertNorm γ hγs w, prod_insert_normShift hγs w⟩
      rw [hset] at hmem
      have key : reprProd w ∈ (P : Set G) := by
        have h2 := Set.mul_mem_mul
          (SetLike.mem_coe.2 (Subgroup.inv_mem (H := P) (normShift_mem hγm)))
          hmem
        simpa [inv_mul_cancel_left] using h2
      exact key
    · intro hx
      have hxP : normShift t γ * x ∈ setSeqProd A := by
        rw [hset]
        exact SetLike.mem_coe.2
          (Subgroup.mul_mem P (normShift_mem hγm) (SetLike.mem_coe.mp hx))
      obtain ⟨f, hf⟩ := hxP
      refine ⟨stripNorm f, ?_⟩
      show reprProd (stripNorm (t := t) f) = x
      have hvalEq : reprProd (insertNorm γ hγs (stripNorm f)) = reprProd f := by
        apply congrArg List.prod
        apply congrArg List.ofFn
        funext i
        by_cases h : i < t
        · simp only [insertNorm, if_pos h]
          symm
          exact Set.mem_singleton_iff.mp (mem_of_eq_set (hγs i h) ((f i).2))
        · simp only [insertNorm, stripNorm, if_neg h]
      have key : reprProd (stripNorm (t := t) f) = (normShift t γ)⁻¹ * reprProd f := by
        rw [← hvalEq, prod_insert_normShift (t := t) hγs (stripNorm (t := t) f),
          inv_mul_cancel_left]
      have hf' : reprProd f = normShift t γ * x := hf
      calc reprProd (stripNorm (t := t) f)
          = (normShift t γ)⁻¹ * reprProd f := key
        _ = (normShift t γ)⁻¹ * (normShift t γ * x) := by rw [hf']
        _ = x := by rw [inv_mul_cancel_left]

/-! ### Small cardinality and index-bookkeeping helpers -/

/-- Cardinality of a singleton set; `Nat.card` form of
`Set.ncard_singleton`, used throughout the size bookkeeping of Theorem 3.1. -/
theorem natCard_set_singleton {α : Type*} (a : α) : Nat.card ({a} : Set α) = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨a, rfl⟩, fun y => Subtype.ext (Set.mem_singleton_iff.mp y.2)⟩

/-- A set of cardinality one is a singleton (tex line 187: "|A_{a,j}| = 1 for
all a < t"). -/
theorem exists_eq_singleton_of_natCard_one {α : Type*} {S : Set α}
    (h : Nat.card S = 1) : ∃ g : α, S = {g} := by
  obtain ⟨z, hz⟩ := Nat.card_eq_one_iff_exists.mp h
  refine ⟨(z : α), Set.ext fun x => ?_⟩
  constructor
  · intro hx
    exact congrArg Subtype.val (hz ⟨x, hx⟩)
  · intro hx
    rw [hx]
    exact z.2

theorem filter_lt_succ_eq_of_notMem {s : Finset ℕ} {j : ℕ} (h : j ∉ s) :
    s.filter (· < j + 1) = s.filter (· < j) := by
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨his, hij⟩
    by_cases hlt : i < j
    · exact ⟨his, hlt⟩
    · have hij' : i = j := by omega
      exact absurd (hij' ▸ his) h
  · rintro ⟨his, hij⟩
    exact ⟨his, by omega⟩

theorem filter_lt_succ_eq_insert {s : Finset ℕ} {j : ℕ} (h : j ∈ s) :
    s.filter (· < j + 1) = insert j (s.filter (· < j)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨his, hij⟩
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hij) with hij' | hij'
    · exact Or.inr ⟨his, hij'⟩
    · rw [hij']
      exact Or.inl rfl
  · rintro (hij | ⟨his, hij⟩)
    · rw [hij]
      exact ⟨h, Nat.lt_succ_self j⟩
    · exact ⟨his, by omega⟩

theorem filter_lt_eq_self_of_subset_Iio {s : Finset ℕ} {n : ℕ}
    (h : s ⊆ Finset.Iio n) : s.filter (· < n) = s :=
  Finset.filter_true_of_mem fun i hi => Finset.mem_Iio.mp (h hi)

/-! ### Extending one chain level through a left-coset transversal
(tex lines 192-196) -/

/-- Left-coset representatives lie in the ambient subgroup `K` ("a full set of
representatives of the left cosets of G_j in G_{j+1}", tex line 192). -/
theorem leftReps_subset {K H : Subgroup G} : leftReps K H ⊆ (K : Set G) := by
  intro c hc
  obtain ⟨q, rfl⟩ := mem_leftReps_iff.mp hc
  exact (cosetSec K H q).property

/-- A product of two elements of subgroup carrier `H` stays in it; set-level
form for membership bookkeeping inside product sets. -/
theorem setMul_subset_coe {H : Subgroup G} :
    ((H : Set G) * (H : Set G)) ⊆ (H : Set G) := by
  intro z hz
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hz
  exact hab ▸ Subgroup.mul_mem H (SetLike.mem_coe.mp ha) (SetLike.mem_coe.mp hb)

/-- If every coordinate before `t` is trivial, an ordered product peels off its
`t`-coordinate; realizes at the level of representations the factorization
`G_j = S A_{t,j} ⋯ A_{k,j}` with `S = {e}` assumed in tex line 189
(d.i_in_s1). -/
theorem prod_split3_of_prefix_one {k : ℕ} {v : Fin k → G} {t : Fin k}
    (hv : ∀ i, i < t → v i = 1) :
    (List.ofFn v).prod =
      v t * (List.ofFn fun a => if t < a then v a else (1 : G)).prod := by
  rw [prod_split3 v t]
  have hpre : (List.ofFn fun a => if a < t then v a else (1 : G)).prod = 1 := by
    have heq : (fun a : Fin k => if a < t then v a else (1 : G))
        = fun _ : Fin k => (1 : G) := by
      funext a
      by_cases h : a < t
      · rw [if_pos h, hv a h]
      · rw [if_neg h]
    rw [heq, prod_ofFn_one]
  rw [hpre, one_mul]

/-- The family realizing `A_{t,j+1} = C_{j+1} A_{t,j}` while keeping every
other factor (`A_{i,j+1} = A_{i,j}` for `i ≠ t`, tex line 193), with `C_{j+1}`
the chosen transversal `leftReps K P` of the left cosets of `P = G_j` inside
`K = G_{j+1}`. -/
def extFamilyL (P K : Subgroup G) {k : ℕ} (A : Fin k → Set G) (t : Fin k) :
    Fin k → Set G :=
  fun i => if i = t then leftReps K P * A i else A i

/-- Any representation of the extended family factors through its `t`
coordinate: `reprProd w = c · reprProd v` with `c ∈ C_{j+1}` a representative,
`v` an `A`-representation carrying the `A t`-part of `(w t)`, and `w` agreeing
with `v` off `t` (tex line 196: `A_{1,j+1} ⋯ A_{k,j+1} = C_{j+1} A_{t,j} ⋯`). -/
theorem reprProd_extFamilyL_decomp {P K : Subgroup G} {k : ℕ} {A : Fin k → Set G}
    {t : Fin k} (hone : ∀ i, i < t → A i = ({1} : Set G))
    (w : ∀ i, extFamilyL P K A t i) :
    ∃ c : G, c ∈ leftReps K P ∧ ∃ v : ∀ i, A i, reprProd w = c * reprProd v ∧
      (w t : G) = c * (v t : G) ∧ ∀ i, i ≠ t → (v i : G) = (w i : G) := by
  have ht : (w t : G) ∈ leftReps K P * A t := by simpa [extFamilyL] using (w t).2
  obtain ⟨c, hcC, y, hyA, hcy⟩ := Set.mem_mul.mp ht
  have hvmem : ∀ i : Fin k, (if i = t then y else (w i : G)) ∈ A i := by
    intro i
    by_cases hi : i = t
    · simpa only [hi, if_pos] using hyA
    · simpa only [extFamilyL, hi, if_neg] using (w i).2
  set v : ∀ i, A i := fun i => ⟨if i = t then y else (w i : G), hvmem i⟩ with hvd
  have hvcoord : ∀ i, (v i : G) = if i = t then y else (w i : G) := fun _ => rfl
  have hvt : (v t : G) = y := by rw [hvcoord t]; exact if_pos rfl
  refine ⟨c, hcC, v, ?_, ?_, fun i hi => by rw [hvcoord i, if_neg hi]⟩
  · have hwpre : ∀ i, i < t → (w i : G) = 1 := fun i hi =>
      Set.mem_singleton_iff.mp
        (mem_of_eq_set (hone i hi) (by simpa [extFamilyL, ne_of_lt hi] using (w i).2))
    have hsfx : (List.ofFn fun a => if t < a then (v a : G) else (1 : G)).prod
        = (List.ofFn fun a => if t < a then (w a : G) else (1 : G)).prod := by
      have hfn : ∀ a : Fin k,
          (if t < a then (v a : G) else (1 : G))
            = (if t < a then (w a : G) else (1 : G)) := by
        intro a
        by_cases h : t < a
        · rw [if_pos h, if_pos h, hvcoord a]
          rw [if_neg (ne_of_gt h)]
        · rw [if_neg h, if_neg h]
      exact congrArg (fun l => List.prod (List.ofFn l)) (funext hfn)
    have hvsplit : reprProd v
        = (v t : G) *
            (List.ofFn fun a => if t < a then (v a : G) else (1 : G)).prod :=
      prod_split3_of_prefix_one (fun i hi => by
        rw [hvcoord i, if_neg (ne_of_lt hi), hwpre i hi])
    have hvs : reprProd v
        = y * (List.ofFn fun a => if t < a then (w a : G) else (1 : G)).prod := by
      rw [hvsplit, hvt, hsfx]
    calc reprProd w
        = (w t : G) *
            (List.ofFn fun a => if t < a then (w a : G) else (1 : G)).prod :=
          prod_split3_of_prefix_one hwpre
      _ = c * (y * (List.ofFn fun a => if t < a then (w a : G) else (1 : G)).prod) := by
          rw [← mul_assoc, ← hcy]
      _ = c * reprProd v := by rw [hvs]
  · rw [hvt]
    exact hcy.symm

/-- The multiplication map `(c, y) ↦ c * y` counting the product of the
transversal with `S` (tex line 195: new cardinalities "as in the j+1 case"). -/
def mulTransMap {P K : Subgroup G} {S : Set G} :
    ↥(leftReps K P ×ˢ S) → ↥(leftReps K P * S) :=
  fun p =>
    let h := Set.mem_prod.mp p.property
    ⟨((p : G × G).1 * (p : G × G).2 : G),
      Set.mem_mul.mpr ⟨(p : G × G).1, h.1, (p : G × G).2, h.2, rfl⟩⟩

/-- Multiplying a subset `S ⊆ P` by the full transversal `leftReps K P`
multiplies its cardinality by `[K : P]`: `mulTransMap` is bijective, injective
because distinct representatives differ outside `P`.  With `natCard_leftReps`
this yields the size step `|A_{t,j+1}| = |C_{j+1}| |A_{t,j}|` of tex line 195. -/
theorem natCard_mul_leftReps {P K : Subgroup G} {S : Set G}
    (hS : S ⊆ ↑P) :
    Nat.card ↥(leftReps K P * S) = P.relIndex K * Nat.card ↥S := by
  have hinj : Function.Injective (@mulTransMap G _ P K S) := by
    rintro p q heq
    have hmul : ((p : G × G).1 * (p : G × G).2 : G)
        = (q : G × G).1 * (q : G × G).2 := congrArg Subtype.val heq
    have hyP : (p : G × G).2 ∈ (P : Set G) :=
      hS (Set.mem_prod.mp p.property).2
    have hy'P : (q : G × G).2 ∈ (P : Set G) :=
      hS (Set.mem_prod.mp q.property).2
    have e1 : (p : G × G).1 *
        ((p : G × G).2 * (q : G × G).2⁻¹) = (q : G × G).1 := by
      calc (p : G × G).1 * ((p : G × G).2 * (q : G × G).2⁻¹)
          = ((p : G × G).1 * (p : G × G).2) * (q : G × G).2⁻¹ := (mul_assoc _ _ _).symm
        _ = ((q : G × G).1 * (q : G × G).2) * (q : G × G).2⁻¹ := by rw [hmul]
        _ = (q : G × G).1 := by rw [mul_inv_cancel_right]
    have key : (p : G × G).2 * (q : G × G).2⁻¹
        = (p : G × G).1⁻¹ * (q : G × G).1 := by rw [← e1, inv_mul_cancel_left]
    have hmem : ((p : G × G).1)⁻¹ * ((q : G × G).1) ∈ (P : Set G) := by
      rw [← key]
      exact SetLike.mem_coe.2
        (Subgroup.mul_mem P (SetLike.mem_coe.mp hyP)
          (Subgroup.inv_mem P (SetLike.mem_coe.mp hy'P)))
    have hcc : (p : G × G).1 = (q : G × G).1 :=
      leftReps_sep (Set.mem_prod.mp p.property).1
        (Set.mem_prod.mp q.property).1 hmem
    have hcyc : (p : G × G).1 * (p : G × G).2
        = (p : G × G).1 * (q : G × G).2 := by
      rw [hmul, ← hcc]
    have hyy : (p : G × G).2 = (q : G × G).2 := mul_left_cancel hcyc
    exact Subtype.ext (Prod.ext hcc hyy)
  have hsurj : ∀ z : ↥(leftReps K P * S), ∃ p : ↥(leftReps K P ×ˢ S),
      mulTransMap p = z := by
    rintro ⟨z, hz⟩
    obtain ⟨c, hc, y, hy, hcy⟩ := Set.mem_mul.mp hz
    refine ⟨⟨(c, y), Set.mem_prod.mpr ⟨hc, hy⟩⟩, Subtype.ext ?_⟩
    show (c * y : G) = _
    exact hcy
  calc Nat.card ↥(leftReps K P * S)
      = Nat.card ↥(leftReps K P ×ˢ S) :=
        (Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩).symm
    _ = Nat.card (↥(leftReps K P) × ↥S) := Nat.card_congr (Equiv.Set.prod _ _)
    _ = Nat.card ↥(leftReps K P) * Nat.card ↥S := Nat.card_prod _ _
    _ = P.relIndex K * Nat.card ↥S := by rw [natCard_leftReps]

/-- The extended family stays inside `K`: kept factors lie in `P ≤ K`, and the
new factor `C_{j+1} A_{t,j}` lies in `K` (tex line 196 concludes
`C_{j+1} G_j = G_{j+1}`). -/
theorem extFamilyL_subset {P K : Subgroup G} {k : ℕ} {A : Fin k → Set G} {t : Fin k}
    (hPK : P ≤ K) (hsub : ∀ i, A i ⊆ ↑P) (i : Fin k) :
    extFamilyL P K A t i ⊆ ↑K := by
  intro z hz
  by_cases hi : i = t
  · subst hi
    simp only [extFamilyL, if_true] at hz
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hz
    refine hab ▸ Subgroup.mul_mem K (SetLike.mem_coe.mp (leftReps_subset ha))
      (SetLike.mem_coe.mpr (hPK (SetLike.mem_coe.mp (hsub _ hb))))
  · simp only [extFamilyL, if_neg hi] at hz
    exact SetLike.mem_coe.mpr (hPK (SetLike.mem_coe.mp (hsub _ hz)))

theorem mem_extFamilyL_of_eq {P K : Subgroup G} {k : ℕ} {A : Fin k → Set G}
    {t i : Fin k} (hi : i = t) {g : G} (hg : g ∈ leftReps K P * A i) :
    g ∈ extFamilyL P K A t i := by
  subst hi
  simpa only [extFamilyL, eq_self_iff_true, if_true] using hg

theorem mem_extFamilyL_of_ne {P K : Subgroup G} {k : ℕ} {A : Fin k → Set G}
    {t i : Fin k} (hi : i ≠ t) {g : G} (hg : g ∈ A i) :
    g ∈ extFamilyL P K A t i := by
  simpa only [extFamilyL, if_neg hi] using hg

/-- Extension step of Theorem 3.1 (tex lines 192-196): an `A` that uniquely
factorizes `P = G_j`, with every factor inside `P` and the leading factors
before block `t` equal to `{1}` (the normalized situation d.i_in_s1 of tex
lines 188-190), extends to a unique factorization of `K = G_{j+1}` by replacing
factor `t` with `C_{j+1} · A_t`, where `C_{j+1} = leftReps K P` is the full set
of left-coset representatives of tex line 192. -/
theorem ufac_extL {P K : Subgroup G} {k : ℕ} {A : Fin k → Set G} {t : Fin k}
    (hPK : P ≤ K) (hufac : UFac P A) (hsub : ∀ i, A i ⊆ ↑P)
    (hone : ∀ i, i < t → A i = ({1} : Set G)) :
    UFac K (extFamilyL P K A t) := by
  obtain ⟨hinj, hset⟩ := hufac
  constructor
  · intro x w w' hw hw'
    obtain ⟨c, hcC, v, hvw, hcwt, hvoff⟩ := reprProd_extFamilyL_decomp hone w
    obtain ⟨c', hcC', v', hvw', hcwt', hvoff'⟩ := reprProd_extFamilyL_decomp hone w'
    rw [hw] at hvw
    rw [hw'] at hvw'
    have hvin : reprProd v ∈ P := by
      have h1 : reprProd v ∈ setSeqProd A := ⟨v, rfl⟩
      rw [hset] at h1
      exact h1
    have hvin' : reprProd v' ∈ P := by
      have h1 : reprProd v' ∈ setSeqProd A := ⟨v', rfl⟩
      rw [hset] at h1
      exact h1
    have e1 : c * (reprProd v * (reprProd v')⁻¹) = c' := by
      calc c * (reprProd v * (reprProd v')⁻¹)
          = (c * reprProd v) * (reprProd v')⁻¹ := (mul_assoc _ _ _).symm
        _ = (c' * reprProd v') * (reprProd v')⁻¹ := by rw [← hvw, ← hvw']
        _ = c' := by rw [mul_inv_cancel_right]
    have key2 : reprProd v * (reprProd v')⁻¹ = c⁻¹ * c' := by
      rw [← e1, inv_mul_cancel_left]
    have hcc : c = c' :=
      leftReps_sep hcC hcC' (by
        rw [← key2]
        exact Subgroup.mul_mem P hvin (Subgroup.inv_mem P hvin'))
    have hrr : reprProd v = reprProd v' := by
      refine mul_left_cancel (a := c) ?_
      calc c * reprProd v = x := hvw.symm
        _ = c' * reprProd v' := hvw'
        _ = c * reprProd v' := by rw [hcc]
    have hveq : v = v' := hinj _ v v' rfl hrr.symm
    refine funext fun i => Subtype.ext ?_
    by_cases hi : i = t
    · subst hi
      rw [hcwt, hcwt', hcc, hveq]
    · rw [← hvoff i hi, ← hvoff' i hi, hveq]
  · ext x
    constructor
    · rintro ⟨w, hx⟩
      obtain ⟨c, hcC, v, hvw, -, -⟩ := reprProd_extFamilyL_decomp hone w
      have hvin : reprProd v ∈ ↑P := by
        have h1 : reprProd v ∈ setSeqProd A := ⟨v, rfl⟩
        rw [hset] at h1
        exact h1
      have hxeq : x = c * reprProd v := hx.symm.trans hvw
      rw [hxeq]
      exact Subgroup.mul_mem K (SetLike.mem_coe.mp (leftReps_subset hcC))
        (SetLike.mem_coe.mp (hPK (SetLike.mem_coe.mp hvin)))
    · intro hxK
      obtain ⟨c, hcC, z, hzP, hczeq⟩ := Set.mem_mul.mp (leftReps_cover hPK hxK)
      obtain ⟨f, hfx⟩ : z ∈ setSeqProd A := by
        rw [hset]
        exact hzP
      have hwi : ∀ i, (if i = t then c * (f i : G) else (f i : G))
          ∈ extFamilyL P K A t i := by
        intro i
        by_cases hi : i = t
        · refine mem_extFamilyL_of_eq hi ?_
          rw [if_pos hi]
          exact Set.mul_mem_mul hcC (f i).property
        · refine mem_extFamilyL_of_ne hi ?_
          rw [if_neg hi]
          exact (f i).property
      set w : ∀ i, extFamilyL P K A t i :=
        fun i => ⟨if i = t then c * (f i : G) else (f i : G), hwi i⟩ with hwdef
      refine ⟨fun i => ⟨if i = t then c * (f i : G) else (f i : G), hwi i⟩, ?_⟩
      have hpref : ∀ i, i < t → (f i : G) = 1 := fun i hi =>
        Set.mem_singleton_iff.mp (mem_of_eq_set (hone i hi) (f i).property)
      have hwpre : ∀ i, i < t → (w i : G) = 1 := by
        intro i hi
        show (if i = t then c * (f i : G) else (f i : G)) = 1
        rw [if_neg (ne_of_lt hi)]
        exact hpref i hi
      have hwsplit : (List.ofFn fun i => (w i : G)).prod = (w t : G) *
          (List.ofFn fun a => if t < a then (w a : G) else (1 : G)).prod :=
        prod_split3_of_prefix_one hwpre
      have hwvalt : (w t : G) = c * (f t : G) := by
        show (if t = t then c * (f t : G) else (f t : G)) = _
        rw [if_pos rfl]
      have hfsplit : (List.ofFn fun i => (f i : G)).prod = (f t : G) *
          (List.ofFn fun a => if t < a then (f a : G) else (1 : G)).prod :=
        prod_split3_of_prefix_one hpref
      have hsfxeq : (List.ofFn fun a => if t < a then (w a : G) else (1 : G)).prod
          = (List.ofFn fun a => if t < a then (f a : G) else (1 : G)).prod := by
        have hpt : ∀ a : Fin k, (if t < a then (w a : G) else (1 : G))
            = (if t < a then (f a : G) else (1 : G)) := by
          intro a
          by_cases h : t < a
          · show (if t < a then (if a = t then c * (f a : G) else (f a : G) : G)
                else (1 : G)) = _
            rw [if_pos h, if_pos h, if_neg (ne_of_gt h)]
          · rw [if_neg h, if_neg h]
        exact congrArg (fun l => List.prod (List.ofFn l)) (funext hpt)
      calc reprProd w
          = (List.ofFn fun i => (w i : G)).prod := rfl
        _ = (w t : G) *
              (List.ofFn fun a => if t < a then (w a : G) else (1 : G)).prod :=
            hwsplit
        _ = (c * (f t : G)) *
              (List.ofFn fun a => if t < a then (w a : G) else (1 : G)).prod :=
            by rw [hwvalt]
        _ = c * ((f t : G) *
              (List.ofFn fun a => if t < a then (f a : G) else (1 : G)).prod) := by
            rw [hsfxeq, mul_assoc]
        _ = c * reprProd f := congrArg (fun w : G => c * w) hfsplit.symm
        _ = x := by
            have h9 : c * reprProd f = c * z := congrArg (fun w : G => c * w) hfx
            rw [h9]
            exact hczeq

/-! ### Mirroring: discharging the "for all a > t" branch (tex lines 159-160)

The one-sidedness condition of tex lines 161-163 allows the empty prefix case
"either for all a < t or for all a > t".  Reversing factor order through index
reversal `finRev` and inversion turns a right-handed extension into a
left-handed one, so only the left-handed lemma above needs a printed-proof
transcription. -/

/-- Mirror family: coordinate `i` holds the inverses of coordinate
`finRev i`. -/
def mirrorFam {k : ℕ} (A : Fin k → Set G) : Fin k → Set G :=
  fun i => (fun g : G => g⁻¹) ⁻¹' A (finRev i)

/-- Turn an `A`-representation into a mirrored one (reverse order and invert). -/
def mirrorTupleOf {k : ℕ} {A : Fin k → Set G} (f : ∀ i, A i) :
    ∀ i, mirrorFam A i := fun i =>
  ⟨((f (finRev i)) : G)⁻¹, by
    show (((f (finRev i)) : G)⁻¹)⁻¹ ∈ A (finRev i)
    rw [inv_inv]
    exact (f _).2⟩

/-- Turn a mirrored representation back into an `A`-representation. -/
def unMirrorTuple {k : ℕ} {A : Fin k → Set G} (w : ∀ i, mirrorFam A i) :
    ∀ i, A i := fun i =>
  ⟨((w (finRev i)) : G)⁻¹, by
    have hp : ((w (finRev i)) : G)⁻¹ ∈ A (finRev (finRev i)) :=
      Set.mem_preimage.mp (w (finRev i)).property
    rwa [finRev_finRev] at hp⟩

theorem reprProd_mirrorTupleOf {k : ℕ} {A : Fin k → Set G} (f : ∀ i, A i) :
    (List.ofFn fun i => ((mirrorTupleOf f) i : G)).prod
      = ((List.ofFn fun i => (f i : G)).prod)⁻¹ :=
  prod_mirror_inv fun i => (f i : G)

theorem reprProd_unMirrorTuple {k : ℕ} {A : Fin k → Set G}
    (w : ∀ i, mirrorFam A i) :
    (List.ofFn fun i => ((unMirrorTuple w) i : G)).prod
      = ((List.ofFn fun i => (w i : G)).prod)⁻¹ :=
  prod_mirror_inv fun i => (w i : G)

theorem setSeqProd_mirrorFam {k : ℕ} (A : Fin k → Set G) :
    setSeqProd (mirrorFam A) = (setSeqProd A)⁻¹ := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨unMirrorTuple w, ?_⟩
    rw [reprProd_unMirrorTuple]
  · intro hx
    rw [Set.mem_inv] at hx
    obtain ⟨f, hf⟩ := hx
    refine ⟨mirrorTupleOf f, ?_⟩
    show (List.ofFn fun i => ((mirrorTupleOf f) i : G)).prod = x
    rw [reprProd_mirrorTupleOf, hf]
    simp

/-- Unique-representation property transfers through mirroring; note
`(setSeqProd A)⁻¹ = ↑P` because `P` is a subgroup. -/
theorem ufac_mirrorFam {P : Subgroup G} {k : ℕ} {A : Fin k → Set G}
    (h : UFac P A) : UFac P (mirrorFam A) := by
  refine ⟨?_, ?_⟩
  · intro x w w' hw hw'
    simp only [reprProd] at hw hw'
    have e1 := h.1 x⁻¹ (unMirrorTuple w) (unMirrorTuple w')
    simp only [reprProd] at e1
    rw [reprProd_unMirrorTuple, hw, reprProd_unMirrorTuple, hw'] at e1
    have hu := e1 rfl rfl
    refine funext fun i => Subtype.ext ?_
    have hv : ((w i : G))⁻¹ = ((w' i : G))⁻¹ := by
      have h2 := congrArg Subtype.val (congrFun hu (finRev i))
      simp only [unMirrorTuple, Subtype.coe_mk] at h2
      rw [finRev_finRev] at h2
      exact h2
    exact inv_injective hv
  · rw [setSeqProd_mirrorFam, h.2]
    ext g
    simp only [Set.mem_inv, SetLike.mem_coe]
    constructor
    · intro hg
      simpa using Subgroup.inv_mem P hg
    · intro hg
      exact Subgroup.inv_mem P hg

/-- Mirroring preserves cardinalities. -/
theorem natCard_mirrorFam {k : ℕ} (A : Fin k → Set G) (i : Fin k) :
    Nat.card (mirrorFam A i) = Nat.card (A (finRev i)) := by
  have hinj : Function.Injective
      (fun p : ↥(A (finRev i)) => (⟨(p : G)⁻¹,
        show (((p : G)⁻¹)⁻¹ ∈ A (finRev i)) from by rw [inv_inv]; exact p.property⟩ :
        ↥(mirrorFam A i))) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ heq
    have hval : (a : G)⁻¹ = (b : G)⁻¹ := congrArg Subtype.val heq
    exact Subtype.ext (by simpa using congrArg (·⁻¹) hval)
  have hsurj : ∀ y : ↥(mirrorFam A i), ∃ p : ↥(A (finRev i)),
      (⟨(p : G)⁻¹, show (((p : G)⁻¹)⁻¹ ∈ A (finRev i)) from by
          rw [inv_inv]; exact p.property⟩ : ↥(mirrorFam A i)) = y := by
    rintro ⟨y, hy⟩
    have hp : ((y : G)⁻¹ ∈ A (finRev i)) := Set.mem_preimage.mp hy
    exact ⟨⟨y⁻¹, hp⟩, Subtype.ext (by simp)⟩
  exact (Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩).symm

/-! ### The chain induction (tex lines 168-200) -/

/-- Stage invariant of tex lines 169-174 (d.A1jA2j): at chain index `j` there
is a uniquely-representing family for `Gd j` with every factor inside `Gd j`
and factor sizes equal to the products of the consumed edge indices
`(s t).filter (· < j)`. -/
theorem exists_stage_ufac {n k : ℕ} {Gd : ℕ → Subgroup G}
    (h0 : Gd 0 = ⊥) (hle : ∀ j, Gd j ≤ Gd (j + 1))
    {s : Fin k → Finset ℕ}
    (hs_disj : ∀ t t', t ≠ t' → s t ∩ s t' = ∅)
    (hs_cov : ∀ j, j < n → ∃ t, j ∈ s t)
    (hs_one : ∀ j, j < n → ∀ t, j ∈ s t →
      (∀ a, a < t → (s a ∩ Finset.Iio (j + 1)) = ∅) ∨
      (∀ a, a > t → (s a ∩ Finset.Iio (j + 1)) = ∅))
    (j : ℕ) (hjn : j ≤ n) :
    ∃ A : Fin k → Set G, UFac (Gd j) A ∧ (∀ i, A i ⊆ ↑(Gd j)) ∧
      ∀ t, Nat.card (A t)
        = ∏ i ∈ (s t).filter (· < j), (Gd i).relIndex (Gd (i + 1)) := by
  have hEdgeIn : ∀ (T : Finset ℕ) (x : ℕ), x ∉ T.filter (· < x) := by
    intro T x hi
    rcases Finset.mem_filter.mp hi with ⟨_, hlt⟩
    exact absurd hlt (Nat.lt_irrefl x)
  induction j with
  | zero =>
    refine ⟨fun _ => ({1} : Set G), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro x w w' _ _
      refine funext fun i => Subtype.ext ?_
      show (w i : G) = (w' i : G)
      rw [Set.mem_singleton_iff.mp (w i).2, Set.mem_singleton_iff.mp (w' i).2]
    · ext x
      constructor
      · rintro ⟨w, rfl⟩
        have hev : (fun i : Fin k => (w i : G)) = fun _ => (1 : G) :=
          funext fun i => Set.mem_singleton_iff.mp (w i).2
        show ((List.ofFn fun i => (w i : G)).prod : G) ∈ _
        rw [hev, prod_ofFn_one]
        exact SetLike.mem_coe.2 (Subgroup.one_mem _)
      · intro hx
        have hx0 : x ∈ Gd 0 := SetLike.mem_coe.mp hx
        rw [h0] at hx0
        have hx1 : (x : G) = 1 := Subgroup.mem_bot.mp hx0
        subst hx1
        exact ⟨fun _ => ⟨1, rfl⟩, prod_ofFn_one⟩
    · intro i z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact SetLike.mem_coe.2 (Subgroup.one_mem _)
    · intro t
      have hf : (s t).filter (· < 0) = ∅ :=
        Finset.eq_empty_of_forall_notMem fun i hi =>
          absurd (Finset.mem_filter.mp hi).2 (Nat.not_lt_zero i)
      rw [natCard_set_singleton, hf, Finset.prod_empty]
  | succ j ih =>
    obtain ⟨A, hU, hSub, hCard⟩ := ih (le_trans (Nat.le_succ j) hjn)
    have hjlt : j < n := Nat.lt_of_succ_le hjn
    obtain ⟨t, hts⟩ := hs_cov j hjlt
    have hnotMem : ∀ u, u ≠ t → j ∉ s u := by
      intro u hue hju
      exact absurd (Finset.mem_inter.mpr ⟨hju, hts⟩)
        (by rw [hs_disj u t hue]; exact Finset.notMem_empty j)
    have hfiltE : ∀ a, (s a ∩ Finset.Iio (j + 1)) = ∅ →
        ((s a).filter (· < j) = ∅ ∧ (s a).filter (· < j + 1) = ∅) := by
      intro a hInt
      constructor
      · refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
        obtain ⟨his, hilt⟩ := Finset.mem_filter.mp hi
        exact absurd (Finset.mem_inter.mpr ⟨his,
            Finset.mem_Iio.mpr (Nat.lt_succ_of_lt hilt)⟩)
          (by rw [hInt]; exact Finset.notMem_empty i)
      · refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
        obtain ⟨his, hilt⟩ := Finset.mem_filter.mp hi
        exact absurd (Finset.mem_inter.mpr ⟨his, Finset.mem_Iio.mpr hilt⟩)
          (by rw [hInt]; exact Finset.notMem_empty i)
    rcases hs_one j hjlt t hts with hL | hR
    · -- left-handed case: every earlier block is empty (tex lines 183-190);
      -- normalize leading factors to `{1}` (Lemma 2.2, d.i_in_s1) and extend
      -- factor `t` by the left-coset transversal (tex lines 192-196)
      have hsL : ∀ a, a < t →
          ((s a).filter (· < j) = ∅ ∧ (s a).filter (· < j + 1) = ∅) :=
        fun a ha => hfiltE a (hL a ha)
      have hsingleL : ∀ a, a < t → ∃ g : G, g ∈ ↑(Gd j) ∧ A a = {g} := by
        intro a ha
        have hc : Nat.card (A a) = 1 := by
          rw [hCard a, (hsL a ha).1, Finset.prod_empty]
        obtain ⟨g, hg⟩ := exists_eq_singleton_of_natCard_one hc
        refine ⟨g, hSub a (by rw [hg]; exact rfl), hg⟩
      choose! γ hγP hγS using hsingleL
      have hNFufac : UFac (Gd j) (normFamilyL t A) :=
        ufac_normL hU (fun a ha => ⟨γ a, hγP a ha, hγS a ha⟩)
      have hNFsub : ∀ i, normFamilyL t A i ⊆ ↑(Gd j) := by
        intro i z hz
        by_cases hi : i < t
        · have hz1 : z ∈ ({1} : Set G) := by
            simpa only [normFamilyL, hi, if_pos] using hz
          rw [Set.mem_singleton_iff.mp hz1]
          exact SetLike.mem_coe.2 (Subgroup.one_mem _)
        · have hz' : z ∈ A i := by
            simpa only [normFamilyL, hi, if_neg] using hz
          exact hSub i hz'
      refine ⟨extFamilyL (Gd j) (Gd (j + 1)) (normFamilyL t A) t,
        ufac_extL (hle j) hNFufac hNFsub (fun i hi => by
          simpa only [normFamilyL, hi, if_pos]), ?_, ?_⟩
      · intro i
        exact extFamilyL_subset (hle j) hNFsub i
      · intro u
        by_cases hul : u < t
        · have heq : extFamilyL (Gd j) (Gd (j + 1)) (normFamilyL t A) t u
            = ({1} : Set G) := by
            show (if u = t then _ else normFamilyL t A u) = _
            rw [if_neg (ne_of_lt hul)]
            show (if u < t then ({1} : Set G) else A u) = ({1} : Set G)
            rw [if_pos hul]
          rw [heq, natCard_set_singleton, (hsL u hul).2, Finset.prod_empty]
        · by_cases hue : u = t
          · rw [hue]
            have heq : extFamilyL (Gd j) (Gd (j + 1)) (normFamilyL t A) t t
                = leftReps (Gd (j + 1)) (Gd j) * normFamilyL t A t := by
              show (if t = t then _ else _) = _
              rw [if_pos rfl]
            have hNFt : normFamilyL t A t = A t := by
              show (if t < t then _ else A t) = _
              rw [if_neg (lt_irrefl t)]
            calc Nat.card ↥(extFamilyL (Gd j) (Gd (j + 1)) (normFamilyL t A) t t)
                = Nat.card ↥(leftReps (Gd (j + 1)) (Gd j) * normFamilyL t A t) := by
                    rw [heq]
              _ = (Gd j).relIndex (Gd (j + 1)) * Nat.card ↥(normFamilyL t A t) :=
                    natCard_mul_leftReps (hNFsub t)
              _ = (Gd j).relIndex (Gd (j + 1)) * Nat.card ↥(A t) := by
                    rw [hNFt]
              _ = (Gd j).relIndex (Gd (j + 1)) *
                    ∏ i ∈ (s t).filter (· < j), (Gd i).relIndex (Gd (i + 1)) :=
                    congrArg _ (hCard t)
              _ = ∏ i ∈ (s t).filter (· < j + 1),
                    (Gd i).relIndex (Gd (i + 1)) := by
                    rw [filter_lt_succ_eq_insert hts,
                      Finset.prod_insert (hEdgeIn (s t) j)]
          · have heq : extFamilyL (Gd j) (Gd (j + 1)) (normFamilyL t A) t u
                = A u := by
              show (if u = t then _ else (if u < t then ({1} : Set G) else A u)) = _
              rw [if_neg hue]
              show (if u < t then ({1} : Set G) else A u) = A u
              rw [if_neg hul]
            rw [heq, hCard u,
              filter_lt_succ_eq_of_notMem (hnotMem u hue)]
    · -- right-handed case: every later block is empty (tex lines 181-185,
      -- second alternative); mirror factor order and reduce to the
      -- left-handed extension above
      have hsR : ∀ a, t < a →
          ((s a).filter (· < j) = ∅ ∧ (s a).filter (· < j + 1) = ∅) :=
        fun a ha => hfiltE a (hR a ha)
      have hBsub : ∀ i, mirrorFam A i ⊆ ↑(Gd j) := by
        intro i g hg
        have hg' : (g : G)⁻¹ ∈ ↑(Gd j) := hSub (finRev i) (Set.mem_preimage.mp hg)
        exact SetLike.mem_coe.mpr (by
          simpa using Subgroup.inv_mem (Gd j)
            (SetLike.mem_coe.mp hg'))
      have hBcard : ∀ i, Nat.card (mirrorFam A i) = Nat.card (A (finRev i)) :=
        fun i => natCard_mirrorFam A i
      have hsingleR : ∀ a, a < finRev t →
          ∃ g : G, g ∈ ↑(Gd j) ∧ mirrorFam A a = {g} := by
        intro a ha
        have hfa : t < finRev a := by
          have h1 := finRev_lt_finRev (k := k) ha
          rwa [finRev_finRev] at h1
        have hc : Nat.card (mirrorFam A a) = 1 := by
          rw [hBcard a, hCard (finRev a), (hsR (finRev a) hfa).1,
            Finset.prod_empty]
        obtain ⟨g, hg⟩ := exists_eq_singleton_of_natCard_one hc
        refine ⟨g, hBsub a (by rw [hg]; exact rfl), hg⟩
      choose! δ hδP hδS using hsingleR
      have hNBufac : UFac (Gd j) (normFamilyL (finRev t) (mirrorFam A)) :=
        ufac_normL (ufac_mirrorFam hU) (fun a ha => ⟨δ a, hδP a ha, hδS a ha⟩)
      have hNBsub : ∀ i, normFamilyL (finRev t) (mirrorFam A) i ⊆ ↑(Gd j) := by
        intro i z hz
        by_cases hi : i < finRev t
        · have hz1 : z ∈ ({1} : Set G) := by
            simpa only [normFamilyL, hi, if_pos] using hz
          rw [Set.mem_singleton_iff.mp hz1]
          exact SetLike.mem_coe.2 (Subgroup.one_mem _)
        · have hz' : z ∈ mirrorFam A i := by
            simpa only [normFamilyL, hi, if_neg] using hz
          exact hBsub i hz'
      refine ⟨mirrorFam
        (extFamilyL (Gd j) (Gd (j + 1)) (normFamilyL (finRev t) (mirrorFam A))
          (finRev t)),
        ufac_mirrorFam (ufac_extL (hle j) hNBufac hNBsub (fun i hi => by
          simpa only [normFamilyL, hi, if_pos])), ?_, ?_⟩
      · intro i g hg
        have hg' : (g : G)⁻¹ ∈ ↑(Gd (j + 1)) :=
          extFamilyL_subset (hle j) hNBsub (finRev i) (Set.mem_preimage.mp hg)
        exact SetLike.mem_coe.mpr (by
          simpa using Subgroup.inv_mem (Gd (j + 1))
            (SetLike.mem_coe.mp hg'))
      · intro u
        rw [natCard_mirrorFam]
        by_cases hut : u = t
        · rw [hut]
          have heq : extFamilyL (Gd j) (Gd (j + 1))
                (normFamilyL (finRev t) (mirrorFam A)) (finRev t) (finRev t)
              = leftReps (Gd (j + 1)) (Gd j)
                  * normFamilyL (finRev t) (mirrorFam A) (finRev t) := by
            show (if finRev t = finRev t then _ else _) = _
            rw [if_pos rfl]
          have hNFt : normFamilyL (finRev t) (mirrorFam A) (finRev t)
                = mirrorFam A (finRev t) := by
            show (if finRev t < finRev t then _ else _) = _
            rw [if_neg (lt_irrefl (finRev t))]
          calc Nat.card ↥(extFamilyL (Gd j) (Gd (j + 1))
                    (normFamilyL (finRev t) (mirrorFam A)) (finRev t) (finRev t))
              = Nat.card ↥(leftReps (Gd (j + 1)) (Gd j)
                    * normFamilyL (finRev t) (mirrorFam A) (finRev t)) := by
                  rw [heq]
            _ = (Gd j).relIndex (Gd (j + 1)) *
                  Nat.card ↥(normFamilyL (finRev t) (mirrorFam A) (finRev t)) :=
                  natCard_mul_leftReps (hNBsub (finRev t))
            _ = (Gd j).relIndex (Gd (j + 1)) * Nat.card ↥(mirrorFam A (finRev t)) :=
                  by rw [hNFt]
            _ = (Gd j).relIndex (Gd (j + 1)) * Nat.card ↥(A (finRev (finRev t))) :=
                  by rw [hBcard]
            _ = (Gd j).relIndex (Gd (j + 1)) * Nat.card ↥(A t) :=
                  by rw [finRev_finRev]
            _ = (Gd j).relIndex (Gd (j + 1)) *
                  ∏ i ∈ (s t).filter (· < j), (Gd i).relIndex (Gd (i + 1)) :=
                  congrArg _ (hCard t)
            _ = ∏ i ∈ (s t).filter (· < j + 1),
                    (Gd i).relIndex (Gd (i + 1)) := by
                  rw [filter_lt_succ_eq_insert hts,
                    Finset.prod_insert (hEdgeIn (s t) j)]
        · by_cases hult : u < t
          · -- earlier block: untouched by the mirrored normalization
            have hfu : finRev t < finRev u := finRev_lt_finRev hult
            have huNE : finRev u ≠ finRev t := ne_of_gt hfu
            have hnlt : ¬ (finRev u < finRev t) := lt_asymm hfu
            have heq : extFamilyL (Gd j) (Gd (j + 1))
                  (normFamilyL (finRev t) (mirrorFam A)) (finRev t) (finRev u)
                = mirrorFam A (finRev u) := by
              show (if finRev u = finRev t then _
                  else normFamilyL (finRev t) (mirrorFam A) (finRev u)) = _
              rw [if_neg huNE]
              show (if finRev u < finRev t then ({1} : Set G)
                  else mirrorFam A (finRev u)) = mirrorFam A (finRev u)
              rw [if_neg hnlt]
            rw [heq, hBcard (finRev u), finRev_finRev, hCard u,
              filter_lt_succ_eq_of_notMem (hnotMem u (ne_of_lt hult))]
          · -- later block: normalized away, matching the empty filter
            have htlt : t < u :=
              lt_of_le_of_ne (le_of_not_gt hult) (Ne.symm hut)
            have hfu : finRev u < finRev t := finRev_lt_finRev htlt
            have heq : extFamilyL (Gd j) (Gd (j + 1))
                  (normFamilyL (finRev t) (mirrorFam A)) (finRev t) (finRev u)
                = ({1} : Set G) := by
              show (if finRev u = finRev t then _
                  else normFamilyL (finRev t) (mirrorFam A) (finRev u)) = _
              rw [if_neg (ne_of_lt hfu)]
              show (if finRev u < finRev t then ({1} : Set G)
                  else mirrorFam A (finRev u)) = ({1} : Set G)
              rw [if_pos hfu]
            rw [heq, natCard_set_singleton, (hsR u htlt).2, Finset.prod_empty]

/-- Theorem 3.1 (`thm2`) of McCulloch26-1, Section 3 ("A Sufficient Condition
for $k$-Factorizations to Exist").

If `{e} = Gd 0 ≤ ⋯ ≤ Gd n = G` is a subgroup chain whose edge indices can be
partitioned into blocks `s t ⊆ {0, …, n-1}` satisfying the one-sidedness
condition of tex lines 161-163 — for each edge `j < n` carried by block `t`,
every earlier or every later block avoids the edges `≤ j` — and each block's
edge-index product equals `a t`, then there are subsets `A t` realizing a
k-fold factorization `G = A 0 ⋯ A (k-1)` with `|A t| = a t`.

Encoding deltas vs. the printed statement (tex lines 148-166): chain steps are
non-strict `Gd j ≤ Gd (j+1)` (strictness unused by the proof), edges are
0-based (`Gd i ≤ Gd (i+1)` corresponds to paper edge $i{+}1$), the total-order
side condition $\sum_i a_i = |G|$ and positivity of the $a_i$ are dropped (both
follow from the hypotheses in any application), and factorization is encoded
as unique representation (`IsFactorization`), which for finite groups matches
the multiplication map being bijective.

Source:
/home/chz/src/gamskil/docs/arxiv/2607.20569v3/Some_Answers_Factorization.tex
lines 148-166 (statement), 168-200 (printed proof). -/
theorem theorem_3_1 {n k : ℕ} {Gd : ℕ → Subgroup G}
    (h0 : Gd 0 = ⊥) (hn : Gd n = ⊤) (hle : ∀ j, Gd j ≤ Gd (j + 1))
    (a : Fin k → ℕ) (s : Fin k → Finset ℕ)
    (hs_sub : ∀ t, s t ⊆ Finset.Iio n)
    (hs_disj : ∀ t t', t ≠ t' → s t ∩ s t' = ∅)
    (hs_cov : ∀ j, j < n → ∃ t, j ∈ s t)
    (hs_one : ∀ j, j < n → ∀ t, j ∈ s t →
      (∀ a', a' < t → (s a' ∩ Finset.Iio (j + 1)) = ∅) ∨
      (∀ a', a' > t → (s a' ∩ Finset.Iio (j + 1)) = ∅))
    (hs_card : ∀ t, ∏ i ∈ s t, (Gd i).relIndex (Gd (i + 1)) = a t) :
    ∃ A : Fin k → Set G, IsFactorization A ∧ ∀ t, Nat.card (A t) = a t := by
  obtain ⟨A, hU, -, hCard⟩ :=
    exists_stage_ufac h0 hle hs_disj hs_cov hs_one n (Nat.le_refl n)
  refine ⟨A, fun x => ?_, fun t => ?_⟩
  · have hx : x ∈ setSeqProd A := by
      rw [hU.2, hn]
      exact SetLike.mem_coe.2 (Subgroup.mem_top _)
    obtain ⟨f, hf⟩ := hx
    exact ⟨f, hf, fun f' hf' => (hU.1 x f f' hf hf').symm⟩
  · calc Nat.card (A t)
        = ∏ i ∈ (s t).filter (· < n), (Gd i).relIndex (Gd (i + 1)) :=
          hCard t
      _ = ∏ i ∈ s t, (Gd i).relIndex (Gd (i + 1)) :=
          congrArg (fun T => ∏ i ∈ T, (Gd i).relIndex (Gd (i + 1)))
            (filter_lt_eq_self_of_subset_Iio (hs_sub t))
      _ = a t := hs_card t
