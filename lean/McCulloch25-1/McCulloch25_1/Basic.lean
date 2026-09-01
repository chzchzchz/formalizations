import Mathlib.Tactic

/-!
# Incidence gain graphs: definitions for McCulloch25-1

Definitions transcribed from Ryan McCulloch, *Incidence Gain Graphs and
Generalized Quadrangles*, arXiv:2502.01805, source cached at
`/home/chz/src/gamskil/docs/arxiv/2502.01805/main.tex` (cited below as
"main.tex" with line numbers).
-/

namespace McCulloch25_1

variable {P B : Type _}

/-- An incidence structure `(𝒫, ℬ, I)`: points, lines, incidence
(main.tex line 40; the paper's symmetry requirement `p I b ↔ b I p` is handled
by taking the point-to-line relation as primitive). -/
structure IncidenceStruct (P B : Type _) where
  /-- Point `p` incident with line `b` (`p I b`, main.tex line 40). -/
  Incident : P → B → Prop

namespace IncidenceStruct

variable (S : IncidenceStruct P B)

/-- Linear space axioms (main.tex lines 77–83). -/
structure IsLinearSpace (S : IncidenceStruct P B) : Prop where
  /-- Any two distinct points are incident with exactly one common line
  (axiom 1, main.tex line 80). -/
  existsUnique_line (p q : P) (hne : p ≠ q) :
    ∃! b, S.Incident p b ∧ S.Incident q b
  /-- Each line is incident with at least two points (axiom 2,
  main.tex line 81). -/
  two_pts (b : B) : ∃ p q : P, p ≠ q ∧ S.Incident p b ∧ S.Incident q b
  /-- There exist a point and a line that are not incident (axiom 3,
  main.tex line 82). -/
  nonincident : ∃ p : P, ∃ b : B, ¬ S.Incident p b

/-- Vertices `𝒫 ∪ ℬ` of the incidence graph (main.tex line 40); elements of
chains (main.tex line 63). -/
inductive Obj (P B : Type _)
  | /-- A point of `𝒫`. -/ pt : P → Obj P B
  | /-- A line of `ℬ`. -/ ln : B → Obj P B

/-- Sort tag: `true` for points, `false` for lines. Adjacent chain elements
have different tags, which yields the parity fact of main.tex line 63 (same
sort iff even distance). -/
def Obj.tag : Obj P B → Bool
  | .pt _ => true
  | .ln _ => false

/-- Symmetric incidence between objects (main.tex line 40: `p I b ↔ b I p`;
main.tex line 63: `u_i` incident with `u_{i-1}`). -/
def ObjInc (S : IncidenceStruct P B) : Obj P B → Obj P B → Prop
  | .pt p, .ln b => S.Incident p b
  | .ln b, .pt p => S.Incident p b
  | _, _ => False

theorem objInc_tag_ne {u v : Obj P B} (h : S.ObjInc u v) : u.tag ≠ v.tag := by
  cases u <;> cases v <;> simp_all [Obj.tag, ObjInc]

/-- Symmetry of the object-incidence relation (main.tex line 40:
$p\ \mathrm{I}\ b \leftrightarrow b\ \mathrm{I}\ p$). -/
theorem objInc_symm {u v : Obj P B} (h : S.ObjInc u v) : S.ObjInc v u := by
  cases u <;> cases v <;> exact h

/-- Adjacent objects along a chain have opposite sorts (main.tex line 63),
so two point-sorted objects are never incident. -/
theorem not_objInc_pt_pt {P B : Type _} {S : IncidenceStruct P B}
    (x y : P) : ¬ S.ObjInc (.pt x) (.pt y) := by
  intro h
  exact h

/-- Two line-sorted objects are never incident (main.tex line 63). -/
theorem not_objInc_ln_ln {P B : Type _} {S : IncidenceStruct P B}
    (b c : B) : ¬ S.ObjInc (.ln b) (.ln c) := by
  intro h
  exact h

/-- Consecutive incidence along a list of objects: the body of a walk/chain
(main.tex line 63). -/
inductive ChainSeq (S : IncidenceStruct P B) : List (Obj P B) → Prop
  | /-- The empty list. -/ nil : ChainSeq S []
  | /-- A single object. -/ single (u : Obj P B) : ChainSeq S [u]
  | /-- One incidence step followed by a chain continuation. -/
    cons {u v : Obj P B} {t : List (Obj P B)} (h : S.ObjInc u v)
      (c : ChainSeq S (v :: t)) : ChainSeq S (u :: v :: t)

/-- A `k`-chain from `u` to `v` (main.tex line 63): a list of `k + 1` objects
starting at `u`, ending at `v`, consecutively incident. The sequence is data,
so two chains are equal exactly when their sequences coincide. -/
structure Chain (S : IncidenceStruct P B) (k : ℕ) (u v : Obj P B) where
  /-- The objects `u₀, …, u_k` of the chain. -/
  seq : List (Obj P B)
  /-- Length `k + 1`. -/
  len : seq.length = k + 1
  /-- First object is `u`. -/
  head : seq.head? = some u
  /-- Last object is `v`. -/
  last : seq.getLast? = some v
  /-- Consecutive incidence. -/
  ok : ChainSeq S seq

/-- The trivial `0`-chain `(u)` (main.tex line 63, `k = 0`). -/
def Chain.refl (u : Obj P B) : S.Chain 0 u u where
  seq := [u]
  len := rfl
  head := rfl
  last := rfl
  ok := .single u

/-- Prepend one incidence step to a chain (main.tex line 63). -/
def Chain.step1 {u v w : Obj P B} {k : ℕ} (h : S.ObjInc u v)
    (c : S.Chain k v w) : S.Chain (k + 1) u w := by
  obtain ⟨seq, hlen, hhead, hlast, hok⟩ := c
  cases hc : seq with
  | nil => rw [hc] at hlen; simp at hlen
  | cons a t =>
      subst hc
      have hav : a = v := by simpa using hhead
      subst hav
      exact ⟨u :: a :: t, by simp [hlen], rfl, by simpa using hlast,
        ChainSeq.cons h hok⟩

/-- Inversion: a chain body of length two is one incidence step
(main.tex line 63). -/
theorem chainSeq_pair {x y : Obj P B} (h : S.ChainSeq [x, y]) :
    S.ObjInc x y := by
  cases h with
  | cons hxy _ => exact hxy

/-- Inversion: a chain body of length three (main.tex line 63). -/
theorem chainSeq_triple {x y z : Obj P B} (h : S.ChainSeq [x, y, z]) :
    S.ObjInc x y ∧ S.ObjInc y z := by
  cases h with
  | cons hxy c' => exact ⟨hxy, chainSeq_pair S c'⟩

/-- Inversion: a chain body of length four (main.tex line 63). -/
theorem chainSeq_quad {w x y z : Obj P B} (h : S.ChainSeq [w, x, y, z]) :
    S.ObjInc w x ∧ S.ObjInc x y ∧ S.ObjInc y z := by
  cases h with
  | cons hwx c' => exact ⟨hwx, chainSeq_triple S c'⟩

theorem Chain.zero_seq {u v : Obj P B} (c : S.Chain 0 u v) :
    c.seq = [u] ∧ u = v := by
  obtain ⟨seq, hlen, hhead, hlast, hok⟩ := c
  show seq = [u] ∧ u = v
  cases hs : seq with
  | nil => rw [hs] at hlen; simp at hlen
  | cons a t =>
      cases t with
      | nil =>
          rw [hs] at hhead hlast
          simp at hhead hlast
          subst hs
          exact ⟨by simp [hhead], by rw [← hhead]; exact hlast⟩
      | cons b t' => rw [hs] at hlen; simp at hlen

theorem Chain.one_seq {u v : Obj P B} (c : S.Chain 1 u v) :
    c.seq = [u, v] ∧ S.ObjInc u v := by
  obtain ⟨seq, hlen, hhead, hlast, hok⟩ := c
  show seq = [u, v] ∧ S.ObjInc u v
  cases hs : seq with
  | nil => rw [hs] at hlen; simp at hlen
  | cons a t =>
      cases t with
      | nil => rw [hs] at hlen; simp at hlen
      | cons b t' =>
          cases t' with
          | nil =>
              rw [hs] at hhead hlast hok
              simp at hhead hlast
              subst hs
              refine ⟨by simp [hhead, hlast], ?_⟩
              rw [← hhead, ← hlast]
              exact chainSeq_pair S hok
          | cons d t'' => rw [hs] at hlen; simp at hlen

/-- A `2`-chain has shape `[u, m, v]` (main.tex line 63). -/
theorem Chain.two_shape {u v : Obj P B} (c : S.Chain 2 u v) :
    ∃ m : Obj P B, S.ObjInc u m ∧ S.ObjInc m v ∧ c.seq = [u, m, v] := by
  obtain ⟨seq, hlen, hhead, hlast, hok⟩ := c
  show ∃ m : Obj P B, S.ObjInc u m ∧ S.ObjInc m v ∧ seq = [u, m, v]
  cases hs : seq with
  | nil => rw [hs] at hlen; simp at hlen
  | cons a t =>
      cases t with
      | nil => rw [hs] at hlen; simp at hlen
      | cons b t' =>
          cases t' with
          | nil => rw [hs] at hlen; simp at hlen
          | cons d t'' =>
              cases t'' with
              | nil =>
                  rw [hs] at hhead hlast hok
                  simp at hhead hlast
                  obtain ⟨h₁, h₂⟩ := chainSeq_triple S hok
                  refine ⟨b, ?_, ?_, ?_⟩
                  · rwa [← hhead]
                  · rwa [← hlast]
                  · simp [hhead, hlast]
              | cons e t3 => rw [hs] at hlen; simp at hlen

/-- A `3`-chain has shape `[u, m₁, m₂, v]` (main.tex line 63). -/
theorem Chain.three_shape {u v : Obj P B} (c : S.Chain 3 u v) :
    ∃ m₁ m₂ : Obj P B, S.ObjInc u m₁ ∧ S.ObjInc m₁ m₂ ∧ S.ObjInc m₂ v ∧
      c.seq = [u, m₁, m₂, v] := by
  obtain ⟨seq, hlen, hhead, hlast, hok⟩ := c
  show ∃ m₁ m₂ : Obj P B, S.ObjInc u m₁ ∧ S.ObjInc m₁ m₂ ∧ S.ObjInc m₂ v ∧
      seq = [u, m₁, m₂, v]
  cases hs : seq with
  | nil => rw [hs] at hlen; simp at hlen
  | cons a t =>
      cases t with
      | nil => rw [hs] at hlen; simp at hlen
      | cons b t' =>
          cases t' with
          | nil => rw [hs] at hlen; simp at hlen
          | cons d t'' =>
              cases t'' with
              | nil => rw [hs] at hlen; simp at hlen
              | cons e t3 =>
                  cases t3 with
                  | nil =>
                      rw [hs] at hhead hlast hok
                      simp at hhead hlast
                      obtain ⟨h₁, h₂, h₃⟩ := chainSeq_quad S hok
                      refine ⟨b, d, ?_, h₂, ?_, ?_⟩
                      · rwa [← hhead]
                      · rwa [← hlast]
                      · simp [hhead, hlast]
                  | cons f t4 => rw [hs] at hlen; simp at hlen

/-- Parity fact for `2`-chains (main.tex line 63: even distance joins same
sorts). -/
theorem Chain.two_tag_eq {u v : Obj P B} (c : S.Chain 2 u v) : u.tag = v.tag := by
  obtain ⟨m, h₁, h₂, _⟩ := c.two_shape
  have n₁ := objInc_tag_ne S h₁
  have n₂ := objInc_tag_ne S h₂
  cases hu : u.tag <;> cases hm : m.tag <;> cases hv : v.tag <;> simp_all

/-- Parity fact for `3`-chains (main.tex line 63: odd distance joins opposite
sorts). -/
theorem Chain.three_tag_ne {u v : Obj P B} (c : S.Chain 3 u v) : u.tag ≠ v.tag := by
  obtain ⟨m₁, m₂, h₁, h₂, h₃, _⟩ := c.three_shape
  have n₁ := objInc_tag_ne S h₁
  have n₂ := objInc_tag_ne S h₂
  have n₃ := objInc_tag_ne S h₃
  intro heq
  rw [← heq] at n₃
  cases hu : u.tag <;> cases hw : m₁.tag <;> cases hx : m₂.tag <;> simp_all

/-- No `0`-chain between distinct objects (main.tex line 63: `d(u,u) = 0`). -/
theorem isEmpty_chain_zero_of_ne {u v : Obj P B} (hne : u ≠ v) :
    IsEmpty (S.Chain 0 u v) :=
  ⟨fun c => hne c.zero_seq.2⟩

/-- A `1`-chain joins opposite sorts (main.tex line 63). -/
theorem isEmpty_chain_one_of_tag_eq {u v : Obj P B} (heq : u.tag = v.tag) :
    IsEmpty (S.Chain 1 u v) :=
  ⟨fun c => by
    have h := objInc_tag_ne S c.one_seq.2
    rw [heq] at h
    exact h rfl⟩

/-- A `2`-chain joins same sorts (main.tex line 63). -/
theorem isEmpty_chain_two_of_tag_ne {u v : Obj P B} (hne : u.tag ≠ v.tag) :
    IsEmpty (S.Chain 2 u v) :=
  ⟨fun c => hne c.two_tag_eq⟩

/-- A `3`-chain joins opposite sorts (main.tex line 63). -/
theorem isEmpty_chain_three_of_tag_eq {u v : Obj P B} (heq : u.tag = v.tag) :
    IsEmpty (S.Chain 3 u v) :=
  ⟨fun c => by
    have h := c.three_tag_ne
    rw [heq] at h
    exact h rfl⟩

/-- `d(u,v) ≤ n` (main.tex line 67): some chain of length at most `n`. -/
def DistLe (S : IncidenceStruct P B) (n : ℕ) (u v : Obj P B) : Prop :=
  ∃ k, k ≤ n ∧ Nonempty (S.Chain k u v)

/-- `d(u,v) = k` (main.tex line 63): a `k`-chain exists and no shorter one
does. -/
def HasDist (S : IncidenceStruct P B) (k : ℕ) (u v : Obj P B) : Prop :=
  Nonempty (S.Chain k u v) ∧ ∀ j, j < k → IsEmpty (S.Chain j u v)

/-- Generalized `n`-gon axioms (main.tex lines 65–69): diameter at most `n`,
and shortest chains shorter than `n` are unique. -/
structure IsGenNGon (S : IncidenceStruct P B) (n : ℕ) : Prop where
  /-- Axiom 1 (main.tex line 67). -/
  dist_le (u v : Obj P B) : S.DistLe n u v
  /-- Axiom 2 (main.tex line 68): when `d(u,v) = k < n` there is a unique
  `k`-chain from `u` to `v`. -/
  unique_short (u v : Obj P B) (k : ℕ) (hk : k < n)
    (hmin : ∀ j, j < k → IsEmpty (S.Chain j u v))
    (c₁ c₂ : S.Chain k u v) : c₁.seq = c₂.seq

/-- Ovoid (main.tex line 75): a set of points meeting every line in exactly
one point. -/
def IsOvoidOf {Pt Ln : Type _} (S : IncidenceStruct Pt Ln) (O : Set Pt) : Prop :=
  ∀ z : Ln, ∃! p : Pt, p ∈ O ∧ S.Incident p z

/-- Incidence structure isomorphism: a pair of bijections preserving
incidence (main.tex line 61). -/
structure IncidenceIso {P B P' B' : Type _}
    (S : IncidenceStruct P B) (S' : IncidenceStruct P' B') where
  /-- Bijection on points. -/
  ptMap : P ≃ P'
  /-- Bijection on lines. -/
  lnMap : B ≃ B'
  /-- Incidence preservation (main.tex line 61). -/
  incident_iff (p : P) (b : B) :
    S.Incident p b ↔ S'.Incident (ptMap p) (lnMap b)

end IncidenceStruct

/-! ## Generic chain utilities (main.tex line 63) -/

namespace IncidenceStruct

section ChainUtils

variable {P B : Type _} (S : IncidenceStruct P B)

/-- Appending one incident step at the end of a chain body. -/
theorem chainSeq_append_single : ∀ {l : List (Obj P B)} {v x : Obj P B},
    S.ChainSeq l → l.getLast? = some v → S.ObjInc v x → S.ChainSeq (l ++ [x]) := by
  intro l v x cs
  induction cs with
  | nil => intro hget _; exact absurd hget (by simp)
  | single u =>
      intro hget hinc
      have hv : u = v := by simpa using hget
      subst hv
      exact ChainSeq.cons hinc (ChainSeq.single x)
  | cons h₀ _ ih =>
      intro hget hinc
      exact ChainSeq.cons h₀ (ih hget hinc)

/-- Reversal of a chain body, together with the fact that the reversed body
ends where the original began. -/
theorem chainSeq_reverse : ∀ {l : List (Obj P B)}, S.ChainSeq l →
    S.ChainSeq l.reverse ∧ l.reverse.getLast? = l.head? := by
  intro l cs
  induction cs with
  | nil => exact ⟨ChainSeq.nil, rfl⟩
  | single u => exact ⟨ChainSeq.single u, rfl⟩
  | @cons a b t h₀ _ ih =>
      obtain ⟨hr, hl⟩ := ih
      rw [List.reverse_cons]
      refine ⟨?_, ?_⟩
      · exact chainSeq_append_single S hr hl (objInc_symm S h₀)
      · rw [List.getLast?_append]
        simp

/-- Reversal of a chain. -/
def Chain.rev {k : ℕ} {u v : Obj P B} (c : S.Chain k u v) :
    S.Chain k v u := by
  obtain ⟨seq, hlen, hhead, hlast, hok⟩ := c
  refine ⟨seq.reverse, by simp [hlen], by rw [List.head?_reverse]; exact hlast,
    by rw [List.getLast?_reverse]; exact hhead,
    (chainSeq_reverse S hok).1⟩

/-- Extending a chain by one incident step at its end. -/
def Chain.snoc1 {k : ℕ} {u v w : Obj P B} (c : S.Chain k u v)
    (h : S.ObjInc v w) : S.Chain (k + 1) u w :=
  Chain.rev S (Chain.step1 S (objInc_symm S h) c.rev)

/-- Symmetry of the distance bound. -/
theorem DistLe.symm {n : ℕ} {u v : Obj P B} (h : S.DistLe n u v) :
    S.DistLe n v u := by
  obtain ⟨k, hk, c⟩ := h
  obtain ⟨c⟩ := c
  exact ⟨k, hk, ⟨Chain.rev S c⟩⟩

/-- Weakening of the distance bound. -/
theorem DistLe.weaken {n m : ℕ} (hnm : n ≤ m) {u v : Obj P B}
    (h : S.DistLe n u v) : S.DistLe m u v := by
  obtain ⟨k, hk, c⟩ := h
  exact ⟨k, le_trans hk hnm, c⟩

/-- Extending a bounded-distance witness by one incident step at the end. -/
theorem DistLe.snoc {n : ℕ} {u v w : Obj P B} (h : S.DistLe n u v)
    (hinc : S.ObjInc v w) : S.DistLe (n + 1) u w := by
  obtain ⟨k, hk, c⟩ := h
  obtain ⟨c⟩ := c
  exact ⟨k + 1, by omega, ⟨Chain.snoc1 S c hinc⟩⟩

end ChainUtils

end IncidenceStruct

/-! ## Gain functions and switching (main.tex lines 42–59) -/

variable {G Λ : Type _}

/-- Switching function `f : V → G` on the vertices `V = 𝒫 ⊔ ℬ`
(main.tex lines 56–57). -/
structure SwitchingFn (P B G : Type _) [Group G] where
  /-- Value at a point. -/
  pt : P → G
  /-- Value at a line. -/
  ln : B → G

/-- Switched gain function `{}^fφ(e) = f(v) φ(e) f(u)⁻¹` for the edge `e = uv`
oriented from the line `u` to the point `v` (main.tex lines 56–57), i.e.
`{}^fφ(bp) = f(p) φ(bp) f(b)⁻¹`. The gain function itself is represented by
its edge values `B → P → G` in the line-to-point orientation (main.tex
lines 42–46). -/
def switchFn [Group G] (f : SwitchingFn P B G) (φ : B → P → G) :
    B → P → G :=
  fun b p => f.pt p * φ b p * (f.ln b)⁻¹

/-! ## Construction 𝔐 (main.tex lines 89–99) -/

/-- Points of `𝔐(Γ,φ)`: the `x_p` and the `y_{b,λ}` (main.tex line 93). -/
inductive MPoint (P B Λ : Type _)
  | /-- `x_p`. -/ x : P → MPoint P B Λ
  | /-- `y_{b,λ}`. -/ y : B → Λ → MPoint P B Λ

/-- Lines of `𝔐(Γ,φ)`: the `z_{p,μ}` (main.tex line 94). -/
inductive MLine (P Λ : Type _)
  | /-- `z_{p,μ}`. -/ z : P → Λ → MLine P Λ

/-- Incidence `I'` of Construction 𝔐 (main.tex line 95): `x_p I' z_{p,μ}` for
all `μ`, and `y_{b,λ} I' z_{p,μ}` when `b I p` and `μ = φ(bp)·λ`. -/
inductive MI (S : IncidenceStruct P B) (φ : B → P → G) [Group G] {Λ : Type _}
    [MulAction G Λ] : MPoint P B Λ → MLine P Λ → Prop
  | /-- `x_p I' z_{p,μ}` for all `μ` (main.tex line 95). -/ xz (p : P) (mu : Λ) :
      MI S φ (MPoint.x p) (MLine.z p mu)
  | /-- `y_{b,λ} I' z_{p,μ}` when `b I p` and `μ = φ(bp)·λ`
  (main.tex line 95). -/
    yz {b : B} {p : P} {la mu : Λ} (h : S.Incident p b) (heq : mu = φ b p • la) :
      MI S φ (MPoint.y b la) (MLine.z p mu)

section MiIff

variable (S : IncidenceStruct P B) (φ : B → P → G) [Group G] {Λ : Type _}
  [MulAction G Λ]

theorem mi_x_iff (p q : P) (mu : Λ) :
    MI S φ (MPoint.x p) (MLine.z q mu) ↔ p = q := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .xz p mu

theorem mi_y_iff (b : B) (la : Λ) (q : P) (mu : Λ) :
    MI S φ (MPoint.y b la) (MLine.z q mu) ↔ S.Incident q b ∧ mu = φ b q • la := by
  constructor
  · intro h
    cases h with
    | yz hinc heq => exact ⟨hinc, heq⟩
  · rintro ⟨hinc, heq⟩
    exact .yz hinc heq

end MiIff

/-- Construction 𝔐: the incidence structure `(𝒫', ℬ', I')` built from an
incidence gain graph with gain group acting on `Λ`
(main.tex lines 89–99). -/
def constructionM (S : IncidenceStruct P B) (φ : B → P → G) [Group G] {Λ : Type _}
    [MulAction G Λ] : IncidenceStruct (MPoint P B Λ) (MLine P Λ) where
  Incident := MI S φ

/-! ## Rho functions (main.tex lines 138–151) -/

section Rho

variable (S : IncidenceStruct P B)

/-- The unique line through two distinct points of a linear space
(main.tex line 144: `b'` the unique line incident with `p` and `q`). -/
noncomputable def connLine (hls : S.IsLinearSpace) {p q : P} (hne : p ≠ q) : B :=
  Classical.choose (hls.existsUnique_line p q hne)

theorem connLine_left (hls : S.IsLinearSpace) {p q : P} (hne : p ≠ q) :
    S.Incident p (connLine S hls hne) :=
  (Classical.choose_spec (hls.existsUnique_line p q hne)).1.1

theorem connLine_right (hls : S.IsLinearSpace) {p q : P} (hne : p ≠ q) :
    S.Incident q (connLine S hls hne) :=
  (Classical.choose_spec (hls.existsUnique_line p q hne)).1.2

theorem connLine_unique (hls : S.IsLinearSpace) {p q : P} (hne : p ≠ q)
    {b : B} (h₁ : S.Incident p b) (h₂ : S.Incident q b) :
    b = connLine S hls hne :=
  (Classical.choose_spec (hls.existsUnique_line p q hne)).2 b ⟨h₁, h₂⟩

variable [Group G]

/-- `ρ_{b,p}(q) = φ_w` along the walk `w = (b,e₁,q,e₂,b',e₃,p)`, where `b'` is
the unique line through `p` and `q` (main.tex lines 138–151); gains multiply
backwards (main.tex line 54), giving
`ρ_{b,p}(q) = φ(b'p) · φ(b'q)⁻¹ · φ(bq)`. -/
noncomputable def rhoVal (hls : S.IsLinearSpace) (φ : B → P → G)
    (b : B) (p : P) (hp : ¬ S.Incident p b) (q : P) (hq : S.Incident q b) : G :=
  (φ (connLine S hls (fun he : p = q => hp (he.symm ▸ hq))) p *
    (φ (connLine S hls (fun he : p = q => hp (he.symm ▸ hq))) q)⁻¹) * φ b q

/-- `ρ_{b,p,λ}(q) = ρ_{b,p}(q) · λ` (main.tex lines 146–150). -/
noncomputable def rhoLam [MulAction G Λ] (hls : S.IsLinearSpace) (φ : B → P → G)
    (b : B) (p : P) (hp : ¬ S.Incident p b) (mu : Λ)
    (q : {q : P // S.Incident q b}) : Λ :=
  rhoVal S hls φ b p hp q.1 q.2 • mu

end Rho

end McCulloch25_1
