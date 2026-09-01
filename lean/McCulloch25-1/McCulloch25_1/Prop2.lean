import McCulloch25_1.Basic

/-!
# Proposition 2: lifting base chains into 𝔐 with walk gains

McCulloch25-1, Proposition 2, whose proof the paper omits ("follows easily
from Construction 𝔐", main.tex line 128).
Source: `/home/chz/src/gamskil/docs/arxiv/2502.01805/main.tex`
lines 130–134 (statement), lines 52–54 (walks and $\varphi_w$), and
lines 89–99 (Construction 𝔐).

Contents: the lift of a base object with a parameter (`liftObj`: base
lines $b$ lift to 𝔐-points $y_{b,\lambda}$, base points $p$ to 𝔐-lines
$z_{p,\lambda}$), the per-step gain `stepGain` ($\delta_i = 1$ for a
line-to-point step, $\delta_i = -1$ for point-to-line, matching the stored
line-to-point orientation of edge values, main.tex lines 42–46), the
backwards walk gain `walkGain` (main.tex line 54: last edge leftmost), the
parameter update `stepParam`, and two lifted sequences — `liftSeq`
(canonical parameters from one initial value) and `liftZip` (independent
per-position parameters). Theorems:

* `prop2_lift` — a base chain lifts to an 𝔐-chain (the "only if" half,
  constructing the $m_i$);
* `prop2_base` — an 𝔐-chain among lifts forces the base sequence to be a
  chain (the "if" half);
* `prop2_gain` — the furthermore clause: along such chains
  $\lambda_k = \varphi_w \cdot \lambda_0$.

Formalization delta: parameters are indexed by chain position (a list of
$\lambda_i$, bundled in `liftZip`), since a base object may repeat along a
chain; the edges $e_i = u_{i-1}u_i$ are not reified because with edge values
stored line-to-point, $\varphi(e_i)^{\delta_i}$ is literally
`stepGain φ u_{i-1} u_i`.
-/

namespace McCulloch25_1

open IncidenceStruct

/-- Lift of a base object with parameter $\lambda$ (main.tex lines 130–134):
a base line $b$ lifts to the 𝔐-point $y_{b,\lambda}$, a base point $p$ to
the 𝔐-line $z_{p,\lambda}$. -/
def liftObj {P B Λ : Type _} :
    Obj P B → Λ → Obj (MPoint P B Λ) (MLine P Λ)
  | .ln b, la => .pt (MPoint.y b la)
  | .pt p, la => .ln (MLine.z p la)

/-- Gain of one chain step (main.tex lines 52–54): a line-to-point step is a
forward edge ($\delta = 1$), a point-to-line step a backward edge
($\delta = -1$); the junk cases never occur along a chain. -/
def stepGain {P B G : Type _} [Group G] (φ : B → P → G) :
    Obj P B → Obj P B → G
  | .ln b, .pt p => φ b p
  | .pt p, .ln b => (φ b p)⁻¹
  | _, _ => 1

/-- Walk gain $\varphi_w$, multiplied backwards so the last edge stands
leftmost (main.tex line 54). -/
def walkGain {P B G : Type _} [Group G] (φ : B → P → G) :
    List (Obj P B) → G
  | [] => 1
  | [_] => 1
  | u :: v :: t => walkGain φ (v :: t) * stepGain φ u v

/-- Parameter update across one step: $\lambda_i =
\varphi(e_i)^{\delta_i}\cdot\lambda_{i-1}$ (main.tex lines 132–134). -/
def stepParam {P B G Λ : Type _} [Group G] [MulAction G Λ]
    (φ : B → P → G) : Obj P B → Obj P B → Λ → Λ
  | .ln b, .pt p, la => φ b p • la
  | .pt p, .ln b, la => (φ b p)⁻¹ • la
  | _, _, la => la

/-- Parameter handed to the tail of a sequence: advanced across the next
step when one exists. -/
def tailParam {P B G Λ : Type _} [Group G] [MulAction G Λ]
    (φ : B → P → G) : Obj P B → List (Obj P B) → Λ → Λ
  | u, v :: _, la => stepParam φ u v la
  | _, _, la => la

/-- Lift of a whole sequence with canonical running parameters, starting
from the given value. -/
def liftSeq {P B G Λ : Type _} [Group G] [MulAction G Λ] (φ : B → P → G) :
    List (Obj P B) → Λ → List (Obj (MPoint P B Λ) (MLine P Λ))
  | [], _ => []
  | u :: l, la => liftObj u la :: liftSeq φ l (tailParam φ u l la)

/-- Lift of a sequence with an independent parameter at each position
(main.tex lines 130–134: $m_i = y_{u_i,\lambda_i}$ resp.
$m_i = z_{u_i,\lambda_i}$). Truncates on length mismatch. -/
def liftZip {P B G Λ : Type _} [Group G] [MulAction G Λ] (φ : B → P → G) :
    List (Obj P B) → List Λ → List (Obj (MPoint P B Λ) (MLine P Λ))
  | u :: l, la :: las => liftObj u la :: liftZip φ l las
  | _, _ => []

variable {P B G Λ : Type _} [Group G] [MulAction G Λ]

/-- The action of a step gain computes the parameter update. -/
theorem stepGain_smul (φ : B → P → G) (u v : Obj P B) (la : Λ) :
    stepGain φ u v • la = stepParam φ u v la := by
  cases u <;> cases v <;> simp [stepGain, stepParam]

/-- One lifted step is incident in 𝔐 exactly when its base objects are
(main.tex line 95). -/
theorem liftObj_objInc (S : IncidenceStruct P B) (φ : B → P → G)
    {u v : Obj P B} (h : S.ObjInc u v) (la : Λ) :
    (constructionM S φ).ObjInc (liftObj u la)
      (liftObj v (stepParam φ u v la)) := by
  cases u with
  | ln b =>
      cases v with
      | pt p => exact MI.yz h rfl
      | ln c => cases h
  | pt p =>
      cases v with
      | ln b =>
          exact (mi_y_iff S φ b _ p la).mpr
            ⟨h, (smul_inv_smul (φ b p) la).symm⟩
      | pt q => cases h

/-- Incidence between lifts forces incidence between the base objects. -/
theorem objInc_of_liftObj_objInc (S : IncidenceStruct P B) (φ : B → P → G)
    {u v : Obj P B} {la lv : Λ}
    (h : (constructionM S φ).ObjInc (liftObj u la) (liftObj v lv)) :
    S.ObjInc u v := by
  cases u with
  | ln b =>
      cases v with
      | pt p => exact ((mi_y_iff S φ b la p lv).mp h).1
      | ln c => exact h
  | pt p =>
      cases v with
      | ln b => exact ((mi_y_iff S φ b lv p la).mp h).1
      | pt q => exact h

/-- The second parameter of an incident pair of lifts is the first one
updated by the step gain. -/
theorem stepParam_eq (S : IncidenceStruct P B) (φ : B → P → G)
    {u v : Obj P B} {la lb : Λ}
    (h : (constructionM S φ).ObjInc (liftObj u la) (liftObj v lb)) :
    lb = stepParam φ u v la := by
  cases u with
  | ln b =>
      cases v with
      | pt p => exact ((mi_y_iff S φ b la p lb).mp h).2
      | ln c => exact h.elim
  | pt p =>
      cases v with
      | ln b =>
          exact (inv_smul_eq_iff.mpr ((mi_y_iff S φ b lb p la).mp h).2).symm
      | pt q => exact h.elim

/-- **Proposition 2, construction half** (main.tex lines 130–134): every base
chain lifts to an 𝔐-chain whose parameters run through `stepParam`. -/
theorem prop2_lift (S : IncidenceStruct P B) (φ : B → P → G)
    {l : List (Obj P B)} (hcs : S.ChainSeq l) (la : Λ) :
    (constructionM S φ).ChainSeq (liftSeq φ l la) := by
  induction hcs generalizing la with
  | nil => exact .nil
  | single u => exact .single (liftObj u la)
  | @cons u v t h _ ih =>
      refine ChainSeq.cons (liftObj_objInc S φ h la) ?_
      exact ih (tailParam φ u (v :: t) la)

private theorem prop2_base_aux (S : IncidenceStruct P B) (φ : B → P → G) :
    ∀ (l : List (Obj P B)) (las : List Λ),
      las.length = l.length →
      (constructionM S φ).ChainSeq (liftZip φ l las) → S.ChainSeq l := by
  intro l
  induction l with
  | nil =>
      intro las hlen _
      cases las with
      | nil => exact .nil
      | cons _ _ => simp at hlen
  | cons u l₂ ih =>
      intro las hlen hmc
      cases las with
      | nil => simp at hlen
      | cons la las₂ =>
          have hl2 : las₂.length = l₂.length := by simpa using hlen
          cases l₂ with
          | nil =>
              cases las₂ with
              | nil => exact ChainSeq.single u
              | cons _ _ => simp at hl2
          | cons v t =>
              cases las₂ with
              | nil => simp at hl2
              | cons lb las₃ =>
                  have hl3 : (lb :: las₃).length = (v :: t).length := hl2
                  cases hmc with
                  | cons hpair htail =>
                      refine ChainSeq.cons
                        (objInc_of_liftObj_objInc S φ hpair) ?_
                      exact ih (lb :: las₃) hl3 htail

/-- **Proposition 2, converse half** (main.tex lines 130–134): if the
parameter-wise lifts of a sequence form an 𝔐-chain, the base sequence is a
chain. -/
theorem prop2_base (S : IncidenceStruct P B) (φ : B → P → G)
    {l : List (Obj P B)} {las : List Λ}
    (hlen : las.length = l.length)
    (hmc : (constructionM S φ).ChainSeq (liftZip φ l las)) :
    S.ChainSeq l :=
  prop2_base_aux S φ l las hlen hmc

private theorem prop2_gain_aux (S : IncidenceStruct P B) (φ : B → P → G) :
    ∀ (l : List (Obj P B)) (las : List Λ),
      las.length = l.length →
      (constructionM S φ).ChainSeq (liftZip φ l las) →
      ∀ la₀ : Λ, las.head? = some la₀ →
        las.getLast? = some (walkGain φ l • la₀) := by
  intro l
  induction l with
  | nil =>
      intro las hlen _ la₀ hh
      cases las with
      | nil => exact absurd hh (by simp)
      | cons _ _ => simp at hlen
  | cons u l₂ ih =>
      intro las hlen hmc la₀ hh
      cases las with
      | nil => simp at hlen
      | cons la las₂ =>
          have h0 : la = la₀ := by simpa using hh
          subst h0
          have hl2 : las₂.length = l₂.length := by simpa using hlen
          cases l₂ with
          | nil =>
              cases las₂ with
              | nil => simp [walkGain, one_smul]
              | cons _ _ => simp at hl2
          | cons v t =>
              cases las₂ with
              | nil => simp at hl2
              | cons lb las₃ =>
                  have hl3 : (lb :: las₃).length = (v :: t).length := hl2
                  cases hmc with
                  | cons hpair htail =>
                      have hstep := stepParam_eq S φ hpair
                      have hw : walkGain φ (u :: v :: t) • la
                          = walkGain φ (v :: t) • stepParam φ u v la := by
                        simp only [walkGain]
                        rw [mul_smul, stepGain_smul]
                      rw [List.getLast?_cons_cons, hw, ← hstep]
                      exact ih (lb :: las₃) hl3 htail lb rfl

/-- **Proposition 2, furthermore clause** (main.tex lines 132–134): along a
lifted 𝔐-chain the last parameter is the walk gain applied to the first:
$\lambda_k = \varphi_w \cdot \lambda_0$. -/
theorem prop2_gain (S : IncidenceStruct P B) (φ : B → P → G)
    {l : List (Obj P B)} {las : List Λ}
    (hlen : las.length = l.length)
    (hmc : (constructionM S φ).ChainSeq (liftZip φ l las))
    {la₀ : Λ} (hhead : las.head? = some la₀) :
    las.getLast? = some (walkGain φ l • la₀) :=
  prop2_gain_aux S φ l las hlen hmc la₀ hhead

end McCulloch25_1
