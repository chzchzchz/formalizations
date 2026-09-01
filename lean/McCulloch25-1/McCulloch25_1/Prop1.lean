import McCulloch25_1.Basic

/-!
# Proposition 1: switching induces an isomorphism of 𝔐

McCulloch25-1, Proposition 1.
Source: `/home/chz/src/gamskil/docs/arxiv/2502.01805/main.tex`
lines 103-126 (statement at 103-112, proof at 114-126).
-/

namespace McCulloch25_1

open IncidenceStruct

variable {P B G Λ : Type _} [Group G] [MulAction G Λ]

/-- The point-map $g_1$ of Proposition 1 (main.tex line 107): fixes every
$x_p$ and sends $y_{b,\lambda}\mapsto y_{b,f(b)\cdot\lambda}$; its inverse
applies $f(b)^{-1}$. -/
def switchPtMap (f : SwitchingFn P B G) : MPoint P B Λ ≃ MPoint P B Λ where
  toFun := fun
    | .x p => .x p
    | .y b la => .y b (f.ln b • la)
  invFun := fun
    | .x p => .x p
    | .y b la => .y b ((f.ln b)⁻¹ • la)
  left_inv := by
    intro mp
    cases mp with
    | x => rfl
    | y b la => simp
  right_inv := by
    intro mp
    cases mp with
    | x => rfl
    | y b la => simp

/-- The line-map $g_2$ of Proposition 1 (main.tex line 108):
$z_{p,\mu}\mapsto z_{p,f(p)\cdot\mu}$. -/
def switchLnMap (f : SwitchingFn P B G) : MLine P Λ ≃ MLine P Λ where
  toFun := fun
    | .z p mu => .z p (f.pt p • mu)
  invFun := fun
    | .z p mu => .z p ((f.pt p)⁻¹ • mu)
  left_inv := by
    intro ml
    cases ml with
    | z => simp
  right_inv := by
    intro ml
    cases ml with
    | z => simp

/-- The cancellation driving Proposition 1's incidence check (the step from
main.tex line 121 to line 123):
$(f(p)\varphi(e)f(b)^{-1})\cdot(f(b)\cdot\nu) = (f(p)\varphi(e))\cdot\nu$. -/
theorem switch_key (f : SwitchingFn P B G) (φ : B → P → G) (b : B) (q : P)
    (nu : Λ) :
    switchFn f φ b q • (f.ln b • nu) = (f.pt q * φ b q) • nu := by
  show (f.pt q * φ b q * (f.ln b)⁻¹) • (f.ln b • nu) = _
  rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one]

/-- Proposition 1's incidence clause for $x_p$ against $z_{q,\mu}$
(main.tex lines 116 and 123: both sides say $p = q$). -/
theorem switchIso_xz (S : IncidenceStruct P B) (φ : B → P → G)
    (f : SwitchingFn P B G) (p q : P) (nu : Λ) :
    MI S φ (MPoint.x p) (MLine.z q nu) ↔
      MI S (switchFn f φ) ((switchPtMap f) (MPoint.x p))
        ((switchLnMap f) (MLine.z q nu)) := by
  -- `switchPtMap f (x p)` and `switchLnMap f (z q nu)` reduce to `x p` and
  -- `z q (f.pt q • nu)` by iota-reduction on the `toFun` matches.
  show MI S φ (MPoint.x p) (MLine.z q nu) ↔
    MI S (switchFn f φ) (MPoint.x p) (MLine.z q (f.pt q • nu))
  constructor
  · intro h
    cases h
    exact .xz _ _
  · intro h
    cases h
    exact .xz _ _

/-- Proposition 1's incidence clause for $y_{b,\lambda}$ against $z_{q,\mu}$
(main.tex lines 115-125): under the maps,
$f(p)\cdot\mu = {}^f\!\varphi(bp)\cdot(f(b)\cdot\lambda)$ unfolds to
$\mu = \varphi(bp)\cdot\lambda$. -/
theorem switchIso_yz (S : IncidenceStruct P B) (φ : B → P → G)
    (f : SwitchingFn P B G) (b : B) (la : Λ) (q : P) (nu : Λ) :
    MI S φ (MPoint.y b la) (MLine.z q nu) ↔
      MI S (switchFn f φ) ((switchPtMap f) (MPoint.y b la))
        ((switchLnMap f) (MLine.z q nu)) := by
  show MI S φ (MPoint.y b la) (MLine.z q nu) ↔
    MI S (switchFn f φ) (MPoint.y b (f.ln b • la)) (MLine.z q (f.pt q • nu))
  rw [mi_y_iff S φ b la q nu,
    mi_y_iff S (switchFn f φ) b (f.ln b • la) q (f.pt q • nu)]
  constructor
  · -- main.tex lines 118-121: $\mu=\varphi(bp)\cdot\lambda$ implies
    -- $f(p)\cdot\mu = ({}^f\!\varphi)(bp)\cdot(f(b)\cdot\lambda)$
    rintro ⟨hinc, heq⟩
    refine ⟨hinc, ?_⟩
    rw [heq, ← mul_smul, ← switch_key f φ b q la]
  · -- main.tex lines 121-123: cancel the bijection $f(p)\cdot(-)$
    rintro ⟨hinc, heq⟩
    rw [switch_key f φ b q la] at heq
    have hc := congrArg (fun ν : Λ => (f.pt q)⁻¹ • ν) heq
    exact ⟨hinc, by simpa [smul_smul, inv_mul_cancel_left] using hc⟩

/-- Proposition 1 (`prop_switching`): switching by $f$ induces an incidence
structure isomorphism $\mathfrak{M}(\Gamma,\varphi)\cong
\mathfrak{M}(\Gamma,{}^f\varphi)$ (main.tex lines 103-112). -/
def switchIso (S : IncidenceStruct P B) (φ : B → P → G) (f : SwitchingFn P B G) :
    IncidenceIso (constructionM (Λ := Λ) S φ)
      (constructionM (Λ := Λ) S (switchFn f φ)) where
  ptMap := switchPtMap f
  lnMap := switchLnMap f
  incident_iff := by
    intro mp ml
    cases mp with
    | x p =>
        cases ml with
        | z q nu => exact switchIso_xz S φ f p q nu
    | y b la =>
        cases ml with
        | z q nu => exact switchIso_yz S φ f b la q nu

end McCulloch25_1
