import McCulloch25_1.Thm5

/-!
# Theorem 7: the affine-plane gain graph yields a generalized quadrangle

McCulloch25-1, Theorem 7.
Source: `/home/chz/src/gamskil/docs/arxiv/2502.01805/main.tex`
lines 264–274 (statement), 276–379 (proof).

Encoding:
- points `F × F`, lines `AffineLn F` (`vert b` = $L_b$, `slope m b` =
  $L_{m,b}$), incidence per main.tex line 262;
- gain group `Multiplicative F` acting on `F` by translation
  (mathlib's `Multiplicative.mulAction` over the regular self-action of
  $(\mathbb{F},+)$, main.tex line 265), so $\rho$-values live in
  `Multiplicative F`;
- gain function `affPhi` per main.tex lines 267–271, values off incidence
  junk (project-wide delta recorded in `Basic.lean`).

Route delta vs. the printed proof: the paper computes each injectivity /
surjectivity case through walk gains $w = (L,e_1,p_1,e_2,M_1,e_3,p)$
(main.tex lines 281, 354, 362). Here two master computations package all
cases, because `rhoVal` already packages the connecting line: for $q \in L$
and $p = (x,y)$ not on $L$,

- $L = L_v$ vertical: $\rho(q) = (x - v)\,y_q - v\,y$
  (main.tex lines 287–306, 354–360);
- $L = L_{m,v}$ non-vertical: $\rho(q) = x\,y_q - x_q\,(y - v)$
  (main.tex lines 310–350, 362–377; the vertical/non-vertical connector
  sub-cases of the printed proof collapse into this one formula).

Injectivity and surjectivity are then single field cancellations
(main.tex lines 304–306, 348–350, 354–360, 362–377).
-/

namespace McCulloch25_1

open IncidenceStruct Multiplicative

/-! ## The affine plane over a field (main.tex line 262) -/

/-- Lines of the affine plane over `F` (main.tex line 262): vertical lines
$L_b$ indexed by the $x$-intercept `b`, and non-vertical lines $L_{m,b}$
indexed by the slope `m` and $y$-intercept `b`. -/
inductive AffineLn (F : Type _)
  | /-- The vertical line $L_b$. -/ vert (b : F)
  | /-- The non-vertical line $L_{m,b}$. -/ slope (m b : F)

/-- Incidence of the affine plane (main.tex line 262): $(b,y)\ \mathrm{I}\ L_b$
for all $y$, and $(x, mx+b)\ \mathrm{I}\ L_{m,b}$ for all $x$. -/
def affIncident {F : Type _} [Add F] [Mul F] (p : F × F) : AffineLn F → Prop
  | .vert b => p.1 = b
  | .slope m b => p.2 = m * p.1 + b

/-- The affine plane over `F` as an incidence structure (main.tex
line 262). -/
def affineStruct (F : Type _) [Add F] [Mul F] :
    IncidenceStruct (F × F) (AffineLn F) where
  Incident p l := affIncident p l

section Thm7

variable {F : Type _} [Field F]

omit [Field F] in
/-- Two points of the plane are equal when both coordinates agree
(used to build plane-point equalities). -/
theorem affPt_eq {p q : F × F} (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q := by
  cases p
  cases q
  simp_all

/-- Auxiliary uniqueness computation for non-vertical lines: two slope-lines
through the same two distinct points have equal slope and intercept
(main.tex line 262's uniqueness, used in `aff_existsUnique_line`). -/
theorem aff_existsUnique_line_aux (p q : F × F) (hx : p.1 ≠ q.1)
    {m b m' b' : F}
    (h₁ : affIncident p (AffineLn.slope m b))
    (h₂ : affIncident q (AffineLn.slope m b))
    (h₁' : affIncident p (AffineLn.slope m' b'))
    (h₂' : affIncident q (AffineLn.slope m' b')) :
    AffineLn.slope m' b' = AffineLn.slope m b := by
  simp only [affIncident] at h₁ h₂ h₁' h₂'
  have hz : p.1 - q.1 ≠ 0 := sub_ne_zero.mpr hx
  have e1 : m * (p.1 - q.1) = p.2 - q.2 := by linear_combination h₂ - h₁
  have e2 : m' * (p.1 - q.1) = p.2 - q.2 := by linear_combination h₂' - h₁'
  have hmm : m' = m := mul_right_cancel₀ hz (e2.trans e1.symm)
  have hb : b = p.2 - m * p.1 := by linear_combination -h₁
  have hb' : b' = p.2 - m' * p.1 := by linear_combination -h₁'
  rw [hb', hb, hmm]

/-- Axiom 1 for the affine plane (main.tex lines 77–83, 262): two distinct
points lie on exactly one common line — the vertical $L_{p_1}$ when their
$x$-coordinates agree, otherwise the non-vertical line of slope
$(p_2-q_2)/(p_1-q_1)$. -/
theorem aff_existsUnique_line (p q : F × F) (hne : p ≠ q) :
    ∃! l, affIncident p l ∧ affIncident q l := by
  by_cases hx : p.1 = q.1
  · refine ⟨AffineLn.vert p.1, ⟨rfl, hx.symm⟩, ?_⟩
    rintro l ⟨h₁, h₂⟩
    cases l with
    | vert b => exact (congrArg AffineLn.vert h₁).symm
    | slope m b =>
        exfalso
        refine hne (affPt_eq hx ?_)
        rw [h₁, h₂, hx]
  · have hz : p.1 - q.1 ≠ 0 := sub_ne_zero.mpr hx
    have hpW : affIncident p (AffineLn.slope ((p.2 - q.2) / (p.1 - q.1))
        (p.2 - (p.2 - q.2) / (p.1 - q.1) * p.1)) := by
      simp only [affIncident]
      field_simp [hz]
      ring
    have hqW : affIncident q (AffineLn.slope ((p.2 - q.2) / (p.1 - q.1))
        (p.2 - (p.2 - q.2) / (p.1 - q.1) * p.1)) := by
      simp only [affIncident]
      field_simp [hz]
      ring
    refine ⟨AffineLn.slope ((p.2 - q.2) / (p.1 - q.1))
      (p.2 - (p.2 - q.2) / (p.1 - q.1) * p.1), ⟨hpW, hqW⟩, ?_⟩
    rintro l ⟨h₁, h₂⟩
    cases l with
    | vert b => exact absurd (h₁.trans h₂.symm) hx
    | slope m b =>
        exact (aff_existsUnique_line_aux p q hx h₁ h₂ hpW hqW).symm

/-- Axiom 2 for the affine plane (main.tex lines 77–83, 262): every line
carries at least two points, $(b,0)$ and $(b,1)$ resp. $(0,b)$ and
$(1,m+b)$. -/
theorem aff_two_pts (l : AffineLn F) :
    ∃ p q : F × F, p ≠ q ∧ affIncident p l ∧ affIncident q l := by
  cases l with
  | vert b =>
      refine ⟨(b, 0), (b, 1), fun he => zero_ne_one (congrArg (·.2) he),
        rfl, rfl⟩
  | slope m b =>
      refine ⟨(0, b), (1, m * 1 + b), fun he => zero_ne_one (congrArg (·.1) he),
        by show b = m * 0 + b; ring, rfl⟩

/-- Axiom 3 for the affine plane (main.tex lines 77–83, 262): $(1,0)$ misses
the vertical $L_0$. -/
theorem aff_nonincident :
    ∃ p : F × F, ∃ l : AffineLn F, ¬ affIncident p l :=
  ⟨(1, 0), .vert 0, one_ne_zero⟩
/-- The affine plane over `F` is a linear space (main.tex lines 77–83 with
the affine-plane incidence of line 262). -/
theorem affineStruct_isLinearSpace : (affineStruct F).IsLinearSpace where
  existsUnique_line := aff_existsUnique_line
  two_pts := aff_two_pts
  nonincident := aff_nonincident

/-- The connecting line of two plane-points with equal $x$-coordinate is the
vertical line $L_{p_1}$ (main.tex line 262; uniqueness of the joining line
pins `connLine`). -/
theorem affConnLine_vert (hls : (affineStruct F).IsLinearSpace) {p q : F × F}
    (hne : p ≠ q) (hx : p.1 = q.1) :
    connLine (affineStruct F) hls hne = AffineLn.vert p.1 :=
  (connLine_unique (affineStruct F) hls hne
    (by show (affineStruct F).Incident p (AffineLn.vert p.1); exact rfl)
    (by show (affineStruct F).Incident q (AffineLn.vert p.1); exact hx.symm)).symm

/-- The connecting line of two plane-points with distinct $x$-coordinates is
the non-vertical line of slope $(p_2-q_2)/(p_1-q_1)$ through them
(main.tex line 262; uniqueness of the joining line pins `connLine`;
explicitly the line $M_1$ of main.tex lines 285, 322, 335). -/
theorem affConnLine_slope (hls : (affineStruct F).IsLinearSpace) {p q : F × F}
    (hne : p ≠ q) (hx : p.1 ≠ q.1) :
    connLine (affineStruct F) hls hne =
      AffineLn.slope ((p.2 - q.2) / (p.1 - q.1))
        (p.2 - (p.2 - q.2) / (p.1 - q.1) * p.1) := by
  have hW : connLine (affineStruct F) hls hne =
      AffineLn.slope ((p.2 - q.2) / (p.1 - q.1))
        (p.2 - (p.2 - q.2) / (p.1 - q.1) * p.1) := by
    refine (connLine_unique (affineStruct F) hls hne ?_ ?_).symm <;>
      · show (affineStruct F).Incident _
            (AffineLn.slope ((p.2 - q.2) / (p.1 - q.1))
              (p.2 - (p.2 - q.2) / (p.1 - q.1) * p.1))
        show _ = _ * _ + _
        field_simp [sub_ne_zero.mpr hx]
        ring
  rw [hW]

/-! ## Gain function and the regular translation action

Gain group $G = (\mathbb{F},+)$ written multiplicatively via the
`Multiplicative` type synonym, acting on $\Lambda = \mathbb{F}$ by
translation (main.tex line 265: "let $\mathbb{F}$ act on itself via
addition"; regularity used through Proposition 6, main.tex line 277). -/

/-- Gain function of main.tex lines 267–271: $\varphi(\{L_b,(b,y)\}) = -by$
and $\varphi(\{L_{m,b},(x,mx+b)\}) = xb$; edges oriented line → point;
values off incidence junk (project delta, cf. `Basic.lean`). -/
noncomputable def affPhi : AffineLn F → F × F → Multiplicative F
  | .vert b, p => ofAdd (-(b * p.2))
  | .slope _ b, p => ofAdd (p.1 * b)

/-- The translation action is free ($\mathbb{F}$ acting on itself, main.tex
line 265); freeness input of Proposition 6. -/
theorem aff_free ⦃g : Multiplicative F⦄ ⦃nu : F⦄ (h : g • nu = nu) : g = 1 := by
  have h' : g.toAdd + nu = nu := h
  exact toAdd_eq_zero.mp (add_right_cancel (a := g.toAdd) (b := nu) (c := 0)
    (by rw [zero_add]; exact h'))

/-- The translation action is transitive (main.tex line 265);
transitivity input of Proposition 6. -/
theorem aff_trans (nu₁ nu₂ : F) : ∃ g : Multiplicative F, g • nu₂ = nu₁ :=
  ⟨ofAdd (nu₁ - nu₂), by
    show (nu₁ - nu₂) + nu₂ = nu₁
    exact sub_add_cancel _ _⟩

/-- Push a multiplicative triple of `ofAdd`-values into one additive value
(reads $\varphi(e_3)\varphi(e_2)^{-1}\varphi(e_1)$ as
$\varphi(e_3)-\varphi(e_2)+\varphi(e_1)$; backwards multiplication is
main.tex line 54). -/
theorem ofAdd_push {a b c : F} :
    (ofAdd a) * (ofAdd b)⁻¹ * ofAdd c = ofAdd (a - b + c) := by
  have h : (ofAdd a) * (ofAdd b)⁻¹ * ofAdd c
      = ofAdd (a + -b + c) := by
    rw [← ofAdd_neg, ← ofAdd_add, ← ofAdd_add]
  rw [h]
  group

omit [Field F] in
/-- `ofAdd` respects `toAdd`-equality (used to transport $\rho$-goals into
plain field identities). -/
theorem ext_toAdd {a b : Multiplicative F} (h : a.toAdd = b.toAdd) : a = b :=
  by simpa using congrArg ofAdd h

/-- Coercion of non-incidence with a vertical line (main.tex line 262). -/
theorem not_inc_vert {p : F × F} (v : F)
    (hp : ¬ affIncident p (AffineLn.vert v)) : p.1 ≠ v := fun he => hp he

/-- Coercion of non-incidence with a non-vertical line (main.tex
line 262). -/
theorem not_inc_slope {p : F × F} (m b : F)
    (hp : ¬ affIncident p (AffineLn.slope m b)) : p.2 ≠ m * p.1 + b :=
  fun he => hp he

/-- Algebraic core of the vertical-case computation (main.tex lines
293–299): substituting $b_1 = y_1 - m_1b$ turns $xb_1 - bb_1 - by_1$ into
$(x-b)y_1 - by$. -/
theorem aff_vert_rho_core (v : F) (p q : F × F)
    (hq1 : q.1 = v) (hv : p.1 - v ≠ 0) :
    p.1 * (p.2 - (p.2 - q.2) / (p.1 - q.1) * p.1)
        - q.1 * (p.2 - (p.2 - q.2) / (p.1 - q.1) * p.1)
      + -(v * q.2)
      = (p.1 - v) * q.2 - v * p.2 := by
  rw [show q.1 = v from hq1]
  field_simp
  ring

/-- Algebraic core of the non-vertical-case computation (main.tex lines
327–333): substituting $b_1 = y_1 - m_1x_1$ turns $xb_1 - x_1b_1 + x_1b$
into $xy_1 - x_1y + x_1b$. -/
theorem aff_slope_rho_core (_m b₀ : F) (p q : F × F)
    (hv : p.1 - q.1 ≠ 0) :
    p.1 * (p.2 - (p.2 - q.2) / (p.1 - q.1) * p.1)
        - q.1 * (p.2 - (p.2 - q.2) / (p.1 - q.1) * p.1)
      + q.1 * b₀
      = p.1 * q.2 - q.1 * p.2 + q.1 * b₀ := by
  field_simp
  ring

/-! ## Master ρ-computations

For $p$ off $L$ and $q \in L$, the walk gain $\rho_{L,p}(q)$ collapses to
one formula per line type (route delta documented in the module header). -/

/-- Vertical case: for $p = (x,y)$ off $L_v$ and $q = (v, y_q) \in L_v$,
$\rho_{L,p}(q) = (x-v)\,y_q - v\,y$ (main.tex lines 287–306: the Case 1
computation $xb_1 - bb_1 - by_1 = xy_1 - yb - by_1$). -/
theorem rhoVal_affVert_toAdd (v : F) (p q : F × F)
    (hp : ¬ affIncident p (AffineLn.vert v))
    (hq : affIncident q (AffineLn.vert v)) :
    (rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.vert v) p hp q hq).toAdd
      = (p.1 - v) * q.2 - v * p.2 := by
  have hx : p.1 ≠ v := not_inc_vert v hp
  have hq1 : q.1 = v := hq
  have hne : p ≠ q := by
    intro he
    rw [he] at hp
    exact hp hq
  have hM := affConnLine_slope affineStruct_isLinearSpace hne
    (fun he => hx (he.trans hq1))
  rw [show rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.vert v) p hp q hq =
        affPhi (connLine (affineStruct F) affineStruct_isLinearSpace hne) p *
          (affPhi (connLine (affineStruct F) affineStruct_isLinearSpace hne) q)⁻¹ *
          affPhi (AffineLn.vert v) q
      from rfl, hM]
  simp only [affPhi]
  rw [ofAdd_push, toAdd_ofAdd]
  exact aff_vert_rho_core v p q hq1 (sub_ne_zero.mpr hx)

/-- Non-vertical case: for $p = (x,y)$ off $L_{m,v}$ and $q = (x_q, mx_q+v)
\in L_{m,v}$, $\rho_{L,p}(q) = x\,y_q - x_q\,(y - v)$ (main.tex lines
310–350: both connector sub-cases — $M$ vertical, lines 310–320, and
non-vertical, lines 322–340 — reduce to $xy_1 - x_1y + x_1b$). -/
theorem rhoVal_affSlope_toAdd (m b₀ : F) (p q : F × F)
    (hp : ¬ affIncident p (AffineLn.slope m b₀))
    (hq : affIncident q (AffineLn.slope m b₀)) :
    (rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.slope m b₀) p hp q hq).toAdd
      = p.1 * q.2 - q.1 * p.2 + q.1 * b₀ := by
  have hne : p ≠ q := by
    intro he
    rw [he] at hp
    exact hp hq
  by_cases hxq : q.1 = p.1
  · -- main.tex lines 310–320: the connector $M$ is the vertical $L_x$
    have hM : connLine (affineStruct F) affineStruct_isLinearSpace hne =
        AffineLn.vert p.1 :=
      affConnLine_vert affineStruct_isLinearSpace hne hxq.symm
    rw [show rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
          (AffineLn.slope m b₀) p hp q hq =
          affPhi (connLine (affineStruct F) affineStruct_isLinearSpace hne) p *
            (affPhi (connLine (affineStruct F) affineStruct_isLinearSpace hne) q)⁻¹ *
            affPhi (AffineLn.slope m b₀) q
        from rfl, hM]
    simp only [affPhi]
    rw [ofAdd_push, toAdd_ofAdd, hxq]
    ring
  · -- main.tex lines 322–340: the connector is non-vertical
    have hM := affConnLine_slope affineStruct_isLinearSpace hne
      (fun he => hxq he.symm)
    rw [show rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
          (AffineLn.slope m b₀) p hp q hq =
          affPhi (connLine (affineStruct F) affineStruct_isLinearSpace hne) p *
            (affPhi (connLine (affineStruct F) affineStruct_isLinearSpace hne) q)⁻¹ *
            affPhi (AffineLn.slope m b₀) q
        from rfl, hM]
    simp only [affPhi]
    rw [ofAdd_push, toAdd_ofAdd]
    exact aff_slope_rho_core m b₀ p q (sub_ne_zero.mpr (fun he => hxq he.symm))

/-! ## Injectivity and surjectivity of ρ_{L,p}

(main.tex lines 279 "Proof of the injectivity", 352 "Proof of the
surjectivity".) -/

/-- Injectivity of $\rho_{L,p}$ for vertical $L$ (main.tex lines 283–306):
$\rho(q) = (x-v)y_q - vy$ and $x \neq v$ force $y_q$ to be recoverable. -/
theorem affRho_inj_vert (v : F) (p : F × F)
    (hp : ¬ affIncident p (AffineLn.vert v))
    ⦃q₁ q₂ : {q : F × F // affIncident q (AffineLn.vert v)}⦄
    (he : rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.vert v) p hp q₁.1 q₁.2 =
      rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.vert v) p hp q₂.1 q₂.2) :
    q₁ = q₂ := by
  have he' : (rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.vert v) p hp q₁.1 q₁.2).toAdd =
      (rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.vert v) p hp q₂.1 q₂.2).toAdd :=
    congrArg Multiplicative.toAdd he
  rw [rhoVal_affVert_toAdd v p q₁.1 hp q₁.2,
      rhoVal_affVert_toAdd v p q₂.1 hp q₂.2] at he'
  have h1 : q₁.1.1 = v := q₁.2
  have h2 : q₂.1.1 = v := q₂.2
  have hv : p.1 - v ≠ 0 := sub_ne_zero.mpr (not_inc_vert v hp)
  have hy12 : q₁.1.2 = q₂.1.2 :=
    mul_left_cancel₀ hv (by linear_combination he')
  exact Subtype.ext (affPt_eq (h1.trans h2.symm) hy12)
/-- Surjectivity of $\rho_{L,p}$ for vertical $L$ (main.tex lines 354–360):
given $z$, take $y_1 = (x-b)^{-1}(z+yb)$. -/
theorem affRho_surj_vert (v : F) (p : F × F)
    (hp : ¬ affIncident p (AffineLn.vert v)) (g : Multiplicative F) :
    ∃ q : {q : F × F // affIncident q (AffineLn.vert v)},
      rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.vert v) p hp q.1 q.2 = g := by
  have hY : affIncident (v, (p.1 - v)⁻¹ * (g.toAdd + v * p.2))
      (AffineLn.vert v) := rfl
  have key := rhoVal_affVert_toAdd v p (v, (p.1 - v)⁻¹ * (g.toAdd + v * p.2))
    hp hY
  refine ⟨⟨(v, (p.1 - v)⁻¹ * (g.toAdd + v * p.2)), hY⟩, ?_⟩
  apply ext_toAdd
  rw [key]
  field_simp [sub_ne_zero.mpr (not_inc_vert v hp)]
  ring

/-- Injectivity of $\rho_{L,p}$ for non-vertical $L$ (main.tex lines
308–350): the uniform formula and $y \neq mx+b$, $x_1 \neq x_2$ force the
point. -/
theorem affRho_inj_slope (m b₀ : F) (p : F × F)
    (hp : ¬ affIncident p (AffineLn.slope m b₀))
    ⦃q₁ q₂ : {q : F × F // affIncident q (AffineLn.slope m b₀)}⦄
    (he : rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.slope m b₀) p hp q₁.1 q₁.2 =
      rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.slope m b₀) p hp q₂.1 q₂.2) :
    q₁ = q₂ := by
  have he' : (rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.slope m b₀) p hp q₁.1 q₁.2).toAdd =
      (rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.slope m b₀) p hp q₂.1 q₂.2).toAdd :=
    congrArg Multiplicative.toAdd he
  rw [rhoVal_affSlope_toAdd m b₀ p q₁.1 hp q₁.2,
      rhoVal_affSlope_toAdd m b₀ p q₂.1 hp q₂.2] at he'
  obtain ⟨⟨x₁, y₁⟩, hq₁⟩ := q₁
  obtain ⟨⟨x₂, y₂⟩, hq₂⟩ := q₂
  have hy₁ : y₁ = m * x₁ + b₀ := hq₁
  have hy₂ : y₂ = m * x₂ + b₀ := hq₂
  have e12 : y₁ - y₂ = m * (x₁ - x₂) := by rw [hy₁, hy₂]; ring
  -- main.tex lines 348–350: $(x_1-x_2)(mx+b-y) = 0$ killed by $y \neq mx+b$
  have hK : p.1 * m - (p.2 - b₀) ≠ 0 := by
    intro hc
    exact not_inc_slope m b₀ hp (by linear_combination -hc)
  have key : (x₁ - x₂) * (p.1 * m - (p.2 - b₀)) = 0 := by
    linear_combination he' - p.1 * e12
  have hx12 : x₁ = x₂ := mul_left_cancel₀ hK (by linear_combination key)
  refine Subtype.ext (affPt_eq hx12 ?_)
  have hy12 : y₁ = y₂ := by
    rw [hx12] at hy₁
    rw [hy₁, hy₂]
  exact hy12

/-- Surjectivity of $\rho_{L,p}$ for non-vertical $L$ (main.tex lines
362–377): given $z$, take $x_1 = (mx+b-y)^{-1}(z-xb)$. -/
theorem affRho_surj_slope (m b₀ : F) (p : F × F)
    (hp : ¬ affIncident p (AffineLn.slope m b₀)) (g : Multiplicative F) :
    ∃ q : {q : F × F // affIncident q (AffineLn.slope m b₀)},
      rhoVal (affineStruct F) affineStruct_isLinearSpace affPhi
        (AffineLn.slope m b₀) p hp q.1 q.2 = g := by
  set X : F := (p.1 * m - (p.2 - b₀))⁻¹ * (g.toAdd - p.1 * b₀) with hX
  have hK : p.1 * m - (p.2 - b₀) ≠ 0 := by
    intro hc
    exact not_inc_slope m b₀ hp (by linear_combination -hc)
  have hY : affIncident (X, m * X + b₀) (AffineLn.slope m b₀) := by
    simp only [affIncident]
  have key := rhoVal_affSlope_toAdd m b₀ p (X, m * X + b₀) hp hY
  refine ⟨⟨(X, m * X + b₀), hY⟩, ?_⟩
  apply ext_toAdd
  rw [key, hX]
  field_simp [hK]
  ring

/-! ## Theorem 7 -/

/-- **Theorem 7** (`thm_affine`): $\mathfrak{M}(\Gamma,\varphi)$ for the
affine plane over a field $\mathbb{F}$ with gain $\varphi(L_b,(b,y)) = -by$,
$\varphi(L_{m,b},(x,mx+b)) = xb$ and the regular additive action is a
generalized quadrangle (main.tex lines 264–274). Route: Theorem 5 +
Proposition 6 reduce the claim to bijectivity of every $\rho_{L,p}$
(main.tex line 277), discharged by the master computations above. -/
theorem thm_affine :
    (constructionM (Λ := F) (affineStruct F) affPhi).IsGenNGon 4 := by
  refine (thm_gq_rho (affineStruct F) affPhi affineStruct_isLinearSpace).2 ?_
  intro L p hp mu
  refine (prop_regular (affineStruct F) affineStruct_isLinearSpace affPhi L p
    hp mu aff_free aff_trans).2 ?_
  cases L with
  | vert v =>
      exact ⟨fun q₁ q₂ he => affRho_inj_vert v p hp he,
        fun g => affRho_surj_vert v p hp g⟩
  | slope m b =>
      exact ⟨fun q₁ q₂ he => affRho_inj_slope m b p hp he,
        fun g => affRho_surj_slope m b p hp g⟩

end Thm7

end McCulloch25_1
