import McCulloch25_1.Thm5

/-!
# Theorem 5, item 3: parameter counts of the Steiner system

McCulloch25-1, Theorem 5 item 3, and the Steiner-system definition it
rests on.
Source: `/home/chz/src/gamskil/docs/arxiv/2502.01805/main.tex`
line 198 (item 3 statement), line 229 (its printed proof), and line 85
(definition of Steiner system $S(2,v,k)$).

Contents: `IsSteinerSystem` ($S(2,v,k)$: a linear space whose lines all
carry exactly $k$ points, $v = |\mathscr{P}|$), its realization under the
generalized-quadrangle hypothesis (`steiner_of_gq`, main.tex lines 197
and 227), and `thm5_item3`: assuming $\mathscr{P}$ finite,
$v \ge 3$, $k = |\Lambda| \ge 2$, every line of $\mathfrak{M}(\Gamma,\varphi)$
carries exactly $1+s = 1+\frac{v-1}{k-1}$ points and every point exactly
$k$ lines.

Formalization delta: the paper's "$t = k-1$" phrasing (main.tex line 229,
"every point … incident with exactly $1+t$ lines") is folded into the
point-count statement `= k`, i.e. $1+t = k$; $s$ appears verbatim as
$(v-1)/(k-1)$, whose divisibility side condition is discharged by the
double count `lines_through_count`.
-/

namespace McCulloch25_1

open IncidenceStruct

/-- Steiner system $S(2,v,k)$ (main.tex line 85): a linear space whose
point set has cardinality $v$ and whose lines all carry exactly $k$
points. -/
def IsSteinerSystem {P B : Type _} (S : IncidenceStruct P B) (k : ℕ) :
    Prop :=
  ∀ b : B, Nat.card {q : P // S.Incident q b} = k

/-- Three distinct points exist in a linear space (main.tex line 229:
"$|\mathscr{P}| \ge 3$" — two points on a line plus a point off it). -/
theorem three_distinct_points {P B : Type _} (S : IncidenceStruct P B)
    (hls : S.IsLinearSpace) :
    ∃ u v w : P, u ≠ v ∧ u ≠ w ∧ v ≠ w := by
  obtain ⟨p₀, b₀, hp₀⟩ := hls.nonincident
  obtain ⟨u, v, hne, hu, hv⟩ := hls.two_pts b₀
  obtain ⟨w, hw⟩ := exists_pt_not_on_line S hls b₀
  refine ⟨u, v, w, hne, ?_, ?_⟩
  · intro hc
    apply hw
    rw [← hc]
    exact hu
  · intro hc
    apply hw
    rw [← hc]
    exact hv

/-- Under the ρ-hypotheses every line carries exactly $|\Lambda|$ points,
so $(\mathscr{P},\mathscr{B},\mathrm{I})$ is a Steiner system
$S(2, v, |\Lambda|)$ (main.tex lines 197 and 227, item 2 tail). -/
theorem steiner_of_gq {P B G Λ : Type _} [Group G] [MulAction G Λ]
    (S : IncidenceStruct P B) (φ : B → P → G) (hls : S.IsLinearSpace)
    (hgq : (constructionM (Λ := Λ) S φ).IsGenNGon 4) [Nonempty Λ] :
    IsSteinerSystem S (Nat.card Λ) := fun b =>
  Nat.card_congr (Classical.choice (thm5_item2 S φ hls hgq b))

/-- A point other than `p` on line `b` exists whenever `p` lies on `b`
(axiom 2, main.tex line 81). -/
theorem exists_ne_of_mem {P B : Type _} (S : IncidenceStruct P B)
    (hls : S.IsLinearSpace) {p : P} {b : B} (_hp : S.Incident p b) :
    ∃ q : P, q ≠ p ∧ S.Incident q b := by
  obtain ⟨u, v, hne, hu, hv⟩ := hls.two_pts b
  by_cases hup : u = p
  · exact ⟨v, fun he => hne (hup.trans he.symm), hv⟩
  · exact ⟨u, hup, hu⟩

/-- The lines through `p` form a finite set when $\mathscr{P}$ is finite:
send each such line to one of its points $\ne p$; two distinct lines
through $p$ meet only in $p$ (axiom 1), so the assignment is injective. -/
theorem finite_lines_through {P B : Type _} (S : IncidenceStruct P B)
    (hls : S.IsLinearSpace) (p : P) [Finite P] :
    Finite {b : B // S.Incident p b} := by
  classical
  have hex : ∀ b : {b : B // S.Incident p b},
      ∃ q : P, q ≠ p ∧ S.Incident q ↑b := fun b =>
    exists_ne_of_mem S hls b.property
  choose g hg using hex
  refine Finite.of_injective
    (f := fun b => (⟨g b, (hg b).1⟩ : {q : P // q ≠ p})) ?_
  intro b c hbc
  have hval : g b = g c := congrArg Subtype.val hbc
  have hincc : S.Incident (g b) ↑c := by
    have h2 := (hg c).2
    rw [← hval] at h2
    exact h2
  obtain ⟨joiner, -, juniq⟩ :=
    hls.existsUnique_line p (g b) (Ne.symm (hg b).1)
  exact Subtype.ext
    ((juniq _ ⟨b.property, (hg b).2⟩).trans
      (juniq _ ⟨c.property, hincc⟩).symm)

open Classical in
/-- Removing one point drops the count by one: the points of `b`
correspond to `Option` of the points of `b` other than `p`. -/
private noncomputable def ptOptMap {P B : Type _} (S : IncidenceStruct P B)
    (p : P) (b : B) (q : {q : P // S.Incident q b}) :
    Option {r : P // r ≠ p ∧ S.Incident r b} :=
  if h : q.val = p then Option.none
  else Option.some ⟨q.val, h, q.property⟩

private def ptOptBwd {P B : Type _} (S : IncidenceStruct P B)
    (p : P) (b : B) (hb : S.Incident p b)
    (o : Option {r : P // r ≠ p ∧ S.Incident r b}) :
    {q : P // S.Incident q b} :=
  match o with
  | Option.none => ⟨p, hb⟩
  | Option.some u => ⟨u.val, u.property.2⟩

open Classical in
private noncomputable def ptCmplMap {P : Type _} (p : P) (x : P) :
    Option {q : P // q ≠ p} :=
  if h : x = p then Option.none else Option.some ⟨x, h⟩

private def ptCmplBwd {P : Type _} (p : P)
    (o : Option {q : P // q ≠ p}) : P :=
  match o with
  | Option.none => p
  | Option.some u => u.val

theorem card_mem_sub_one {P B : Type _} (S : IncidenceStruct P B)
    [Finite P] {p : P} {b : B} (hp : S.Incident p b) :
    Nat.card {q : P // S.Incident q b}
      = Nat.card {r : P // r ≠ p ∧ S.Incident r b} + 1 := by
  classical
  rw [← Finite.card_option (α := {r : P // r ≠ p ∧ S.Incident r b})]
  show Nat.card {q : P // S.Incident q b}
      = Nat.card (Option {r : P // r ≠ p ∧ S.Incident r b})
  refine Nat.card_eq_of_bijective (fun q => ptOptMap S p b q) ?_
  constructor
  · intro a c hac
    by_cases hu' : a.val = p
    · by_cases hv' : c.val = p
      · exact Subtype.ext (by rw [hu', hv'])
      · exfalso
        simp [ptOptMap, hu', hv'] at hac
    · by_cases hv' : c.val = p
      · exfalso
        simp [ptOptMap, hu', hv'] at hac
      · simp only [ptOptMap, dif_neg hu', dif_neg hv'] at hac
        injection hac with hinj
        injection hinj with hval
        exact Subtype.ext hval
  · intro o
    cases o with
    | none => exact ⟨⟨p, hp⟩, by simp [ptOptMap]⟩
    | some u =>
        refine ⟨⟨u.val, u.property.2⟩, ?_⟩
        simp only [ptOptMap, dif_neg u.property.1]

/-- Removing the distinguished point `p` drops the count by one. -/
theorem card_complement_pt {P : Type _} [Finite P] (p : P) :
    Nat.card {q : P // q ≠ p} = Nat.card P - 1 := by
  classical
  have hcard : Nat.card P = Nat.card {q : P // q ≠ p} + 1 := by
    rw [← Finite.card_option (α := {q : P // q ≠ p})]
    refine Nat.card_eq_of_bijective (fun x => ptCmplMap p x) ?_
    constructor
    · intro a c hac
      by_cases hu' : a = p
      · by_cases hv' : c = p
        · exact hu'.trans hv'.symm
        · exfalso
          simp [ptCmplMap, hu', hv'] at hac
      · by_cases hv' : c = p
        · exfalso
          simp [ptCmplMap, hu', hv'] at hac
        · simp only [ptCmplMap, dif_neg hu', dif_neg hv'] at hac
          injection hac with hinj
          exact congrArg Subtype.val hinj
    · intro o
      refine ⟨ptCmplBwd p o, ?_⟩
      cases o with
      | none => simp [ptCmplMap, ptCmplBwd]
      | some u => simp [ptCmplMap, ptCmplBwd, dif_neg u.property]
  omega

/-- Forward map of the point-partition by connecting lines with `p`
(main.tex line 229 double count). -/
private noncomputable def affPartFwd {P B : Type _} (S : IncidenceStruct P B)
    (hls : S.IsLinearSpace) (p : P) (q : {q : P // q ≠ p}):
    Σ b : {b : B // S.Incident p b},
      {r : P // r ≠ p ∧ S.Incident r ↑b} :=
  ⟨⟨connLine S hls (q.property), connLine_right S hls (q.property)⟩,
    ⟨q.val, q.property, connLine_left S hls (q.property)⟩⟩

/-- Backward map of the point-partition by connecting lines with `p`. -/
private noncomputable def affPartBwd {P B : Type _} (S : IncidenceStruct P B)
    (_hls : S.IsLinearSpace) (p : P)
    (t : Σ b : {b : B // S.Incident p b},
      {r : P // r ≠ p ∧ S.Incident r ↑b}) : {q : P // q ≠ p} :=
  ⟨t.2.val, t.2.property.1⟩

/-- Double count (main.tex line 229): the $v - 1$ points other than $p$
are partitioned by their connecting line with $p$ into $r_p$ fibers, each
of size $k - 1$. -/
theorem lines_through_count {P B G Λ : Type _} [Group G] [MulAction G Λ]
    (S : IncidenceStruct P B) (φ : B → P → G) (hls : S.IsLinearSpace)
    (hgq : (constructionM (Λ := Λ) S φ).IsGenNGon 4) [Nonempty Λ]
    (p : P) [Finite P] :
    (Nat.card P - 1)
      = Nat.card {b : B // S.Incident p b} * (Nat.card Λ - 1) := by
  classical
  haveI hfinsp : Finite {b : B // S.Incident p b} :=
    finite_lines_through S hls p
  have hfin : Fintype {b : B // S.Incident p b} := Fintype.ofFinite _
  have hsig : {q : P // q ≠ p} ≃
      Σ b : {b : B // S.Incident p b},
        {r : P // r ≠ p ∧ S.Incident r ↑b} :=
    { toFun := affPartFwd S hls p
      invFun := affPartBwd S hls p
      left_inv := fun q => by
        simp [affPartFwd, affPartBwd]
      right_inv := by
        rintro ⟨⟨b, hb⟩, u, hu, hub⟩
        have hbc : b = connLine S hls hu :=
          connLine_unique S hls hu hub hb
        subst hbc
        simp [affPartFwd, affPartBwd] }
  have hfib : ∀ b : {b : B // S.Incident p b},
      Nat.card {r : P // r ≠ p ∧ S.Incident r ↑b} = Nat.card Λ - 1 := by
    intro b
    have hk := card_mem_sub_one S (b.property)
    rw [steiner_of_gq S φ hls hgq b.val] at hk
    omega
  rw [← card_complement_pt p, Nat.card_congr hsig, Nat.card_sigma,
    Finset.sum_congr rfl (fun b _ => hfib b), Finset.sum_const,
    Nat.card_eq_fintype_card (α := {b : B // S.Incident p b})]
  simp

/-! ## Point and line counts inside 𝔐 (main.tex line 229) -/

/-- Points of 𝔐 on $z_{p,\mu}$ map to `none` (for $x_p$) or to the line
through $p$ backing a $y$-point (main.tex line 229). -/
private noncomputable def zPtsMap {P B G Λ : Type _} [Group G] [MulAction G Λ]
    (S : IncidenceStruct P B) (φ : B → P → G) (p : P) (mu : Λ)
    (mp : MPoint P B Λ) (hmp : MI S φ mp (MLine.z p mu)) :
    Option {b : B // S.Incident p b} :=
  match mp, hmp with
  | .x _, _ => Option.none
  | .y b _, hmp => Option.some ⟨b, ((mi_y_iff S φ b _ p mu).mp hmp).1⟩

/-- Backward map for `zPtsMap`. -/
private noncomputable def zPtsBwd {P B G Λ : Type _} [Group G] [MulAction G Λ]
    (S : IncidenceStruct P B) (φ : B → P → G) (p : P) (mu : Λ) :
    Option {b : B // S.Incident p b} →
      {mp : MPoint P B Λ // MI S φ mp (MLine.z p mu)}
  | Option.none => ⟨MPoint.x p, MI.xz p mu⟩
  | Option.some b =>
      ⟨MPoint.y b.val ((φ b.val p)⁻¹ • mu),
        MI.yz b.property (smul_inv_smul (φ b.val p) mu).symm⟩

/-- Lines of 𝔐 through $y_{b,\lambda}$ correspond to points $q$ on $b$
(main.tex line 229). -/
private noncomputable def yLinesMap {P B G Λ : Type _} [Group G]
    [MulAction G Λ] (S : IncidenceStruct P B) (φ : B → P → G) (b : B)
    (la : Λ) (ml : MLine P Λ) (hml : MI S φ (MPoint.y b la) ml) :
    {q : P // S.Incident q b} :=
  match ml, hml with
  | .z q mu', hml =>
      (⟨q, ((mi_y_iff S φ b la q mu').mp hml).1⟩ :
        {q : P // S.Incident q b})

/-- Backward map for `yLinesMap`. -/
private noncomputable def yLinesBwd {P B G Λ : Type _} [Group G]
    [MulAction G Λ] (S : IncidenceStruct P B) (φ : B → P → G) (b : B)
    (la : Λ) (q : {q : P // S.Incident q b}) :
    {ml : MLine P Λ // MI S φ (MPoint.y b la) ml} :=
  ⟨MLine.z q.val (φ b q.val • la), MI.yz q.property rfl⟩

/-- Lines of 𝔐 through $x_p$ correspond to parameters in $\Lambda$
(main.tex line 229). -/
private noncomputable def xLinesMap {P B G Λ : Type _} [Group G]
    [MulAction G Λ] (S : IncidenceStruct P B) (φ : B → P → G) (p : P)
    (ml : MLine P Λ) (hml : MI S φ (MPoint.x p) ml) : Λ :=
  match ml, hml with
  | .z _ mu', _ => mu'

/-- Backward map for `xLinesMap`. -/
private noncomputable def xLinesBwd {P B G Λ : Type _} [Group G]
    [MulAction G Λ] (S : IncidenceStruct P B) (φ : B → P → G) (p : P)
    (mu : Λ) : {ml : MLine P Λ // MI S φ (MPoint.x p) ml} :=
  ⟨MLine.z p mu, MI.xz p mu⟩

/-- Every line $z_{p,\mu}$ of 𝔐 carries $r_p + 1$ points, where $r_p$ is
the number of base-lines through $p$ (main.tex line 229). -/
theorem card_line_z {P B G Λ : Type _} [Group G] [MulAction G Λ]
    (S : IncidenceStruct P B) (φ : B → P → G) (hls : S.IsLinearSpace)
    (p : P) (mu : Λ) [Finite P] :
    Nat.card {mp : MPoint P B Λ // MI S φ mp (MLine.z p mu)}
      = Nat.card {b : B // S.Incident p b} + 1 := by
  classical
  haveI hfinsp : Finite {b : B // S.Incident p b} :=
    finite_lines_through S hls p
  rw [← Finite.card_option (α := {b : B // S.Incident p b})]
  refine Nat.card_eq_of_bijective (fun mp => zPtsMap S φ p mu mp mp.property) ?_
  constructor
  · rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    cases a with
    | x q =>
        cases c with
        | x r =>
            have hq : q = p := (mi_x_iff S φ q p mu).mp ha
            have hr : r = p := (mi_x_iff S φ r p mu).mp hc
            subst hr
            subst hq
            rfl
        | y e lc =>
            exfalso
            simp only [zPtsMap] at hac
            exact Option.noConfusion hac
    | y d ld =>
        cases c with
        | x q =>
            exfalso
            simp only [zPtsMap] at hac
            exact Option.noConfusion hac
        | y e lc =>
            have hd : d = e := by
              simp only [zPtsMap] at hac
              exact congrArg Subtype.val (Option.some.inj hac)
            obtain ⟨-, he1⟩ := (mi_y_iff S φ d ld p mu).mp ha
            obtain ⟨-, he2⟩ := (mi_y_iff S φ e lc p mu).mp hc
            rw [hd] at he1
            have hdlc : ld = lc := by
              have r1 : (φ e p)⁻¹ • mu = ld := by rw [he1, inv_smul_smul]
              have r2 : (φ e p)⁻¹ • mu = lc := by rw [he2, inv_smul_smul]
              exact r1.symm.trans r2
            exact Subtype.ext
              ((congrArg (fun t => MPoint.y t ld) hd).trans
                (congrArg (MPoint.y e) hdlc))
  · intro o
    refine ⟨zPtsBwd S φ p mu o, ?_⟩
    cases o with
    | none => rfl
    | some b => simp [zPtsMap, zPtsBwd]

/-- Every point $y_{b,\lambda}$ of 𝔐 carries $|\mathscr{P}_b|$ lines
(main.tex line 229). -/
theorem card_point_y {P B G Λ : Type _} [Group G] [MulAction G Λ]
    (S : IncidenceStruct P B) (φ : B → P → G) (b : B) (la : Λ) :
    Nat.card {ml : MLine P Λ // MI S φ (MPoint.y b la) ml}
      = Nat.card {q : P // S.Incident q b} := by
  refine Nat.card_eq_of_bijective
    (fun ml => yLinesMap S φ b la ml ml.property) ?_
  constructor
  · rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    cases a with
    | z q mu' =>
        cases c with
        | z r nu' =>
            have hq : q = r := by
              simp only [yLinesMap] at hac
              exact congrArg Subtype.val hac
            have hmu : mu' = nu' := by
              have e1 := ((mi_y_iff S φ b la q mu').mp ha).2
              have e2 := ((mi_y_iff S φ b la r nu').mp hc).2
              rw [hq] at e1
              exact e1.trans e2.symm
            exact Subtype.ext (α := MLine P Λ) (by simp [hq, hmu])
  · intro q
    exact ⟨yLinesBwd S φ b la q, rfl⟩

/-- Every point $x_p$ of 𝔐 carries $|\Lambda|$ lines (main.tex line 229). -/
theorem card_point_x {P B G Λ : Type _} [Group G] [MulAction G Λ]
    (S : IncidenceStruct P B) (φ : B → P → G) (p : P) :
    Nat.card {ml : MLine P Λ // MI S φ (MPoint.x p) ml}
      = Nat.card Λ := by
  refine Nat.card_eq_of_bijective
    (fun ml => xLinesMap S φ p ml ml.property) ?_
  constructor
  · rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    cases a with
    | z q mu' =>
        cases c with
        | z r nu' =>
            have hmu : mu' = nu' := by
              simp only [xLinesMap] at hac
              exact hac
            have hpq : p = q := (mi_x_iff S φ p q mu').mp ha
            have hpr : p = r := (mi_x_iff S φ p r nu').mp hc
            exact Subtype.ext (α := MLine P Λ)
              ((congrArg (MLine.z q) hmu).trans
                (congrArg (fun t => MLine.z t nu') (hpq.symm.trans hpr)))
  · intro mu
    exact ⟨xLinesBwd S φ p mu, rfl⟩

/-- **Theorem 5, item 3** (main.tex lines 198 and 229): if $\mathscr{P}$
is finite, then $v = |\mathscr{P}| \ge 3$, $k = |\Lambda| \ge 2$, every
line of $\mathfrak{M}$ carries exactly $1+s$ points with
$s = \frac{v-1}{k-1}$, and every point carries exactly $k = 1+t$ lines
with $t = k-1$. -/
theorem thm5_item3 {P B G Λ : Type _} [Group G] [MulAction G Λ]
    (S : IncidenceStruct P B) (φ : B → P → G) (hls : S.IsLinearSpace)
    (hgq : (constructionM (Λ := Λ) S φ).IsGenNGon 4) [Nonempty Λ]
    [Finite P] :
    3 ≤ Nat.card P ∧ 2 ≤ Nat.card Λ ∧
      (∀ ml : MLine P Λ,
          Nat.card {mp : MPoint P B Λ // MI S φ mp ml}
            = 1 + (Nat.card P - 1) / (Nat.card Λ - 1)) ∧
      (∀ mp : MPoint P B Λ,
          Nat.card {ml : MLine P Λ // MI S φ mp ml} = Nat.card Λ) := by
  -- shared counting input (main.tex line 229)
  have hk2 : 2 ≤ Nat.card Λ := by
    obtain ⟨p₀, b₀, hp₀⟩ := hls.nonincident
    obtain ⟨u, v, hne, hu, hv⟩ := hls.two_pts b₀
    have hnt : Nontrivial {q : P // S.Incident q b₀} :=
      ⟨⟨u, hu⟩, ⟨v, hv⟩, fun he => hne (congrArg Subtype.val he)⟩
    have hlt : 1 < Nat.card {q : P // S.Incident q b₀} :=
      Finite.one_lt_card_iff_nontrivial.mpr hnt
    rw [steiner_of_gq S φ hls hgq b₀] at hlt
    omega
  have hK0 : Nat.card Λ - 1 ≠ 0 := by omega
  have hdiv : ∀ p : P,
      (Nat.card P - 1) / (Nat.card Λ - 1)
        = Nat.card {b : B // S.Incident p b} := fun p => by
    exact Nat.div_eq_of_eq_mul_left
      (by omega : 0 < Nat.card Λ - 1)
      (lines_through_count S φ hls hgq p)
  refine ⟨?_, hk2, ?_, ?_⟩
  · -- v ≥ 3 (main.tex line 229, first sentence)
    obtain ⟨u, v, w, h1, h2, h3⟩ := three_distinct_points S hls
    have hinj : Function.Injective
        (f := fun i : Fin 3 =>
          match i.val with
          | 0 => u
          | 1 => v
          | _ => w) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    haveI hfinP : Fintype P := Fintype.ofFinite _
    rw [show (3 : ℕ) = Fintype.card (Fin 3) from by simp]
    calc Fintype.card (Fin 3) ≤ Fintype.card P :=
          Fintype.card_le_of_injective _ hinj
      _ = Nat.card P := Nat.card_eq_fintype_card.symm
  · -- every line carries exactly 1 + s points
    intro ml
    cases ml with
    | z p mu =>
      rw [card_line_z S φ hls p mu, hdiv p]
      omega
  · -- every point carries exactly k = 1 + t lines
    intro mp
    cases mp with
    | x p => exact card_point_x S φ p
    | y b la =>
        exact (card_point_y S φ b la).trans (steiner_of_gq S φ hls hgq b)

end McCulloch25_1
