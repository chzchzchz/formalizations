import McCulloch25_1.Basic
import McCulloch25_1.Lem3

/-!
# Lemma 4: uniqueness of 2-chains between same-sort objects of 𝔐

McCulloch25-1, Lemma 4.

Source: `/home/chz/src/gamskil/docs/arxiv/2502.01805/main.tex`
lines 173–189 (statement at 173–175, proof at 177–189).

**Erratum E1** (recorded in
`/home/chz/src/gamskil/docs/papers/open/McCulloch25-1/open_questions.md`):
the printed hypothesis is $d(u,v) \le 2$, which fails at $u = v = x_p$ for
$|\Lambda| \ge 2$ (then $d(x_p,x_p)=0\le2$ while $(x_p,z_{p,\mu},x_p)$ is a
valid $2$-chain for every $\mu$). The formal statement uses $d(u,v)=2$
exactly; Theorem 5 invokes it only at genuine distance-2 pairs
(main.tex line 207).

Formalization delta: the linear-space hypothesis is carried explicitly; the
printed proof appeals to it once, for uniqueness of the shared point of two
distinct lines (main.tex line 188, "…a linear space and hence a common point
$p$ is unique").
-/

namespace McCulloch25_1

open IncidenceStruct

variable {P B G Λ : Type _} [Group G] [MulAction G Λ]

section Lem4

variable (S : IncidenceStruct P B) (φ : B → P → G)
local notation "M" => constructionM S φ

/-- Lemma 4 (`lem_two_chain`), repaired per erratum E1: if $u,v$ have the
same sort and $d(u,v) = 2$, then every two $2$-chains from $u$ to $v$ have
the same sequence (main.tex lines 173–175, proof lines 177–189). -/
theorem lem4 (hls : S.IsLinearSpace) ⦃u v : Obj (MPoint P B Λ) (MLine P Λ)⦄
    (hsame : u.tag = v.tag) (hd : HasDist M 2 u v)
    (c₁ c₂ : Chain M 2 u v) : c₁.seq = c₂.seq := by
  have h0 := hd.2 0 (by omega)
  have hne : u ≠ v := by
    intro he
    subst he
    exact h0.elim (Chain.refl M _)
  obtain ⟨m₁, hu₁, hm₁, hseq₁⟩ := c₁.two_shape
  obtain ⟨m₂, hu₂, hm₂, hseq₂⟩ := c₂.two_shape
  have key : m₁ = m₂ := by
    cases u with
    | pt pu =>
      cases pu with
      | x p =>
        -- main.tex line 184 (Case 2): an $x/x$ pair at distance $2$ forces
        -- $p = q$, i.e. $u = v$, contradicting the empty $0$-chain set.
        cases v with
        | pt pv =>
          cases pv with
          | x q =>
            cases m₁ with
            | pt wp => exact ((not_objInc_pt_pt _ _) hu₁).elim
            | ln wl =>
              cases wl with
              | z r nu =>
                have hrp : p = r := (mi_x_iff S φ p r nu).mp hu₁
                have hrq : q = r := (mi_x_iff S φ q r nu).mp hm₁
                exact (hne (by rw [hrp, ← hrq])).elim
          -- main.tex line 186 (Case 3): the middle term is forced to
          -- $z_{p,\varphi(bp)^{-1}\cdot\lambda}$ on both chains.
          | y b la =>
            cases m₁ with
            | pt wp => exact ((not_objInc_pt_pt _ _) hu₁).elim
            | ln wl =>
              cases wl with
              | z r nu =>
                have hrp : p = r := (mi_x_iff S φ p r nu).mp hu₁
                subst hrp
                obtain ⟨-, hnu⟩ := (mi_y_iff S φ b la p nu).mp hm₁
                cases m₂ with
                | pt wp => exact ((not_objInc_pt_pt _ _) hu₂).elim
                | ln wl₂ =>
                  cases wl₂ with
                  | z r₂ nu₂ =>
                    have hr₂p : p = r₂ := (mi_x_iff S φ p r₂ nu₂).mp hu₂
                    subst hr₂p
                    obtain ⟨-, hnu₂⟩ := (mi_y_iff S φ b la p nu₂).mp hm₂
                    rw [hnu, hnu₂]
        | ln vl =>
          cases vl with
          | z q nu => exact absurd hsame (by simp [Obj.tag])
      | y b la =>
        cases v with
        | pt pv =>
          cases pv with
          | x q =>
            -- Mirror of main.tex line 186: the middle term is forced to
            -- $z_{q,\varphi(bq)\cdot\lambda}$ on both chains.
            cases m₁ with
            | pt wp => exact ((not_objInc_pt_pt _ _) hu₁).elim
            | ln wl =>
              cases wl with
              | z r nu =>
                have hqr : q = r := (mi_x_iff S φ q r nu).mp hm₁
                subst hqr
                obtain ⟨-, hnu⟩ := (mi_y_iff S φ b la q nu).mp hu₁
                cases m₂ with
                | pt wp => exact ((not_objInc_pt_pt _ _) hu₂).elim
                | ln wl₂ =>
                  cases wl₂ with
                  | z r₂ nu₂ =>
                    have hq₂r : q = r₂ := (mi_x_iff S φ q r₂ nu₂).mp hm₂
                    subst hq₂r
                    obtain ⟨-, hnu₂⟩ := (mi_y_iff S φ b la q nu₂).mp hu₂
                    rw [hnu, hnu₂]
          -- main.tex line 188 (Case 4): for $b \ne b'$ the shared point of
          -- the two lines is unique by axiom 1; for $b = b'$ the chain
          -- equations give $\varphi(bp)\cdot\lambda =
          -- \varphi(bp)\cdot\lambda'$, which cancels to $\lambda = \lambda'$,
          -- i.e. $u = v$.
          | y b' la' =>
            cases m₁ with
            | pt wp => exact ((not_objInc_pt_pt _ _) hu₁).elim
            | ln wl =>
              cases wl with
              | z p nu =>
                obtain ⟨hbp, hnu⟩ := (mi_y_iff S φ b la p nu).mp hu₁
                obtain ⟨hb'p, hnu'⟩ := (mi_y_iff S φ b' la' p nu).mp hm₁
                cases m₂ with
                | pt wp => exact ((not_objInc_pt_pt _ _) hu₂).elim
                | ln wl₂ =>
                  cases wl₂ with
                  | z p₂ nu₂ =>
                    obtain ⟨hbp₂, hnu₂⟩ := (mi_y_iff S φ b la p₂ nu₂).mp hu₂
                    obtain ⟨hb'p₂, hnu₂'⟩ :=
                      (mi_y_iff S φ b' la' p₂ nu₂).mp hm₂
                    by_cases hbb' : b = b'
                    · have hla' : la = la' := by
                        have hEq : φ b p • la = φ b' p • la' :=
                          hnu.symm.trans hnu'
                        rw [hbb'] at hEq
                        have hcc := congrArg (fun x : Λ => (φ b p)⁻¹ • x) hEq
                        simpa [inv_smul_smul] using hcc
                      exact (hne (by rw [hbb', hla'])).elim
                    · have hpp₂ : p = p₂ := by
                        by_contra hpp
                        obtain ⟨c, hc⟩ := hls.existsUnique_line p p₂ hpp
                        have hbc : b = c := hc.2 b ⟨hbp, hbp₂⟩
                        have hb₂c : b' = c := hc.2 b' ⟨hb'p, hb'p₂⟩
                        exact hbb' (hbc.trans hb₂c.symm)
                      subst hpp₂
                      rw [hnu, ← hnu₂]
        | ln vl =>
          cases vl with
          | z q nu => exact absurd hsame (by simp [Obj.tag])
    | ln ul =>
      cases ul with
      | z p mu =>
        cases v with
        | pt pv =>
          cases pv with
          | x q => exact absurd hsame (by simp [Obj.tag])
          | y b la => exact absurd hsame (by simp [Obj.tag])
        | ln vl =>
          cases vl with
          | z q nu =>
            -- main.tex lines 178–182 (Case 1). An $x_r$ middle forces
            -- $r = p$ resp. $r_2 = p$. Against a $y_{b_2,\lambda_2}$ middle,
            -- $\mu = \varphi(b_2p)\cdot\lambda_2$ and
            -- $\nu = \varphi(b_2q)\cdot\lambda_2$, while the $x$-side gives
            -- $p = q$, so $\mu = \nu$, i.e. $u = v$.
            cases m₁ with
            | pt wp =>
              cases wp with
              | x r =>
                have hrp : r = p := (mi_x_iff S φ r p mu).mp hu₁
                cases m₂ with
                | pt wp₂ =>
                  cases wp₂ with
                  | x r₂ =>
                    have hr₂p : r₂ = p := (mi_x_iff S φ r₂ p mu).mp hu₂
                    rw [hrp, hr₂p]
                  | y b₂ la₂ =>
                    have hrq : r = q := (mi_x_iff S φ r q nu).mp hm₁
                    obtain ⟨-, hmu⟩ := (mi_y_iff S φ b₂ la₂ p mu).mp hu₂
                    obtain ⟨-, hnu⟩ := (mi_y_iff S φ b₂ la₂ q nu).mp hm₂
                    have hpq : p = q := hrp.symm.trans hrq
                    subst hpq
                    have hmunu : mu = nu := hmu.trans hnu.symm
                    exact (hne (by rw [hmunu])).elim
                | ln wl₂ => exact ((not_objInc_ln_ln _ _) hu₂).elim
              -- A $y_{b,\lambda}$ middle satisfies $\mu = \varphi(bp)\cdot\lambda$
              -- and $\nu = \varphi(bq)\cdot\lambda$. Against a second $x_{r_2}$
              -- middle, $p = q = r_2$, so $\mu = \nu$, i.e. $u = v$. Against a
              -- second $y_{b_2,\lambda_2}$ middle: if $p = q$ then again
              -- $\mu = \nu$ and $u = v$; otherwise $p \ne q$ are both incident
              -- with $b$ and $b_2$, so $b = b_2$ by axiom 1, and cancelling the
              -- bijection $\varphi(bp)\cdot(-)$ gives $\lambda = \lambda_2$.
              | y b la =>
                obtain ⟨hbp, hmu⟩ := (mi_y_iff S φ b la p mu).mp hu₁
                obtain ⟨hbq, hnu⟩ := (mi_y_iff S φ b la q nu).mp hm₁
                cases m₂ with
                | pt wp₂ =>
                  cases wp₂ with
                  | x r₂ =>
                    have hr₂p : r₂ = p := (mi_x_iff S φ r₂ p mu).mp hu₂
                    have hr₂q : r₂ = q := (mi_x_iff S φ r₂ q nu).mp hm₂
                    have hpq : p = q := hr₂p.symm.trans hr₂q
                    subst hpq
                    have hmunu : mu = nu := hmu.trans hnu.symm
                    exact (hne (by rw [hmunu])).elim
                  | y b₂ la₂ =>
                    obtain ⟨hb₂p, hmu₂⟩ := (mi_y_iff S φ b₂ la₂ p mu).mp hu₂
                    obtain ⟨hb₂q, hnu₂⟩ := (mi_y_iff S φ b₂ la₂ q nu).mp hm₂
                    by_cases hpq : p = q
                    · subst hpq
                      have hmunu : mu = nu := hmu.trans hnu.symm
                      exact (hne (by rw [hmunu])).elim
                    · have hbb₂ : b = b₂ := by
                        obtain ⟨c, hc⟩ := hls.existsUnique_line p q hpq
                        have hbc : b = c := hc.2 b ⟨hbp, hbq⟩
                        have hb₂c : b₂ = c := hc.2 b₂ ⟨hb₂p, hb₂q⟩
                        exact hbc.trans hb₂c.symm
                      have hla₂ : la = la₂ := by
                        have hEq : φ b p • la = φ b₂ p • la₂ :=
                          hmu.symm.trans hmu₂
                        rw [hbb₂] at hEq
                        have hcc := congrArg (fun x : Λ => (φ b p)⁻¹ • x) hEq
                        simpa [inv_smul_smul] using hcc
                      rw [hbb₂, hla₂]
                | ln wl₂ => exact ((not_objInc_ln_ln _ _) hu₂).elim
            | ln wl => exact ((not_objInc_ln_ln _ _) hu₁).elim
  rw [hseq₁, hseq₂, key]

end Lem4

end McCulloch25_1
