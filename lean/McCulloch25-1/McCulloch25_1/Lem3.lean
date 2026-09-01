import McCulloch25_1.Basic

/-!
# Distances and shortest chains inside 𝔐(Γ,φ): Lemma 3

McCulloch25-1, Lemma 3 (all four items as standalone statements).
Source: `/home/chz/src/gamskil/docs/arxiv/2502.01805/main.tex`
lines 153–171 (Lemma 3), lines 203–209 (the distance-bound input).
-/

namespace McCulloch25_1

open IncidenceStruct

variable {P B G Λ : Type _} [Group G] [MulAction G Λ]

/-- Object of `𝔐(Γ,φ)` representing the point `x_p` (main.tex line 93). -/
abbrev MX (p : P) : Obj (MPoint P B Λ) (MLine P Λ) := .pt (.x p)

/-- Object of `𝔐(Γ,φ)` representing the point `y_{b,λ}` (main.tex line 93). -/
abbrev MY (b : B) (la : Λ) : Obj (MPoint P B Λ) (MLine P Λ) := .pt (.y b la)

/-- Object of `𝔐(Γ,φ)` representing the line `z_{p,μ}` (main.tex line 94). -/
abbrev MZ (p : P) (mu : Λ) : Obj (MPoint P B Λ) (MLine P Λ) := .ln (.z p mu)

/-- The objects `x_p` and `z_{q,μ}` are distinct sorts (used to rule out
short chains; tags follow main.tex line 63's parity). -/
theorem MX_ne_MZ (p q : P) (mu : Λ) :
    @MX P B Λ p ≠ @MZ P B Λ q mu :=
  fun he => Obj.noConfusion he

/-- The objects `y_{b,λ}` and `z_{p,μ}` are distinct sorts (main.tex
line 63's point/line division of 𝔐). -/
theorem MY_ne_MZ (b : B) (la : Λ) (p : P) (mu : Λ) :
    @MY P B Λ b la ≠ @MZ P B Λ p mu :=
  fun he => Obj.noConfusion he

section Lem3

variable (S : IncidenceStruct P B) (φ : B → P → G)
local notation "M" => constructionM S φ

/-- Lemma 3 item 1 (statement main.tex line 156, proof line 164 "clear"):
`d(x_p, z_{p,μ}) = 1`, witnessed by the unique `1`-chain `(x_p, z_{p,μ})`. -/
theorem lem3_item1 (p : P) (mu : Λ) :
    HasDist M 1 (MX p) (MZ p mu) ∧
      ∀ c₁ c₂ : Chain M 1 (MX p) (MZ p mu), c₁.seq = c₂.seq := by
  refine ⟨⟨⟨[MX p, MZ p mu], rfl, rfl, rfl,
    ChainSeq.cons ((mi_x_iff S φ p p mu).2 rfl) (ChainSeq.single _)⟩,
    fun j hj => ?_⟩, fun c₁ c₂ => by rw [c₁.one_seq.1, c₂.one_seq.1]⟩
  have : j = 0 := by omega
  subst this
  exact isEmpty_chain_zero_of_ne M (MX_ne_MZ p p mu)

/-- Lemma 3 item 3 (statement main.tex line 158, proof line 164 "clear"):
if `b I p` and `μ = φ(bp)·λ` then `d(y_{b,λ}, z_{p,μ}) = 1`. -/
theorem lem3_item3 (b : B) (la : Λ) (p : P) (mu : Λ) (hinc : S.Incident p b)
    (heq : mu = φ b p • la) :
    HasDist M 1 (MY b la) (MZ p mu) ∧
      ∀ c₁ c₂ : Chain M 1 (MY b la) (MZ p mu), c₁.seq = c₂.seq := by
  refine ⟨⟨⟨[MY b la, MZ p mu], rfl, rfl, rfl,
    ChainSeq.cons ((mi_y_iff S φ b la p mu).2 ⟨hinc, heq⟩) (ChainSeq.single _)⟩,
    fun j hj => ?_⟩, fun c₁ c₂ => by rw [c₁.one_seq.1, c₂.one_seq.1]⟩
  have : j = 0 := by omega
  subst this
  exact isEmpty_chain_zero_of_ne M (MY_ne_MZ b la p mu)

/-- Existence half of Lemma 3 item 2 as a distance bound
(main.tex lines 157, 166): `d(x_p, z_{q,μ}) ≤ 3`; equality needs `p ≠ q`
and is recorded by `lem3_item2`. -/
theorem distLe_mx_mz (hls : S.IsLinearSpace) (p q : P) (mu : Λ) :
    DistLe M 3 (MX p) (MZ q mu) := by
  by_cases hpq : p = q
  · subst hpq
    exact ⟨1, by omega, (lem3_item1 S φ p mu).1.1⟩
  · obtain ⟨b', hb'p, hb'q⟩ :
        ∃ b', S.Incident p b' ∧ S.Incident q b' :=
      ⟨connLine S hls hpq, connLine_left S hls hpq, connLine_right S hls hpq⟩
    -- 3-chain (x_p, z_{p,λ₁}, y_{b',λ₂}, z_{q,μ}), λ's solved backwards from μ
    -- (main.tex lines 166: λ₂ = φ(b'q)^{-1}·μ transported through λ₁).
    refine ⟨3, le_refl _, ⟨[MX p, MZ p (φ b' p • (φ b' q)⁻¹ • mu),
      MY b' ((φ b' q)⁻¹ • mu), MZ q mu], by simp, by simp, by simp, ?_⟩⟩
    refine ChainSeq.cons ((mi_x_iff S φ p p _).2 rfl)
      (ChainSeq.cons (?h2) (ChainSeq.cons (?h3) (ChainSeq.single _)))
    · exact (mi_y_iff S φ b' _ p _).2 ⟨hb'p, by simp [smul_smul]⟩
    · exact (mi_y_iff S φ b' _ q _).2 ⟨hb'q, by simp [smul_smul]⟩

/-- Existence half of Lemma 3 item 4 in incident form
(main.tex lines 159, 168): if `b I p` then `d(y_{b,λ}, z_{p,μ}) ≤ 3`,
whatever `μ` is. -/
theorem distLe_my_mz_incident (b : B) (la : Λ) (p : P) (mu : Λ)
    (hinc : S.Incident p b) : DistLe M 3 (MY b la) (MZ p mu) := by
  by_cases heq : mu = φ b p • la
  · rw [heq]
    exact ⟨1, by omega,
      (lem3_item3 S φ b la p (φ b p • la) hinc rfl).1.1⟩
  · -- 3-chain (y_{b,λ}, z_{p,λ₁}, x_p, z_{p,μ}), λ₁ = φ(bp)·λ (line 168)
    refine ⟨3, le_refl _, ⟨[MY b la, MZ p (φ b p • la), MX p, MZ p mu],
      by simp, by simp, by simp, ?_⟩⟩
    refine ChainSeq.cons ((mi_y_iff S φ b la p _).2 ⟨hinc, rfl⟩)
      (ChainSeq.cons ((mi_x_iff S φ p p _).2 rfl)
        (ChainSeq.cons ((mi_x_iff S φ p p _).2 rfl) (ChainSeq.single _)))

/-- Uniqueness of the $3$-chain from $x_p$ to $z_{q,\lambda}$ when
$p \neq q$ (Lemma 3 item 2, uniqueness half; main.tex line 166). -/
theorem unique_three_xz (hls : S.IsLinearSpace) (p q : P) (lam : Λ)
    (hpq : p ≠ q)
    (c₁ c₂ : Chain (constructionM (Λ := Λ) S φ) 3 (MX p) (MZ q lam)) :
    c₁.seq = c₂.seq := by
  obtain ⟨m₁, m₂, h1, h2, h3, hs₁⟩ := c₁.three_shape
  obtain ⟨n₁, n₂, g1, g2, g3, hs₂⟩ := c₂.three_shape
  cases m₁ with
  | pt wp => exact ((not_objInc_pt_pt _ _) h1).elim
  | ln wl =>
    cases wl with
    | z r nu =>
      have hrp : p = r := (mi_x_iff S φ p r nu).mp h1
      subst hrp
      cases m₂ with
      | ln wl => exact ((not_objInc_ln_ln _ _) h2).elim
      | pt wp =>
        cases wp with
        | x r' =>
          have h2' : r' = p := (mi_x_iff S φ r' p nu).mp h2
          have h3' : r' = q := (mi_x_iff S φ r' q lam).mp h3
          exact absurd (h2'.symm.trans h3') hpq
        | y b' nu' =>
          obtain ⟨hb'p, hnu⟩ := (mi_y_iff S φ b' nu' p nu).mp h2
          obtain ⟨hb'q, hlam⟩ := (mi_y_iff S φ b' nu' q lam).mp h3
          have hconn : b' = connLine S hls hpq :=
            connLine_unique S hls hpq hb'p hb'q
          cases n₁ with
          | pt wp => exact ((not_objInc_pt_pt _ _) g1).elim
          | ln wl =>
            cases wl with
            | z r₂ nu₂ =>
              have hr₂p : p = r₂ := (mi_x_iff S φ p r₂ nu₂).mp g1
              subst hr₂p
              cases n₂ with
              | ln wl => exact ((not_objInc_ln_ln _ _) g2).elim
              | pt wp =>
                cases wp with
                | x r' =>
                  have h2₂ : r' = p := (mi_x_iff S φ r' p nu₂).mp g2
                  have h3₂ : r' = q := (mi_x_iff S φ r' q lam).mp g3
                  exact absurd (h2₂.symm.trans h3₂) hpq
                | y b₂ nu₂' =>
                  obtain ⟨hb₂p, hnu₂⟩ := (mi_y_iff S φ b₂ nu₂' p nu₂).mp g2
                  obtain ⟨hb₂q, hlam₂⟩ := (mi_y_iff S φ b₂ nu₂' q lam).mp g3
                  have hconn₂ : b₂ = connLine S hls hpq :=
                    connLine_unique S hls hpq hb₂p hb₂q
                  have hnu'c : nu' = (φ (connLine S hls hpq) q)⁻¹ • lam := by
                    rw [← hconn, hlam, inv_smul_smul]
                  have hnu₂'c : nu₂' = (φ (connLine S hls hpq) q)⁻¹ • lam := by
                    rw [← hconn₂, hlam₂, inv_smul_smul]
                  have hnuc : nu = φ (connLine S hls hpq) p • nu' := by
                    rw [hnu, hconn]
                  have hnu₂c : nu₂ = φ (connLine S hls hpq) p • nu₂' := by
                    rw [hnu₂, hconn₂]
                  rw [hs₁, hs₂, hnuc, hnu'c, hnu₂c, hnu₂'c, hconn, hconn₂]

/-- Uniqueness of the $3$-chain from incident $y_{b,\lambda}$ to $z_{p,\mu}$
with $\mu \neq \varphi(bp)\cdot\lambda$ (Lemma 3 item 4, uniqueness half;
main.tex lines 168-170). -/
theorem unique_three_yz_incident (hls : S.IsLinearSpace)
    (b : B) (la : Λ) (p : P) (mu : Λ) (hbp : S.Incident p b)
    (hne : mu ≠ φ b p • la)
    (hmin : ∀ j, j < 3 → IsEmpty (Chain (constructionM (Λ := Λ) S φ) j
      (MY b la) (MZ p mu)))
    (c₁ c₂ : Chain (constructionM (Λ := Λ) S φ) 3 (MY b la) (MZ p mu)) :
    c₁.seq = c₂.seq := by
  have norm : ∀ c : Chain (constructionM (Λ := Λ) S φ) 3 (MY b la) (MZ p mu),
      c.seq = [MY b la, MZ p (φ b p • la), MX p, MZ p mu] := by
    intro c
    obtain ⟨m₁, m₂, h1, h2, h3, hs⟩ := c.three_shape
    cases m₁ with
    | pt wp => exact ((not_objInc_pt_pt _ _) h1).elim
    | ln wl =>
      cases wl with
      | z p' lam₁ =>
        obtain ⟨hb'p', heq1⟩ := (mi_y_iff S φ b la p' lam₁).mp h1
        cases m₂ with
        | ln wl => exact ((not_objInc_ln_ln _ _) h2).elim
        | pt wp =>
          cases wp with
          | x r =>
            -- canonical form: both links force the first index $p$
            have hrp' : r = p' := (mi_x_iff S φ r p' lam₁).mp h2
            have hrp : r = p := (mi_x_iff S φ r p mu).mp h3
            subst hrp'
            subst hrp
            rw [hs, heq1]
          | y b'' lam₂ =>
            obtain ⟨hb''p', heq2⟩ := (mi_y_iff S φ b'' lam₂ p' lam₁).mp h2
            obtain ⟨hb''p, heq3⟩ := (mi_y_iff S φ b'' lam₂ p mu).mp h3
            by_cases hp'p : p' = p
            · subst hp'p
              -- $\mu = \lambda_1 = \varphi(bp)\cdot\lambda$ contradicts hne
              exact absurd ((heq3.trans heq2.symm).trans heq1) hne
            · -- $b'' = b$ (both join the distinct points $p',p$), then
              --   $\lambda_2 = \lambda$, so the middle equals the start and
              --   a $1$-chain appears, contradicting minimality
              have hp'p' : p' ≠ p := fun hh => hp'p hh
              have hbc : b'' = connLine S hls hp'p :=
                connLine_unique S hls hp'p hb''p' hb''p
              have hbb : b = connLine S hls hp'p :=
                connLine_unique S hls hp'p hb'p' hbp
              have hbb'' : b = b'' := hbb.trans hbc.symm
              have hEq : φ b p' • la = φ b'' p' • lam₂ :=
                heq1.symm.trans heq2
              rw [← hbb''] at hEq
              have hla₂ : la = lam₂ := by
                have hc := congrArg (fun x : Λ => (φ b p')⁻¹ • x) hEq
                simpa using hc
              rw [← hbb''] at h3
              rw [← hla₂] at h3
              exact (hmin 1 (by omega)).elim ⟨[MY b la, MZ p mu],
                rfl, rfl, rfl, ChainSeq.cons h3 (ChainSeq.single _)⟩
  exact (norm c₁).trans (norm c₂).symm

/-- Lemma 3 item 2 (statement main.tex line 157, proof line 166): if
`p ≠ q`, then `d(x_p, z_{q,λ}) = 3` and there is a unique `3`-chain in
𝔐(Γ,φ) from `x_p` to `z_{q,λ}`. -/
theorem lem3_item2 (hls : S.IsLinearSpace) (p q : P) (mu : Λ) (hpq : p ≠ q) :
    HasDist M 3 (MX p) (MZ q mu) ∧
      ∀ c₁ c₂ : Chain M 3 (MX p) (MZ q mu), c₁.seq = c₂.seq := by
  have hmin : ∀ j, j < 3 → IsEmpty (Chain M j (MX p) (MZ q mu)) := by
    intro j hj
    have hjc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjc with rfl | rfl | rfl
    · exact isEmpty_chain_zero_of_ne M (MX_ne_MZ p q mu)
    · -- a $1$-chain would be the incidence $x_p \mathrm{I}' z_{q,\mu}$,
      -- i.e. $p = q$ (main.tex line 95, first clause)
      exact ⟨fun c => hpq ((mi_x_iff S φ p q mu).mp c.one_seq.2)⟩
    · exact isEmpty_chain_two_of_tag_ne M (by simp [Obj.tag])
  refine ⟨⟨?_, hmin⟩, unique_three_xz S φ hls p q mu hpq⟩
  -- existence: `distLe_mx_mz` yields some chain of length ≤ 3; lengths < 3
  -- are excluded by `hmin`'s witnesses, so the length is exactly 3
  obtain ⟨k, hk, hc⟩ := distLe_mx_mz S φ hls p q mu
  obtain ⟨c⟩ := hc
  match k, c with
  | 3, c => exact ⟨c⟩
  | 0, c => exact absurd c.zero_seq.2 (MX_ne_MZ p q mu)
  | 1, c => exact absurd ((mi_x_iff S φ p q mu).mp c.one_seq.2) hpq
  | 2, c => exact absurd c.two_tag_eq (by simp [Obj.tag])
  | (k + 4), c => omega

/-- Lemma 3 item 4, incident case (statement main.tex line 159, proof lines
168–170): if `b I p` and `μ ≠ φ(bp)·λ`, then `d(y_{b,λ}, z_{p,μ}) = 3` and
there is a unique `3`-chain in 𝔐(Γ,φ) from `y_{b,λ}` to `z_{p,μ}`. -/
theorem lem3_item4 (hls : S.IsLinearSpace) (b : B) (la : Λ) (p : P) (mu : Λ)
    (hinc : S.Incident p b) (hne : mu ≠ φ b p • la) :
    HasDist M 3 (MY b la) (MZ p mu) ∧
      ∀ c₁ c₂ : Chain M 3 (MY b la) (MZ p mu), c₁.seq = c₂.seq := by
  have hmin : ∀ j, j < 3 → IsEmpty (Chain M j (MY b la) (MZ p mu)) := by
    intro j hj
    have hjc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjc with rfl | rfl | rfl
    · exact isEmpty_chain_zero_of_ne M (MY_ne_MZ b la p mu)
    · -- a $1$-chain would force $\mu = \varphi(bp)\cdot\lambda$
      -- (main.tex line 95, second clause)
      exact ⟨fun c => hne ((mi_y_iff S φ b la p mu).mp c.one_seq.2).2⟩
    · exact isEmpty_chain_two_of_tag_ne M (by simp [Obj.tag])
  refine ⟨⟨?_, hmin⟩,
    unique_three_yz_incident S φ hls b la p mu hinc hne hmin⟩
  obtain ⟨k, hk, hc⟩ := distLe_my_mz_incident S φ b la p mu hinc
  obtain ⟨c⟩ := hc
  match k, c with
  | 3, c => exact ⟨c⟩
  | 0, c => exact absurd c.zero_seq.2 (MY_ne_MZ b la p mu)
  | 1, c => exact absurd (((mi_y_iff S φ b la p mu).mp c.one_seq.2).2) hne
  | 2, c => exact absurd c.two_tag_eq (by simp [Obj.tag])
  | (k + 4), c => omega

end Lem3

end McCulloch25_1
