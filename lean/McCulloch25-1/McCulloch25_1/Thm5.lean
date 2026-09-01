import McCulloch25_1.Basic
import McCulloch25_1.Lem3
import McCulloch25_1.Lem4
import McCulloch25_1.Prop6

/-!
# Theorem 5: 𝔐(Γ,φ) is a generalized quadrangle iff ρ is bijective

McCulloch25-1, Theorem 5 (the paper's hub), fully proved. Contents:
`thm_gq_rho` (the equivalence), `thm5_converse` (converse half,
main.tex lines 219-221), items 1 and 2, and the forward-direction
machinery (`Chain.four_tag_eq`, `hasDist_three_of_gq`, `distLe_four`,
`unique_three_missing`). Lemma 3's uniqueness halves
(`unique_three_xz`, `unique_three_yz_incident`) and the promoted full
statements `lem3_item2`/`lem3_item4` live in `Lem3.lean`.

Source: `/home/chz/src/gamskil/docs/arxiv/2502.01805/main.tex`
lines 193-230 (statement at 193-199, proof at 202-230).
-/

namespace McCulloch25_1

open IncidenceStruct

variable {P B G Λ : Type _} [Group G] [MulAction G Λ]

section Thm5

variable (S : IncidenceStruct P B) (φ : B → P → G)

/-- Every point lies on some line; consequence of axioms 1-3
(main.tex lines 80-82; presupposed at main.tex line 229). -/
theorem exists_line_of (hls : S.IsLinearSpace) (p : P) :
    ∃ b : B, S.Incident p b := by
  obtain ⟨p₀, b₀, hp₀⟩ := hls.nonincident
  by_cases hb₀ : S.Incident p b₀
  · exact ⟨b₀, hb₀⟩
  · -- $p \notin b_0$: a point $q_1 \in b_0$ differs from $p$ and
    -- axiom 1 produces their common line through $p$
    obtain ⟨q₁, q₂, hne, hq₁b, _⟩ := hls.two_pts b₀
    have hpq₁ : p ≠ q₁ := fun he => hb₀ (by rw [he]; exact hq₁b)
    exact ⟨connLine S hls hpq₁, connLine_left S hls hpq₁⟩

/-- Some point misses any given line (axioms 1-3, main.tex lines 80-82).
Route: were every point on `b`, two distinct points of `b₀` (axiom 2) would
lie on both `b` and `b₀`, forcing `b = b₀` by axiom 1 and contradicting
axiom 3's witness `p₀` missed by `b₀`. -/
theorem exists_pt_not_on_line (hls : S.IsLinearSpace) (b : B) :
    ∃ p : P, ¬ S.Incident p b := by
  by_cases hall : ∀ p : P, S.Incident p b
  · exfalso
    obtain ⟨p₀, b₀, hp₀⟩ := hls.nonincident
    obtain ⟨q₁, q₂, hne, hq₁b₀, hq₂b₀⟩ := hls.two_pts b₀
    obtain ⟨c, hc⟩ := hls.existsUnique_line q₁ q₂ hne
    have hbc : b = c := hc.2 b ⟨hall q₁, hall q₂⟩
    have hb₀c : b₀ = c := hc.2 b₀ ⟨hq₁b₀, hq₂b₀⟩
    have hp₀b₀ : S.Incident p₀ b₀ := by
      rw [hb₀c, ← hbc]
      exact hall p₀
    exact hp₀ hp₀b₀
  · push_neg at hall
    exact hall

namespace IncidenceStruct

/-- Parity fact for `4`-chains (main.tex line 63: even distance joins same
sorts), by splitting the chain into two `2`-chains. -/
theorem Chain.four_tag_eq {P B : Type _} {S : IncidenceStruct P B}
    {u v : Obj P B} (c : S.Chain 4 u v) : u.tag = v.tag := by
  obtain ⟨seq, hlen, hhead, hlast, hok⟩ := c
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
          | nil => rw [hs] at hlen; simp at hlen
          | cons f t4 =>
            cases t4 with
            | nil =>
                rw [hs] at hhead hlast hok
                simp at hhead hlast
                have hlinks : S.ObjInc a b ∧ S.ObjInc b d ∧ S.ObjInc d e ∧
                    S.ObjInc e f := by
                  cases hok with
                  | cons hh r =>
                    obtain ⟨i₂, i₃, i₄⟩ := chainSeq_quad S r
                    exact ⟨hh, i₂, i₃, i₄⟩
                obtain ⟨h₁, h₂, h₃, h₄⟩ := hlinks
                have pfx : S.Chain 2 a d :=
                  ⟨[a, b, d], rfl, rfl, rfl,
                    ChainSeq.cons h₁ (ChainSeq.cons h₂ (ChainSeq.single d))⟩
                have sfx : S.Chain 2 d f :=
                  ⟨[d, e, f], rfl, rfl, rfl,
                    ChainSeq.cons h₃ (ChainSeq.cons h₄ (ChainSeq.single f))⟩
                rw [← hhead, ← hlast]
                exact (Chain.two_tag_eq S pfx).trans (Chain.two_tag_eq S sfx)
            | cons g t5 => rw [hs] at hlen; simp at hlen

end IncidenceStruct

/-- Inside a generalized quadrangle $\mathfrak{M}(\Gamma,\varphi)$, a
nonincident pair $y_{b,\lambda}$, $z_{p,\mu}$ lies at distance exactly $3$
(main.tex lines 220-221: "it cannot be one since $b\ \cancel{\mathrm{I}}\ p$";
odd parity excludes $0$ and $2$, the diameter bound excludes $4$). -/
theorem hasDist_three_of_gq
    (hgq : (constructionM (Λ := Λ) S φ).IsGenNGon 4)
    (b : B) (la : Λ) (p : P) (nu : Λ) (hp : ¬ S.Incident p b) :
    HasDist (constructionM (Λ := Λ) S φ) 3 (MY b la) (MZ p nu) := by
  obtain ⟨k, hk, c⟩ := hgq.dist_le (MY b la) (MZ p nu)
  obtain ⟨c⟩ := c
  refine ⟨?_, ?_⟩
  · match k, c with
    | 0, c => exact absurd c.zero_seq.2 (MY_ne_MZ b la p nu)
    | 1, c => exact absurd ((mi_y_iff S φ b la p nu).mp c.one_seq.2).1 hp
    | 2, c => exact absurd c.two_tag_eq (by simp [Obj.tag])
    | 3, c => exact ⟨c⟩
    | 4, c => exact absurd c.four_tag_eq (by simp [Obj.tag])
  · intro j hj
    have hjc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hjc with rfl | rfl | rfl
    · exact isEmpty_chain_zero_of_ne _ (MY_ne_MZ b la p nu)
    · exact ⟨fun c => hp ((mi_y_iff S φ b la p nu).mp c.one_seq.2).1⟩
    · exact isEmpty_chain_two_of_tag_ne _ (by simp [Obj.tag])

/-- **Theorem 5, converse half**: the GQ axioms alone force every
$\rho_{b,p,\lambda}$ to be bijective (main.tex lines 219-221): for arbitrary
$\mu$, the unique $3$-chain from $y_{b,\lambda}$ to $z_{p,\mu}$ exhibits
$q \ \mathrm{I}\ b$ with $\rho_{b,p,\lambda}(q) = \mu$ (existence), and
uniqueness of that chain forces uniqueness of $q$ (injectivity). -/
theorem thm5_converse (hls : S.IsLinearSpace)
    (hgq : (constructionM (Λ := Λ) S φ).IsGenNGon 4) :
    ∀ (b : B) (p : P) (hp : ¬ S.Incident p b) (mu : Λ),
      Function.Bijective (rhoLam S hls φ b p hp mu) := by
  intro b p hp lam
  have hd3 : ∀ nu : Λ,
      HasDist (constructionM (Λ := Λ) S φ) 3 (MY b lam) (MZ p nu) :=
    fun nu => hasDist_three_of_gq S φ hgq b lam p nu hp
  refine ⟨fun q₁ q₂ he => ?_, fun nu => ?_⟩
  · -- main.tex line 221, uniqueness half: two witnesses give two $3$-chains,
    -- whose equality forces equal second terms
    have he' : rhoVal S hls φ b p hp q₁.1 q₁.2 • lam =
        rhoVal S hls φ b p hp q₂.1 q₂.2 • lam := he
    let build : ∀ (q : {q : P // S.Incident q b}) (_hne : p ≠ q.1) (tgt : Λ),
        rhoVal S hls φ b p hp q.1 q.2 • lam = tgt →
        Chain (constructionM (Λ := Λ) S φ) 3 (MY b lam) (MZ p tgt) :=
      fun q hne tgt htgt =>
        ⟨[MY b lam, MZ q.1 (φ b q.1 • lam),
            MY (connLine S hls hne)
              ((φ (connLine S hls hne) q.1)⁻¹ • (φ b q.1 • lam)),
          MZ p tgt],
          by simp, rfl, by simp,
          ChainSeq.cons ((mi_y_iff S φ b lam q.1 _).2 ⟨q.2, rfl⟩)
            (ChainSeq.cons ((mi_y_iff S φ (connLine S hls hne) _ q.1 _).2
                ⟨connLine_right S hls hne, by simp [smul_inv_smul]⟩)
              (ChainSeq.cons ((mi_y_iff S φ (connLine S hls hne) _ p _).2
                ⟨connLine_left S hls hne,
                  htgt.symm.trans (by rw [← mul_smul, ← mul_smul]; rfl)⟩)
                (ChainSeq.single _)))⟩
    let c₁ := build q₁ (fun hqq => hp (by rw [hqq]; exact q₁.2))
      (rhoVal S hls φ b p hp q₁.1 q₁.2 • lam) rfl
    let c₂ := build q₂ (fun hqq => hp (by rw [hqq]; exact q₂.2))
      (rhoVal S hls φ b p hp q₁.1 q₁.2 • lam) he'.symm
    have e := hgq.unique_short (MY b lam)
      (MZ p (rhoVal S hls φ b p hp q₁.1 q₁.2 • lam)) 3 (by omega)
      (hd3 _).2 c₁ c₂
    have hsome : (some (Obj.ln (MLine.z q₁.1 (φ b q₁.1 • lam))) :
        Option (Obj (MPoint P B Λ) (MLine P Λ))) =
      some (Obj.ln (MLine.z q₂.1 (φ b q₂.1 • lam))) :=
      congrArg
        (fun l : List (Obj (MPoint P B Λ) (MLine P Λ)) => l.tail.head?) e
    have hpair : q₁.1 = q₂.1 ∧ φ b q₁.1 • lam = φ b q₂.1 • lam := by
      simpa using hsome
    exact Subtype.ext hpair.1
  · -- main.tex line 220-221, existence half: read $q$ off the $3$-chain
    obtain ⟨c⟩ := (hd3 nu).1
    obtain ⟨m₁, m₂, hm₁, hm₂, hm₃, -⟩ := c.three_shape
    cases m₁ with
    | pt wp => exact ((not_objInc_pt_pt _ _) hm₁).elim
    | ln wl =>
      cases wl with
      | z q lam₁ =>
        obtain ⟨hbq, hlam₁⟩ := (mi_y_iff S φ b lam q lam₁).mp hm₁
        cases m₂ with
        | ln wl => exact ((not_objInc_ln_ln _ _) hm₂).elim
        | pt wp =>
          cases wp with
          | x r =>
            -- an $x_r$ middle would force $p = q \mathrm{I}\, b$
            have hrq : r = q := (mi_x_iff S φ r q lam₁).mp hm₂
            have hrp : r = p := (mi_x_iff S φ r p nu).mp hm₃
            have hpq : p = q := hrp.symm.trans hrq
            exact ((hp (by rw [hpq]; exact hbq))).elim
          | y b'' lam₂ =>
            -- main.tex lines 213: $\mu = \varphi(bp)\cdot\lambda_2$ with
            -- $\lambda_2 = \varphi(b'q)^{-1}\cdot\varphi(bq)\cdot\lambda$
            obtain ⟨hb''q, hlam₁'⟩ := (mi_y_iff S φ b'' lam₂ q lam₁).mp hm₂
            obtain ⟨hpb'', hnu⟩ := (mi_y_iff S φ b'' lam₂ p nu).mp hm₃
            refine ⟨⟨q, hbq⟩, ?_⟩
            show rhoVal S hls φ b p hp q hbq • lam = nu
            have hne : p ≠ q := fun he => hp (by rw [he]; exact hbq)
            -- the chain's $b''$ is the connecting line of $p$ and $q$
            have hconn : connLine S hls hne = b'' :=
              (connLine_unique S hls hne hpb'' hb''q).symm
            rw [show rhoVal S hls φ b p hp q hbq =
                  φ (connLine S hls hne) p * (φ (connLine S hls hne) q)⁻¹
                    * φ b q from rfl, hconn, hnu,
              mul_smul, mul_smul, ← hlam₁, hlam₁', inv_smul_smul]

/-- **Theorem 5, item 2** (main.tex lines 197 and 227): for every $b$, the
set $\mathscr{P}_b$ is in bijection with $\Lambda$. -/
theorem thm5_item2 (hls : S.IsLinearSpace)
    (hgq : (constructionM (Λ := Λ) S φ).IsGenNGon 4) (b : B) [Nonempty Λ] :
    Nonempty ({q : P // S.Incident q b} ≃ Λ) := by
  obtain ⟨p, hp⟩ := exists_pt_not_on_line S hls b
  exact ⟨Equiv.ofBijective _
    (thm5_converse S φ hls hgq b p hp (Classical.arbitrary _))⟩

/-- **Theorem 5, item 1**: $X = \{x_p\}$ is an ovoid of $\mathfrak{M}
(\Gamma,\varphi)$ (main.tex lines 196 and 225). Unconditional: each line
$z_{q,\mu}$ meets $X$ in exactly $x_q$. -/
theorem thm5_item1 :
    IsOvoidOf (constructionM (Λ := Λ) S φ) {mp | ∃ q : P, mp = MPoint.x q} := by
  intro ml
  cases ml with
  | z q mu =>
      refine ⟨MPoint.x q, ⟨⟨q, rfl⟩, MI.xz q mu⟩, ?_⟩
      -- main.tex line 225 ("clear from Construction 𝔐"): $z_{q,\mu}$ meets
      -- $X$ only in $x_q$, since $x_p \mathrm{I}' z_{q,\mu}$ iff $p = q$.
      intro mp' hpair
      simp only [Set.mem_setOf_eq] at hpair
      obtain ⟨t, rfl⟩ := hpair.1
      have htq : t = q := (mi_x_iff S φ t q mu).mp hpair.2
      rw [htq]

/-! ## Forward direction of Theorem 5 -/

section Fwd

variable [Nonempty Λ]

/-- Every point-object of 𝔐 is incident with some line-object (main.tex
line 205: "by Construction 𝔐 we have no isolated objects"). -/
theorem exists_mi_line (hls : S.IsLinearSpace) (mp : MPoint P B Λ) :
    ∃ ml : MLine P Λ, MI S φ mp ml := by
  cases mp with
  | x p => exact ⟨MLine.z p (Classical.arbitrary _), MI.xz p _⟩
  | y b la =>
    obtain ⟨u₁, u₂, -, -, hu₂⟩ := hls.two_pts b
    exact ⟨MLine.z u₂ (φ b u₂ • la), MI.yz hu₂ rfl⟩

omit [Nonempty Λ] in
/-- Missing-case existence: nonincident $y_{b,\lambda}$, $z_{p,\mu}$ pairs
are joined by a $3$-chain, using $\rho_{b,p,\lambda}$-surjectivity
(main.tex lines 211-213). -/
theorem chain_three_missing
    (hbij : ∀ (b : B) (p : P) (hp : ¬ S.Incident p b) (mu : Λ),
      Function.Bijective (rhoLam S hls φ b p hp mu))
    (hls : S.IsLinearSpace) (b : B) (la : Λ) (p : P) (mu : Λ)
    (hp : ¬ S.Incident p b) :
    Nonempty (Chain (constructionM (Λ := Λ) S φ) 3 (MY b la) (MZ p mu)) := by
  obtain ⟨q, hq⟩ := (hbij b p hp la).2 mu
  have hne : p ≠ q.1 := fun he => hp (by rw [he]; exact q.2)
  refine ⟨⟨[MY b la, MZ q.1 (φ b q.1 • la),
      MY (connLine S hls hne)
        ((φ (connLine S hls hne) q.1)⁻¹ • (φ b q.1 • la)), MZ p mu],
    by simp, rfl, by simp,
    ChainSeq.cons ((mi_y_iff S φ b la q.1 _).2 ⟨q.2, rfl⟩)
      (ChainSeq.cons ((mi_y_iff S φ (connLine S hls hne) _ q.1 _).2
          ⟨connLine_right S hls hne, by simp [smul_inv_smul]⟩)
        (ChainSeq.cons ((mi_y_iff S φ (connLine S hls hne) _ p _).2
          ⟨connLine_left S hls hne,
            by rw [← mul_smul, ← mul_smul]; exact hq.symm⟩)
          (ChainSeq.single _)))⟩⟩

omit [Nonempty Λ] in
/-- Point-to-line distances inside 𝔐 are at most 3 (Lemma 3 items 1-4
existence halves plus the missing case; main.tex lines 205, 209-217). -/
theorem distLe_three_pt_ln
    (hbij : ∀ (b : B) (p : P) (hp : ¬ S.Incident p b) (mu : Λ),
      Function.Bijective (rhoLam S hls φ b p hp mu))
    (hls : S.IsLinearSpace) (mp : MPoint P B Λ) (ml : MLine P Λ) :
    DistLe (constructionM (Λ := Λ) S φ) 3 (Obj.pt mp) (Obj.ln ml) := by
  cases mp with
  | x p => exact distLe_mx_mz S φ hls p _ _
  | y b la =>
    cases ml with
    | z p mu =>
      by_cases hbp : S.Incident p b
      · exact distLe_my_mz_incident S φ b la p mu hbp
      · exact ⟨3, le_refl _, chain_three_missing S φ hbij hls b la p mu hbp⟩

/-- All pairs of objects of 𝔐 lie at distance ≤ 4 under the ρ-hypotheses
(main.tex lines 205-207: route same-sort pairs through an object incident
with the second one). -/
theorem distLe_four
    (hbij : ∀ (b : B) (p : P) (hp : ¬ S.Incident p b) (mu : Λ),
      Function.Bijective (rhoLam S hls φ b p hp mu))
    (hls : S.IsLinearSpace) (u v : Obj (MPoint P B Λ) (MLine P Λ)) :
    DistLe (constructionM (Λ := Λ) S φ) 4 u v := by
  match u, v with
  | .pt mp, .ln ml =>
      exact DistLe.weaken (constructionM (Λ := Λ) S φ) (by omega)
        (distLe_three_pt_ln S φ hbij hls mp ml)
  | .ln ml, .pt mp =>
      exact DistLe.weaken (constructionM (Λ := Λ) S φ) (by omega)
        (DistLe.symm (constructionM (Λ := Λ) S φ)
          (distLe_three_pt_ln S φ hbij hls mp ml))
  | .pt mp, .pt mp' =>
      obtain ⟨ml, hml⟩ := exists_mi_line S φ hls mp'
      exact DistLe.snoc (constructionM (Λ := Λ) S φ)
        (DistLe.weaken (constructionM (Λ := Λ) S φ) (by omega)
          (distLe_three_pt_ln S φ hbij hls mp ml))
        (show (constructionM (Λ := Λ) S φ).ObjInc (Obj.ln ml) (Obj.pt mp')
          from hml)
  | .ln ml, .ln ml' =>
      cases ml' with
      | z q mu =>
        exact DistLe.snoc (constructionM (Λ := Λ) S φ)
          (DistLe.weaken (constructionM (Λ := Λ) S φ) (by omega)
            (DistLe.symm (constructionM (Λ := Λ) S φ)
              (distLe_three_pt_ln S φ hbij hls (MPoint.x q) ml)))
          (show (constructionM (Λ := Λ) S φ).ObjInc
              (Obj.pt (MPoint.x q)) (Obj.ln (MLine.z q mu))
            from MI.xz q mu)

omit [Nonempty Λ] in
/-- Uniqueness of the $3$-chain from nonincident $y_{b,\lambda}$ to
$z_{p,\mu}$, via $\rho_{b,p,\lambda}$-injectivity (main.tex lines 215-217). -/
theorem unique_three_missing
    (hbij : ∀ (b : B) (p : P) (hp : ¬ S.Incident p b) (mu : Λ),
      Function.Bijective (rhoLam S hls φ b p hp mu))
    (hls : S.IsLinearSpace) (b : B) (la : Λ) (p : P) (mu : Λ)
    (hp : ¬ S.Incident p b)
    (c₁ c₂ : Chain (constructionM (Λ := Λ) S φ) 3 (MY b la) (MZ p mu)) :
    c₁.seq = c₂.seq := by
  have hneQ : ∀ q : {q : P // S.Incident q b}, p ≠ q.1 :=
    fun q he => hp (by rw [he]; exact q.2)
  have norm : ∀ c : Chain (constructionM (Λ := Λ) S φ) 3 (MY b la) (MZ p mu),
      ∃ q : {q : P // S.Incident q b},
        rhoVal S hls φ b p hp q.1 q.2 • la = mu ∧
        c.seq = [MY b la, MZ q.1 (φ b q.1 • la),
          MY (connLine S hls (hneQ q))
            ((φ (connLine S hls (hneQ q)) q.1)⁻¹ • (φ b q.1 • la)),
          MZ p mu] := by
    intro c
    obtain ⟨m₁, m₂, h1, h2, h3, hs⟩ := c.three_shape
    cases m₁ with
    | pt wp => exact ((not_objInc_pt_pt _ _) h1).elim
    | ln wl =>
      cases wl with
      | z qq lam₁ =>
        obtain ⟨hbqq, heq1⟩ := (mi_y_iff S φ b la qq lam₁).mp h1
        have hne : p ≠ qq := fun he => hp (by rw [he]; exact hbqq)
        cases m₂ with
        | ln wl => exact ((not_objInc_ln_ln _ _) h2).elim
        | pt wp =>
          cases wp with
          | x r =>
            -- an $x_r$ middle would force $p = qq \mathrm{I}\, b$
            have hr1 : r = qq := (mi_x_iff S φ r qq lam₁).mp h2
            have hr2 : r = p := (mi_x_iff S φ r p mu).mp h3
            exact ((hp (by rw [hr2.symm.trans hr1]; exact hbqq))).elim
          | y b'' lam₂ =>
            obtain ⟨hb''q, heq2⟩ := (mi_y_iff S φ b'' lam₂ qq lam₁).mp h2
            obtain ⟨hb''p, heq3⟩ := (mi_y_iff S φ b'' lam₂ p mu).mp h3
            have hb''c : b'' = connLine S hls hne :=
              connLine_unique S hls hne hb''p hb''q
            rw [hb''c] at heq2 heq3
            have hlam₂ : lam₂ = (φ (connLine S hls hne) qq)⁻¹ • lam₁ := by
              have hc := congrArg
                (fun x : Λ => (φ (connLine S hls hne) qq)⁻¹ • x) heq2
              simpa using hc.symm
            refine ⟨⟨qq, hbqq⟩, ?_, ?_⟩
            · -- main.tex lines 211-217: $\mu = \varphi_w \cdot \lambda$
              rw [show rhoVal S hls φ b p hp qq hbqq =
                    φ (connLine S hls hne) p * (φ (connLine S hls hne) qq)⁻¹
                      * φ b qq from rfl, mul_smul, mul_smul, ← heq1,
                    ← hlam₂]
              exact heq3.symm
            · rw [hs, hb''c, heq1, hlam₂, heq1]
  obtain ⟨q₁, hv₁, hs₁⟩ := norm c₁
  obtain ⟨q₂, hv₂, hs₂⟩ := norm c₂
  have hq12 : q₁ = q₂ := (hbij b p hp la).1 (hv₁.trans hv₂.symm)
  subst hq12
  rw [hs₁, hs₂]

end Fwd

/-- **Theorem 5** (`thm_gq_rho`): $\mathfrak{M}(\Gamma,\varphi)$ is a
generalized quadrangle if and only if every $\rho_{b,p,\lambda}$ is bijective
(main.tex lines 193-199, proof at 202-230). Forward direction: `dist_le` by
`distLe_four`; `unique_short` for $k \le 1$ trivially, $k = 2$ via Lemma 4,
$k = 3$ by endpoint dispatch to Lemma 3 items 2/4 and the missing case.
Converse direction: `thm5_converse`. -/
theorem thm_gq_rho (hls : S.IsLinearSpace) [Nonempty Λ] :
    (constructionM (Λ := Λ) S φ).IsGenNGon 4 ↔
      ∀ (b : B) (p : P) (hp : ¬ S.Incident p b) (mu : Λ),
        Function.Bijective (rhoLam S hls φ b p hp mu) := by
  constructor
  · exact thm5_converse S φ hls
  · intro hbij
    refine ⟨fun u v => distLe_four S φ hbij hls u v, ?_⟩
    intro u v k hk hmin c₁ c₂
    match k, c₁, c₂ with
    | 0, c₁, c₂ => rw [c₁.zero_seq.1, c₂.zero_seq.1]
    | 1, c₁, c₂ => rw [c₁.one_seq.1, c₂.one_seq.1]
    | 2, c₁, c₂ =>
        exact lem4 S φ hls c₁.two_tag_eq ⟨⟨c₁⟩, hmin⟩ c₁ c₂
    | 3, c₁, c₂ =>
      match u, v, c₁, c₂, hmin with
      | .pt (.x p), .ln (.z q lam), c₁, c₂, hmin =>
          have hpq : p ≠ q := by
            intro he
            subst he
            exact (hmin 1 (by omega)).elim ⟨[MX p, MZ p lam], rfl, rfl, rfl,
              ChainSeq.cons ((mi_x_iff S φ p p lam).mpr rfl)
                (ChainSeq.single _)⟩
          exact unique_three_xz S φ hls p q lam hpq c₁ c₂
      | .pt (.y b la), .ln (.z p mu), c₁, c₂, hmin =>
          by_cases hbp : S.Incident p b
          · have hne : mu ≠ φ b p • la := by
              intro he
              exact (hmin 1 (by omega)).elim ⟨[MY b la, MZ p mu], rfl, rfl, rfl,
                ChainSeq.cons ((mi_y_iff S φ b la p mu).mpr ⟨hbp, he⟩)
                  (ChainSeq.single _)⟩
            exact unique_three_yz_incident S φ hls b la p mu hbp hne hmin c₁ c₂
          · exact unique_three_missing S φ hbij hls b la p mu hbp c₁ c₂
      | .ln (.z p mu), .pt (.x q), c₁, c₂, hmin =>
          have hpq : q ≠ p := by
            intro he
            subst he
            exact (hmin 1 (by omega)).elim ⟨[MZ q mu, MX q], rfl, rfl, rfl,
              ChainSeq.cons ((mi_x_iff S φ q q mu).mpr rfl)
                (ChainSeq.single _)⟩
          have hrev : c₁.seq.reverse = c₂.seq.reverse :=
            unique_three_xz S φ hls q p mu hpq
              (Chain.rev (constructionM (Λ := Λ) S φ) c₁)
              (Chain.rev (constructionM (Λ := Λ) S φ) c₂)
          rw [List.reverse_inj] at hrev
          exact hrev
      | .ln (.z p mu), .pt (.y b la), c₁, c₂, hmin =>
          by_cases hbp : S.Incident p b
          · have hne : mu ≠ φ b p • la := by
              intro he
              exact (hmin 1 (by omega)).elim ⟨[MZ p mu, MY b la], rfl, rfl, rfl,
                ChainSeq.cons ((mi_y_iff S φ b la p mu).mpr ⟨hbp, he⟩)
                  (ChainSeq.single _)⟩
            have hmin' : ∀ j, j < 3 →
                IsEmpty (Chain (constructionM (Λ := Λ) S φ) j
                  (MY b la) (MZ p mu)) :=
              fun j hj => ⟨fun c =>
                IsEmpty.elim' (hmin j hj)
                  (Chain.rev (constructionM (Λ := Λ) S φ) c)⟩
            have hrev : c₁.seq.reverse = c₂.seq.reverse :=
              unique_three_yz_incident S φ hls b la p mu hbp hne hmin'
                (Chain.rev (constructionM (Λ := Λ) S φ) c₁)
                (Chain.rev (constructionM (Λ := Λ) S φ) c₂)
            rw [List.reverse_inj] at hrev
            exact hrev
          · have hmin' : ∀ j, j < 3 →
                IsEmpty (Chain (constructionM (Λ := Λ) S φ) j
                  (MY b la) (MZ p mu)) :=
              fun j hj => ⟨fun c =>
                IsEmpty.elim' (hmin j hj)
                  (Chain.rev (constructionM (Λ := Λ) S φ) c)⟩
            have hrev : c₁.seq.reverse = c₂.seq.reverse :=
              unique_three_missing S φ hbij hls b la p mu hbp
                (Chain.rev (constructionM (Λ := Λ) S φ) c₁)
                (Chain.rev (constructionM (Λ := Λ) S φ) c₂)
            rw [List.reverse_inj] at hrev
            exact hrev
      | .pt _, .pt _, c₁, c₂, _ =>
          exact absurd c₁.three_tag_ne (by simp [Obj.tag])
      | .ln _, .ln _, c₁, c₂, _ =>
          exact absurd c₁.three_tag_ne (by simp [Obj.tag])

end Thm5

end McCulloch25_1
