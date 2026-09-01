import McCulloch25_1.Basic

/-!
# Proposition 6: regular actions reduce the test to rho_{b,p}

McCulloch25-1, Proposition 6.
Source: `/home/chz/src/gamskil/docs/arxiv/2502.01805/main.tex`
lines 236-258 (statement at 236-238, proof at 240-258).
-/

namespace McCulloch25_1

open IncidenceStruct

variable {P B G Λ : Type _} [Group G] [MulAction G Λ]
variable (S : IncidenceStruct P B)

/-- Proposition 6 (`prop_regular`): with the gain group acting **regularly**
(free + transitive, main.tex line 52) on Λ, `rho_{b,p,λ}` is bijective iff
`rho_{b,p}` is (main.tex lines 236-238). Injectivity transfers both ways
because every g acts by a bijection; freeness strips fixed points
(main.tex lines 241-247); transitivity moves targets (lines 249-255).
Restatement delta: the right-hand side unpacks `Function.Bijective` of the
lambda into its injectivity/surjectivity parts over the raw `rhoVal` form,
so no beta-reduction is ever demanded of `rw`. -/
theorem prop_regular (hls : S.IsLinearSpace) (φ : B → P → G)
    (b : B) (p : P) (hp : ¬ S.Incident p b) (mu : Λ)
    (hfree : ∀ ⦃g : G⦄ ⦃nu : Λ⦄, g • nu = nu → g = 1)
    (htrans : ∀ nu₁ nu₂ : Λ, ∃ g : G, g • nu₂ = nu₁) :
    Function.Bijective (rhoLam S hls φ b p hp mu) ↔
      (∀ q₁ q₂ : {q : P // S.Incident q b},
          rhoVal S hls φ b p hp q₁.1 q₁.2 = rhoVal S hls φ b p hp q₂.1 q₂.2 →
          q₁ = q₂) ∧
      (∀ g : G, ∃ q : {q : P // S.Incident q b},
          rhoVal S hls φ b p hp q.1 q.2 = g) := by
  constructor
  · -- main.tex lines 240-247: injectivity transfers by congruence; the
    -- surjectivity transfer (lines 249-255 forward) hits $g \cdot \lambda$
    -- by transitivity and cancels $g^{-1}\cdot(-)$ by freeness.
    rintro ⟨hinj, hsurj⟩
    refine ⟨fun q₁ q₂ he => ?_, fun g => ?_⟩
    · refine hinj ?_
      show rhoVal S hls φ b p hp q₁.1 q₁.2 • mu =
          rhoVal S hls φ b p hp q₂.1 q₂.2 • mu
      rw [he]
    · obtain ⟨q, hq⟩ := hsurj (g • mu)
      have hq' : rhoVal S hls φ b p hp q.1 q.2 • mu = g • mu := hq
      have key : g⁻¹ * rhoVal S hls φ b p hp q.1 q.2 = 1 :=
        hfree (by rw [mul_smul, hq', inv_smul_smul])
      exact ⟨q, (inv_mul_eq_one.mp key).symm⟩
  · -- main.tex lines 241-247: freeness strips $\rho(q_1)^{-1}\rho(q_2)$;
    -- lines 249-255 backward: realize $h$ with $h \cdot \mu = t$, then hit it
    -- with raw surjectivity.
    rintro ⟨hinj, hsurj⟩
    refine ⟨fun q₁ q₂ he => ?_, fun t => ?_⟩
    · have hsmul : rhoVal S hls φ b p hp q₁.1 q₁.2 • mu =
          rhoVal S hls φ b p hp q₂.1 q₂.2 • mu := he
      have key : (rhoVal S hls φ b p hp q₁.1 q₁.2)⁻¹ *
          rhoVal S hls φ b p hp q₂.1 q₂.2 = 1 :=
        hfree (by rw [mul_smul, ← hsmul, inv_smul_smul])
      exact hinj q₁ q₂ (inv_mul_eq_one.mp key)
    · obtain ⟨h, hh⟩ := htrans t mu
      obtain ⟨q, hq⟩ := hsurj h
      refine ⟨q, ?_⟩
      show rhoVal S hls φ b p hp q.1 q.2 • mu = t
      rw [hq, hh]

end McCulloch25_1
