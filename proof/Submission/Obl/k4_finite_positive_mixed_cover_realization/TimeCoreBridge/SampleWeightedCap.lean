-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/SampleWeightedCap.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.SampleCaps
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.OriginalMassTransport

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
open MeasureTheory MvPolynomial Set

section Sample
variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
  {Mpr Dpr : ℕ} {d₁ ρ gain δ₀ τ ε : ℝ} {m : ℕ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
  {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ}
  {A : Fin C → Set (ℕ × (Fin 6 → ℝ))} {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {Mg Dg : ℕ} {i : ℕ} {h : ℝ} {n : ℕ} {old : Fin n → Fin C}
  {R' : Fin n → MvPolynomial (Fin 4) ℝ} {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))}
  {V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {q : ℝ}


/-- The original comparison cap commutes with the world weight. No candidate
or packet law is normalized by its own mass. -/
theorem sampleInput_weighted_candidate_group_cap (hNk : 1 ≤ Nk)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q) (a : Fin n)
    (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : (Q (old a)).det ≠ 0) (v0 : EuclideanSpace ℝ (Fin 3)) {radius : ℝ} (hradius : 0 < radius)
    {cov : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hcov : cov ⊆ V a) :
    let U := Nk ^ (4 * ρ * gain * L + 4 * ε)
    let H := Nk ^ (-f q + τ) * (16 * (1 + U ^ 2)) * radius ^ 3 * |(Q (old a)).det| / 2 ^ T i
    (ENNReal.ofReal (ω (γ (old a))) • ((ν (γ (old a))).prod volume).restrict cov).map
      ((groupBase (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) v0 radius) ∘
        obs (B (γ (old a))) (δ Nk L)) ≤
      ENNReal.ofReal (ω (γ (old a)) * H) • volume := by
  have hcap := sampleInput_candidate_group_cap hNk hsi a c u Q hQ v0 hradius hcov
  have hm := (measurable_groupBase (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) v0 radius).comp
    (measurable_obs (B (γ (old a))) (δ Nk L))
  have hω : 0 ≤ ω (γ (old a)) := hsi.1.2.1 _
  dsimp only
  have hw := weighted_restrict_map_cap _ _ _ _ hm hω hcap
  rwa [Measure.restrict_smul] at hw

end Sample
end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
