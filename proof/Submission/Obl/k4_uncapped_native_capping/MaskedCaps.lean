import Submission.Obl.k4_uncapped_native_capping.Glue
import Submission.Obl.k4_uncapped_native_capping.PacketCapping
import Submission.Obl.k4_uncapped_native_capping.PreparationParameters

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Filter Set
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section
set_option linter.unusedVariables false

/-- The profile error is fixed before the exact problem. A fixed finite
preparation has power-small original cost and caps every provisional family,
uniformly in its formats and in all sufficiently small geometric losses. -/
theorem maskedCaps
    (ds S η s m U χ : ℝ) (hds : 0 ≤ ds) (hds1 : ds < 1)
    (hS : 0 < S) (hη : 0 < η) (hs : 0 < s) (hs1 : s < 1) (hsm : s < m)
    (hU : 0 < U) (hUm : U < m) (hUη : U ≤ η) (hχ : 0 < χ) :
    MaskedCaps ds S η s m U χ := by
  obtain ⟨ξ, τ, ε, σ, hξ, hτ, hε, hσ, hσχ, hslack⟩ := exists_capping_parameters hχ hS
  refine ⟨ξ, hξ, ?_⟩
  intro N K d W ω ν E P B f g G hprob hprofile
  let p : UWE.Problem := ⟨N, K, 1, d, W, ω, ν, E, P, B, f, g, G⟩
  have hp : p.Valid S η := hprob
  obtain ⟨R, V, hR, hV, hRgrid, hVgrid, hmeas, hcost⟩ :=
    finite_capping_preparation hp rfl hs.le hs1.le hU.le hUη hε hτ
  refine ⟨UWE.densityPreparationBad p S R V τ, hmeas, hcost, σ, hσ, ?_⟩
  intro loss hloss hlossσ M D h
  filter_upwards [eventually_capping_constant hp hχ] with k hk
  intro pack hg ha hc
  apply PacketData.cap_restrictOriginal hp rfl k R V hR hV hs.le hs1.le hε hτ.le
    hRgrid hVgrid hloss.le (hlossσ.trans hσχ) hslack hk ?_ hg ha hc
  intro r hr hrs
  have hlow := (abs_le.mp (hprofile r hr hrs)).1
  change ds * r - ξ ≤ f r - f 0
  linarith

/-- Analytical restriction and finite light-law deletion complete the
frozen analytical capping stage. -/
theorem analyticalCapping : AnalyticalCappingStatement :=
  analyticalCapping_of_maskedCaps maskedCaps

end
end Submission.Obl.k4_uncapped_native_capping
