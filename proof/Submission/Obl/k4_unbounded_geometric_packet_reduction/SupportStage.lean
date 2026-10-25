import Submission.Obl.k4_unbounded_geometric_packet_reduction.SupportSample
import Submission.Obl.k4_unbounded_geometric_packet_reduction.Problems

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open Filter MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The full native oscillation support-completion stage.  The earlier-law
partition exponent is chosen first, then its scalar tolerance, and then one
original problem whose format is fixed before every actual chart loss. -/
theorem supportCompletionStage : SupportCompletionStatement := by
  intro hV ds kr S η hds hds1 hprep
  obtain ⟨Cpart, hCpart, hpieces⟩ := hV.support_pieces
  obtain ⟨s, m, U, hs, hs1, hsm, hU, hUm, hprep⟩ := hprep
  refine ⟨s, m, U, hs, hs1, hsm, hU, hUm, ?_⟩
  intro χ h t hχ hh ht
  let n : ℝ := ((2 * Cpart + 12 : ℕ) : ℝ)
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ 2 * Cpart + 12 by omega)
  have hnp : 0 < n := by linarith
  let χ₀ : ℝ := min (s / 2) (χ / n)
  have hχ₀ : 0 < χ₀ := lt_min (by positivity) (div_pos hχ hnp)
  have hχ₀s : χ₀ ≤ s := (min_le_left _ _).trans (by linarith)
  have hχscale : χ₀ * n ≤ χ := (le_div_iff₀ hnp).mp (min_le_right _ _)
  have hχ₀χ : χ₀ ≤ χ := by
    have hmul := mul_le_mul_of_nonneg_left hn hχ₀.le
    nlinarith
  obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hv, hd, hH, M, D, hsamples⟩ :=
    hprep χ₀ h t hχ₀ hh ht
  let p : Data := ⟨N, K, 1, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
  have hp : Valid p := hv
  refine ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hv, hd, hH, M, D, ?_⟩
  intro loss hloss
  let loss₀ : ℝ := min (loss / 2) (min (χ / 2) (χ₀ / 2))
  have hloss₀ : 0 < loss₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hleloss : loss₀ ≤ loss / 2 := min_le_left _ _
  have hleχ : loss₀ ≤ χ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hleχ₀ : loss₀ ≤ χ₀ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hlate₁ := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hp.scale_tendsto (show -loss < -loss₀ by linarith) (6 : ℝ)
  have hlate₂ := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hp.scale_tendsto (show -χ < -loss₀ by linarith) (3 : ℝ)
  have hlate₃ := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hp.scale_tendsto (show -χ₀ < -loss₀ by linarith) (3 : ℝ)
  apply ((hsamples loss₀ hloss₀).and_eventually (hlate₁.and (hlate₂.and hlate₃))).mono
  rintro k ⟨hsample, hlate₁, hlate₂, hlate₃⟩
  apply hsample.complete_support
    (fun C R μ b hcert => hpieces (N k) χ₀ ds s m C R μ b (hp.scale_ge_two k) hχ₀s hcert)
    (hp.scale_ge_two k) (fun w => (hp.B_pos k w).le) (by linarith) hχ₀χ hχscale (by linarith)
  linarith

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
