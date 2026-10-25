-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/ProjectionNumerics.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from LOT tree g-oai-074, obligation o173, session x0598,
-- commit 267b57bc, Submission/Obl/k4_quadratic_cover_to_analytical_atlas/ProjectionNumerics.lean.
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.CapNumerics

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

/-- A common density ceiling and the original packet floor retain a power-sized
projection fraction. The common original scale cancels exactly. -/
theorem power_projection_fraction {N lam H m a b C : ℝ}
    (hN : 0 < N) (hlam : 0 < lam) (hH : 0 < H) (hC : 0 < C)
    (hmass : lam * N ^ a ≤ m) (hcap : H ≤ lam * C * N ^ b) :
    N ^ (a - b) / C ≤ m / H := by
  apply (le_div_iff₀ hH).mpr
  have hp : N ^ (a - b) * N ^ b = N ^ a := by
    rw [← Real.rpow_add hN, sub_add_cancel]
  calc
    _ ≤ (N ^ (a - b) / C) * (lam * C * N ^ b) :=
      mul_le_mul_of_nonneg_left hcap (by positivity)
    _ = lam * (N ^ (a - b) * N ^ b) := by field_simp
    _ = lam * N ^ a := by rw [hp]
    _ ≤ _ := hmass

/-- The per-candidate normalized cap keeps its negative d*h*L factor. This sharper
form must be retained for the projection floor, even when the matching domination
budget later absorbs all small losses into R^epsilon. -/
theorem candidate_single_cap_budget {N d h ρ gain L ε δ0 τtail fri fq τ J κ prior : ℝ}
    (hN : 1 ≤ N) (hslack : 0 ≤ 4 * ρ * gain * L + 4 * ε)
    (hτ : 0 ≤ τ) (hJ : 0 ≤ J) (hκ : 0 < κ) (hp : 0 ≤ prior)
    (hprior : N ^ (-fri) * J / κ ≤ prior)
    (hprofile : d * h * L - 5 * δ0 * L ≤ fq - fri) :
    N ^ (-fq + τtail) * (16 * (1 + (N ^ (4 * ρ * gain * L + 4 * ε)) ^ 2)) * (τ * J) ≤
      (τ * prior) * (32 * κ) *
        N ^ (-d * h * L + (8 * ρ * gain + 5 * δ0) * L + 8 * ε + τtail) := by
  have hh := candidate_cap_prior_cancellation (n := 1) (a := 0) (fq := fq) (τtail := τtail) hN (by norm_num)
    (by simp) hslack hτ hJ hκ hp hprior
  simp only [one_mul, zero_add] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hN
  nlinarith

/-- The half-witness floor and pure-density cap cancel d*h*L, leaving only the
small profile/fit losses. This is the fraction used in the BEFORE-subdivision
discriminant coefficient bound. No old-packet count occurs. -/
theorem candidate_original_projection_fraction
    {N d h ρ gain L ε δ0 τtail fri fq τ J κ prior m : ℝ}
    (hN : 1 ≤ N) (hslack : 0 ≤ 4 * ρ * gain * L + 4 * ε)
    (hτ : 0 < τ) (hJ : 0 < J) (hκ : 0 < κ) (hp : 0 < prior)
    (hprior : N ^ (-fri) * J / κ ≤ prior)
    (hprofile : d * h * L - 5 * δ0 * L ≤ fq - fri)
    (hmass : (τ * prior) * N ^ (-((d * h + 4 * ρ * gain) * L) - 4 * ε) / 2 ≤ m) :
    N ^ (-((12 * ρ * gain + 5 * δ0) * L + 12 * ε + τtail)) / (64 * κ) ≤
      m / (N ^ (-fq + τtail) * (16 * (1 + (N ^ (4 * ρ * gain * L + 4 * ε)) ^ 2)) * (τ * J)) := by
  have hNpos : 0 < N := by linarith
  have hcap := candidate_single_cap_budget (τtail := τtail) hN hslack hτ.le hJ.le hκ hp.le hprior hprofile
  have hcap' : N ^ (-fq + τtail) *
      (16 * (1 + (N ^ (4 * ρ * gain * L + 4 * ε)) ^ 2)) * (τ * J) ≤
      ((τ * prior) / 2) * (64 * κ) *
        N ^ (-d * h * L + (8 * ρ * gain + 5 * δ0) * L + 8 * ε + τtail) := by
    convert hcap using 1 <;> ring
  have hmass' : ((τ * prior) / 2) *
      N ^ (-((d * h + 4 * ρ * gain) * L) - 4 * ε) ≤ m := by
    convert hmass using 1 <;> ring
  have hh := power_projection_fraction hNpos (by positivity) (by positivity) (by positivity)
    hmass' hcap'
  convert hh using 1 <;> congr 2 <;> ring

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
