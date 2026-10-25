import Submission.Obl.k4_clean_cover_graph_atlas.CapNumerics
import Mathlib

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory

/-- The uniform relative projection parameter belongs to `(0,1]`. -/
theorem projection_ratio_pos_le_one {N loss κ : ℝ}
    (hN : 1 ≤ N) (hloss : 0 ≤ loss) (hκ : 1 ≤ κ) :
    0 < N ^ (-loss) / (64 * κ) ∧ N ^ (-loss) / (64 * κ) ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have hκ0 : 0 < κ := by linarith
  have hp : N ^ (-loss) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hN (neg_nonpos.mpr hloss)
  exact ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith)⟩

/-- The numeric projection floor becomes a floor for the unchanged original
candidate law. The full original prior mass is used on the right of its input floor. -/
theorem original_candidate_projection_mass_floor {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (A : Set X) (mass : ENNReal) (hAfinite : ν A ≠ ⊤)
    {N J len κ d h ρ gain L ε δ₀ τ fri fq : ℝ}
    (hN : 1 ≤ N) (hJ : 0 ≤ J) (hlen : 0 < len) (hκ : 0 < κ)
    (hprior : ENNReal.ofReal (N ^ (-fri) * J / κ) ≤ ν A)
    (hprofile : d * h * L - 5 * δ₀ * L ≤ fq - fri)
    (hfloor : ENNReal.ofReal (N ^ (-((d * h + 4 * ρ * gain) * L + 4 * ε)) /
      (2 * len)) * ν A ≤ mass) :
    ENNReal.ofReal
      ((32 * N ^ (-fq + τ + 2 * (4 * ρ * gain * L + 4 * ε)) * (J / len)) *
        (N ^ (-((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ)) / (64 * κ))) ≤ mass := by
  have hN0 : 0 < N := by linarith
  have hp := ENNReal.toReal_mono hAfinite hprior
  rw [ENNReal.toReal_ofReal (by positivity)] at hp
  have hb := original_candidate_projection_floor (ρ := ρ) (gain := gain) (ε := ε) (τ := τ)
    hN hJ hlen hκ hp hprofile
  calc
    _ ≤ ENNReal.ofReal
        (N ^ (-((d * h + 4 * ρ * gain) * L + 4 * ε)) / (2 * len) * (ν A).toReal) :=
      ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal (N ^ (-((d * h + 4 * ρ * gain) * L + 4 * ε)) /
        (2 * len)) * ν A := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hAfinite]
    _ ≤ mass := hfloor

end Submission.Obl.k4_clean_cover_graph_atlas
