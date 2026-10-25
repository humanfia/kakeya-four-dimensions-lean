-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.LocalEstimates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Local

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- Endpoint constants at the bottom scale separate from the geometric local factor. -/
theorem endpoint_frame_identity {d r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (a ω t θ σ N : ℝ) (hN : 0 ≤ N) :
    a * r ^ (ω + t) * (d ^ (-θ))⁻¹ * (N * r ^ 2) *
      ((d ^ (-θ)) ^ (-(3 / 2 : ℝ)) * d ^ (-θ) * (N * r)) ^ (-σ) =
    a * d ^ (θ * (1 - σ / 2)) * r ^ t * volumeFactor σ ω r N := by
  rw [Real.mul_rpow (by positivity : 0 ≤ (d ^ (-θ)) ^ (-(3 / 2 : ℝ)) * d ^ (-θ))
    (mul_nonneg hN hr.le)]
  rw [← Real.rpow_mul hd.le, ← Real.rpow_add hd, ← Real.rpow_mul hd.le]
  rw [← Real.rpow_neg hd.le, neg_neg]
  have hp : d ^ θ * d ^ ((-θ * -(3 / 2 : ℝ) + -θ) * -σ) =
      d ^ (θ * (1 - σ / 2)) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  dsimp [volumeFactor]
  rw [Real.rpow_add hr]
  calc
    _ = a * (d ^ θ * d ^ ((-θ * -(3 / 2 : ℝ) + -θ) * -σ)) * r ^ t *
        (r ^ ω * (N * r ^ 2) * (N * r) ^ (-σ)) := by ring
    _ = _ := by rw [hp]

/-- Uniform endpoint lower bounds for normalized local families on large gaps. -/
theorem Endpoint.on_large_gap {σ ω : ℝ} (hE : Endpoint σ ω) (hσ : 0 ≤ σ)
    {loss h : ℝ} (hloss : 0 < loss) (hh : 0 < h) :
    ∃ a : ℝ, 0 < a ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
    ∀ d r : ℝ, 0 < d → d ≤ 1 → d ≤ r → r ≤ 1 / 100 → r ≤ d ^ h →
      ∀ n x v Y, FrameAdmissible d r θ n x v Y →
      ENNReal.ofReal (a * d ^ loss * volumeFactor σ ω r n) ≤ volume (⋃ i, Y i) := by
  obtain ⟨a, ha, η, hη, hbound⟩ := hE (loss / 2) (by positivity)
  let θ : ℝ := min 1 (min (loss / 2) (h * η))
  have hθ : 0 < θ := lt_min zero_lt_one (lt_min (by positivity) (mul_pos hh hη))
  have hθloss : θ ≤ loss / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hθη : θ ≤ h * η := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨a, ha, θ, hθ, min_le_left _ _, ?_⟩
  intro d r hd hd1 hdr hr100 hgap n x v Y hA
  have hr : 0 < r := hd.trans_le hdr
  have herror : 1 ≤ d ^ (-θ) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_nonpos.mpr hθ.le)
  have hlocal := hA.to_admissible (local_density_power hd hd1 hr.le hη.le hgap hθη)
  have hv := hbound r hr hr100 (d ^ (-θ)) (d ^ (-θ)) herror herror n x v Y hlocal
  rw [endpoint_frame_identity hd hr a ω (loss / 2) θ σ n (Nat.cast_nonneg n)] at hv
  apply le_trans (ENNReal.ofReal_le_ofReal _) hv
  have hp : d ^ loss ≤ d ^ (θ * (1 - σ / 2)) * r ^ (loss / 2) := by
    calc
      d ^ loss ≤ d ^ (θ + loss / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
      _ = d ^ θ * d ^ (loss / 2) := Real.rpow_add hd _ _
      _ ≤ d ^ (θ * (1 - σ / 2)) * r ^ (loss / 2) := by
        apply mul_le_mul
        · exact Real.rpow_le_rpow_of_exponent_ge hd hd1 (by nlinarith)
        · exact Real.rpow_le_rpow hd.le hdr (by positivity)
        · positivity
        · positivity
  have hfactor : 0 ≤ volumeFactor σ ω r n := by dsimp [volumeFactor]; positivity
  calc
    a * d ^ loss * volumeFactor σ ω r n ≤
        a * (d ^ (θ * (1 - σ / 2)) * r ^ (loss / 2)) * volumeFactor σ ω r n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp ha.le) hfactor
    _ = _ := by ring

end WangZahlLot.Obl.wz_multiscale_finite_tower
