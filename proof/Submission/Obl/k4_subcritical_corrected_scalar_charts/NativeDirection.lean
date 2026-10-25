/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeDirection.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeOriginalCaps
import Submission.Obl.k4_subcritical_corrected_scalar_charts.FiberGeometry

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set

noncomputable section

/-- A whole-child native norm controls the contact directional slope. The
transverse derivative is paid at h² and the tilt error is O(Kh). -/
theorem horizontal_slope_of_atlas_norm (L : Fin 4 → ℝ) (c : Fin 5 → ℝ)
    {h m t K E : ℝ} (hh : 0 < h) (hK : 0 ≤ K)
    (ht : |t - m| ≤ h) (hc : |c 4 - m| ≤ K * h)
    (hnorm : ∀ z : Fin 3 → ℝ, (∀ e, |atlasFrame h m c z e| ≤ 1) →
      |affineField L z| ≤ E) :
    |L 2 + t * L 3| ≤ 2 * (K + 2) * E / h := by
  let U : (Fin 3 → ℝ) → Fin 3 → ℝ :=
    nativeUnframe h m (c 0) (c 2 + c 4 * c 0) (c 1) (-c 3 - c 4 * c 1) (c 4)
  have hn (u : Fin 3 → ℝ) (hu : ∀ e, |u e| ≤ 1) : |affineField L (U u)| ≤ E := by
    apply hnorm
    intro e
    rw [atlasFrame, show U u = nativeUnframe h m (c 0) (c 2 + c 4 * c 0)
      (c 1) (-c 3 - c 4 * c 1) (c 4) u from rfl,
      nativeFrame_unframe hh.ne']
    exact hu e
  have h0 := hn (0 : Fin 3 → ℝ) (by intro e; simp)
  have h1 := hn (![0, 1, 0] : Fin 3 → ℝ) (by intro e; fin_cases e <;> norm_num)
  have h2 := hn (![0, 0, 1] : Fin 3 → ℝ) (by intro e; fin_cases e <;> norm_num)
  have htd : |t - c 4| ≤ (K + 1) * h := by
    calc
      _ ≤ |t - m| + |m - c 4| := abs_sub_le _ _ _
      _ ≤ h + K * h := add_le_add ht (by simpa only [abs_sub_comm] using hc)
      _ = _ := by ring
  have hx0 : |(L 0 + L 1 * m) + L 2 * (c 0 + m * c 1) +
      L 3 * (c 2 + m * c 3 + c 4 * (c 0 + m * c 1))| ≤ E := by
    convert h0 using 1 <;> dsimp [U, nativeUnframe, affineField] <;> congr 1 <;> ring
  have hx1 : |(L 0 + L 1 * m) + L 2 * (c 0 + m * c 1 + h) +
      L 3 * ((c 2 + m * c 3 + c 4 * (c 0 + m * c 1)) + c 4 * h)| ≤ E := by
    convert h1 using 1 <;> simp [U, nativeUnframe, affineField] <;> congr 1 <;> ring
  have hx2 : |(L 0 + L 1 * m) + L 2 * (c 0 + m * c 1) +
      L 3 * ((c 2 + m * c 3 + c 4 * (c 0 + m * c 1)) + h ^ 2)| ≤ E := by
    convert h2 using 1 <;> simp [U, nativeUnframe, affineField] <;> congr 1 <;> ring
  have hs := horizontal_slope_of_three_values hh
    (show 0 ≤ K + 1 by linarith) htd hx0 hx1 hx2
  convert hs using 1 <;> ring

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
