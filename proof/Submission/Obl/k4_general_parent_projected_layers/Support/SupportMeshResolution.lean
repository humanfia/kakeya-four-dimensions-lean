/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/SupportMeshResolution.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.ParentZoom
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! A single physical mesh resolves every row of the normalized true packet. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

noncomputable section

theorem supportZoom_mesh_resolution {K q g delta : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (hg : 0 < g) (hg1 : g ≤ 1) (hd : 0 ≤ delta)
    (tmid z₀ : ℝ) (c : Fin 5 → ℝ) (hc₃ : |c 3| ≤ K) (hc₄ : |c 4| ≤ K)
    (e : Fin 3) :
    (∑ j, |(supportZoom K q g tmid z₀ c).baseMatrix e j| * delta) ≤ delta / (q * g) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hqg : 0 < q * g := mul_pos hq hg
  have hdenq : 0 < 32 * K * q := by positivity
  have hdenw : 0 < 16 * K * q * g := by positivity
  have hmajor : (32 * K * q)⁻¹ * delta ≤ delta / (q * g) := by
    have hg32 : g ≤ 32 * K := hg1.trans (by linarith)
    have hdenle : q * g ≤ 32 * K * q := by
      nlinarith [mul_le_mul_of_nonneg_right hg32 hq.le]
    calc
      _ = delta / (32 * K * q) := by rw [div_eq_mul_inv]; ring
      _ ≤ _ := div_le_div_of_nonneg_left hd hqg hdenle
  fin_cases e
  · simpa [Zoom.baseMatrix, supportZoom, Fin.sum_univ_three, abs_inv, abs_of_pos hdenq, abs_of_pos hK0, abs_of_pos hq] using hmajor
  · simpa [Zoom.baseMatrix, supportZoom, Fin.sum_univ_three, abs_inv, abs_of_pos hdenq, abs_of_pos hK0, abs_of_pos hq] using hmajor
  · have hsum : (|c 3| / (16 * K * q * g)) * delta +
        (|c 4| / (16 * K * q * g)) * delta + (16 * K * q * g)⁻¹ * delta ≤ delta / (q * g) := by
      apply (le_div_iff₀ hqg).mpr
      have heq : ((|c 3| / (16 * K * q * g)) * delta +
          (|c 4| / (16 * K * q * g)) * delta + (16 * K * q * g)⁻¹ * delta) * (q * g) =
            (|c 3| + |c 4| + 1) * delta / (16 * K) := by
        field_simp <;> ring
      rw [heq]
      apply (div_le_iff₀ (by positivity : 0 < 16 * K)).mpr
      have hsumc : |c 3| + |c 4| + 1 ≤ 16 * K := by linarith
      simpa only [mul_comm delta] using mul_le_mul_of_nonneg_right hsumc hd
    simpa [Zoom.baseMatrix, supportZoom, Fin.sum_univ_three, abs_div, abs_neg,
      abs_inv, abs_of_pos hdenw, abs_of_pos hK0, abs_of_pos hq, abs_of_pos hg] using hsum

end

end Submission.Obl.k4_general_parent_projected_layers
