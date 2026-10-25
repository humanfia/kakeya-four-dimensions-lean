import Submission.Obl.k4_pair_anchor_jet_bins.Interface
import Submission.Obl.k4_algebraic_real_jet_comparison.RealGeometry

namespace Submission.Obl.k4_pair_anchor_jet_bins

open Set Metric

/-- The relative short-time condition puts a Lipschitz source trajectory in the continuation ball. -/
theorem trajectory_point_control {A T q r t t₀ : ℝ} (hq : 1 ≤ q)
    (hr : r ≤ (8 * T)⁻¹) (hfit : r ≤ A⁻¹ / 100)
    (z z₀ : R3) (hz : ‖z - z₀‖ ≤ q * |t - t₀|) (ht : |t - t₀| ≤ r / q) :
    emb z ∈ closedBall (emb z₀) ((8 * T)⁻¹) ∧
      t ∈ Icc (t₀ - A⁻¹ / (100 * q)) (t₀ + A⁻¹ / (100 * q)) := by
  have hq0 : 0 < q := by linarith
  have hstep : q * |t - t₀| ≤ r := by
    simpa only [mul_comm] using (le_div_iff₀ hq0).mp ht
  have hdist : dist (emb z) (emb z₀) = ‖z - z₀‖ := by
    change dist (Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding 3 z)
      (Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding 3 z₀) = _
    rw [(Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding 3).isometry.dist_eq]
    rfl
  refine ⟨by rw [mem_closedBall, hdist]; exact hz.trans (hstep.trans hr), ?_⟩
  have htime : |t - t₀| ≤ A⁻¹ / (100 * q) := by
    calc
      _ ≤ r / q := ht
      _ ≤ (A⁻¹ / 100) / q := (div_le_div_iff_of_pos_right hq0).mpr hfit
      _ = _ := by rw [div_div]
  have hh := abs_le.mp htime
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

end Submission.Obl.k4_pair_anchor_jet_bins
