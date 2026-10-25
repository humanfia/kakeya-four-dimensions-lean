import Mathlib
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealSeparatedCounts

namespace Submission.Obl.k4_oss_finite_energy_relation

attribute [local instance] Classical.propDecidable

/-- At a slope at least one quarter, a short affine window contains few points. -/
theorem affine_window_card {δ t : ℝ} (hδ : 0 < δ) (ht : (1 : ℝ) / 4 ≤ t)
    (B : Finset ℝ)
    (hsep : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b') (a x : ℝ) :
    ((B.filter (fun b => |x - (a + t * b)| ≤ 16 * δ)).card : ℝ) ≤ 130 := by
  classical
  let F := B.filter (fun b => |x - (a + t * b)| ≤ 16 * δ)
  have htpos : 0 < t := by linarith
  have hball : ∀ b ∈ F, dist b ((x - a) / t) ≤ 64 * δ := by
    intro b hb
    have hwin := (Finset.mem_filter.mp hb).2
    have hid : t * (b - (x - a) / t) = -(x - (a + t * b)) := by
      field_simp; ring
    have hm : t * |b - (x - a) / t| ≤ 16 * δ := by
      calc
        t * |b - (x - a) / t| = |t * (b - (x - a) / t)| := by
          rw [abs_mul, abs_of_pos htpos]
        _ = |x - (a + t * b)| := by rw [hid, abs_neg]
        _ ≤ 16 * δ := hwin
    rw [Real.dist_eq]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (abs_nonneg (b - (x - a) / t))]
  have hpack := WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.real_separated_ball_card
    hδ (by positivity : 0 ≤ 64 * δ) F
    (fun b hb b' hb' hne => hsep b (Finset.mem_filter.mp hb).1 b' (Finset.mem_filter.mp hb').1 hne)
    hball
  change (F.card : ℝ) ≤ 130
  nlinarith

end Submission.Obl.k4_oss_finite_energy_relation
