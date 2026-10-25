import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.QuadBounds

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

/-- The original positive-base-mass witness for quadratic graph comparison. -/
def graphGoodRegion (P : MvPolynomial (Fin 2) ℝ) (t₀ q u v w K : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc t₀ (t₀ + q) ∧ |p.2 - (u + v * p.1)| ≤ w ∧
    |MvPolynomial.eval ![p.1, p.2] P| ≤ K}

/-- A current-law base-mass floor controls the original quadratic graph
throughout the enlarged normalized block. The comparison loss is a fixed
polynomial, so it can enter the common tangent subpower allowance. -/
theorem graph_norm_on_block {P : MvPolynomial (Fin 2) ℝ}
    (hP : P.totalDegree ≤ 2) {t₀ q u v w K : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (hw : 0 < w) (hwidth : q ≤ K * w)
    (hvolume : ENNReal.ofReal ((q * (2 * w)) / K) ≤
      volume (graphGoodRegion P t₀ q u v w K))
    {t z : ℝ} (ht : t ∈ Icc t₀ (t₀ + q)) (hz : z ∈ Icc (-2 : ℝ) 2) :
    |MvPolynomial.eval ![t, u + t * v + z * q] P| ≤ 4665600 * K ^ 7 := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hmass : ENNReal.ofReal ((1 / K) * (q * (2 * w))) ≤
      volume {p : ℝ × ℝ | p.1 ∈ Icc t₀ (t₀ + q) ∧
        |p.2 - (u + v * p.1)| ≤ w ∧ |MvPolynomial.eval ![p.1, p.2] P| ≤ K} := by
    have heq : (1 / K) * (q * (2 * w)) = (q * (2 * w)) / K := by ring
    simpa only [graphGoodRegion, heq] using hvolume
  have hnorm := quad_remez_parallelogram (isQuad2_eval P hP) hq hw
    (one_div_pos.mpr hK0) hmass t ht (u + t * v + z * q)
  have hzabs : |z| ≤ 2 := abs_le.mpr hz
  have hdist : |u + t * v + z * q - (u + v * t)| / w ≤ 2 * K := by
    have heq : u + t * v + z * q - (u + v * t) = z * q := by ring
    rw [heq, abs_mul, abs_of_pos hq, div_le_iff₀ hw]
    calc
      |z| * q ≤ 2 * q := mul_le_mul_of_nonneg_right hzabs hq.le
      _ ≤ 2 * (K * w) := mul_le_mul_of_nonneg_left hwidth (by norm_num)
      _ = _ := by ring
  have hsum : 3 + |u + t * v + z * q - (u + v * t)| / w ≤ 5 * K := by linarith
  have hsq : (3 + |u + t * v + z * q - (u + v * t)| / w) ^ 2 ≤ (5 * K) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hsum
  calc
    _ ≤ 186624 * K * (3 + |u + t * v + z * q - (u + v * t)| / w) ^ 2 /
        (1 / K) ^ 4 := hnorm
    _ ≤ 186624 * K * (5 * K) ^ 2 / (1 / K) ^ 4 := by gcongr
    _ = 4665600 * K ^ 7 := by field_simp [hK0.ne']; ring

end Submission.Obl.k4_scalar_guarded_tangent_preparation
