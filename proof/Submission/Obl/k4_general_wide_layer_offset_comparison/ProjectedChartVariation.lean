import Submission.Obl.k4_general_wide_layer_offset_comparison.SourceResolution
import Submission.Obl.k4_general_wide_layer_offset_comparison.PolynomialMatchSheets

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedChartVariation.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MvPolynomial

noncomputable section

/-- A small change in normalized chart coordinates has its explicit
physical cost in time and transverse position. The native hidden coordinate
is never moved. -/
theorem projectedChartPolynomial_variation
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    {B R δ η time q u v b : ℝ} (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hq : 0 < q) (hb : 0 < b) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (htime : q * δ ≤ η) (htrans : (|v| * q + b) * δ ≤ η)
    (hcoeff : ∀ e, |G.coeff e| ≤ B) (x z : Fin 3 → ℝ)
    (hx : ∀ i, |x i| ≤ R)
    (hclose : ∀ i : Fin 2,
      |projectedDomainCoordinates time q u v b x i - z i.castSucc| ≤ δ) :
    |eval ![x 0, x 2] G - eval z (projectedChartPolynomial G time q u v b)| ≤
      54 * B * (R + 1) ^ 4 * η := by
  let y : Fin 3 → ℝ := ![time + q * z 0, x 1,
    u + v * (time + q * z 0) + b * z 1]
  have hc0 : |(x 0 - time) / q - z 0| ≤ δ := hclose 0
  have hc1 : |(x 2 - u - x 0 * v) / b - z 1| ≤ δ := hclose 1
  have ht : x 0 - (time + q * z 0) = q * ((x 0 - time) / q - z 0) := by
    field_simp
    ring
  have hy : x 2 - (u + v * (time + q * z 0) + b * z 1) =
      v * q * ((x 0 - time) / q - z 0) + b * ((x 2 - u - x 0 * v) / b - z 1) := by
    field_simp
    ring
  have hxy : ∀ i, |x i - y i| ≤ η := by
    intro i
    fin_cases i
    · change |x 0 - (time + q * z 0)| ≤ η
      rw [ht, abs_mul, abs_of_pos hq]
      exact (mul_le_mul_of_nonneg_left hc0 hq.le).trans htime
    · change |x 1 - x 1| ≤ η
      simpa using hη
    · change |x 2 - (u + v * (time + q * z 0) + b * z 1)| ≤ η
      rw [hy]
      calc
        _ ≤ |v * q * ((x 0 - time) / q - z 0)| +
            |b * ((x 2 - u - x 0 * v) / b - z 1)| := abs_add_le _ _
        _ = |v| * q * |(x 0 - time) / q - z 0| +
            b * |(x 2 - u - x 0 * v) / b - z 1| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hq, abs_of_pos hb]
        _ ≤ |v| * q * δ + b * δ :=
          add_le_add (mul_le_mul_of_nonneg_left hc0 (mul_nonneg (abs_nonneg _) hq.le))
            (mul_le_mul_of_nonneg_left hc1 hb.le)
        _ = (|v| * q + b) * δ := by ring
        _ ≤ η := htrans
  have hv := projected_predictor_variation G hG hB hR hη hη1 hcoeff x y hx hxy
  simpa [projectedChartPolynomial_value, y] using hv

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The literal common-domain base can be jittered while retaining the
original signal and the original polynomial values as reference. -/
theorem projected_domain_jitter_variation
    {k : ℕ} {B δ η h g b : ℝ} (hK : 1 ≤ p.K k) (hB : 0 ≤ B)
    (hh : 0 < h) (hb : 0 < b) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    (hcoeff : ∀ e, |G.coeff e| ≤ B)
    {ω : α × ℝ} (hω : ω ∈ p.baseGood k) (D : ℤ × ℤ × ℤ)
    (hcode : p.domainCode k h g b ω = D)
    (htime : (32 * h) * δ ≤ η)
    (htrans : (|domainVelocity g D| * (32 * h) + 32 * b) * δ ≤ η)
    (z : Fin 3 → ℝ) (hclose : ∀ i : Fin 2,
      |p.normalizedDomainBase k h g b ω i - z i.castSucc| ≤ δ) :
    |eval ![ω.2, (p.x k ω.1 ω.2) 2] G -
      eval z (projectedChartPolynomial G (domainTime h D) (32 * h)
        (domainIntercept h g b D) (domainVelocity g D) (32 * b))| ≤
      54 * B * (p.K k + 1) ^ 4 * η := by
  have hbase := p.baseGood_base_bound hK hω
  apply projectedChartPolynomial_variation G hG hB hK (by positivity) (by positivity)
    hη hη1 htime htrans hcoeff
    ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] z
  · intro i
    fin_cases i
    · exact hbase 0
    · exact hbase 1
    · exact hbase 2
  · intro i
    rw [p.normalizedDomainBase_on_code hcode] at hclose
    exact hclose i

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
