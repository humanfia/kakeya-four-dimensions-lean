import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Rounding
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.OriginalMarking

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open MeasureTheory Set
open scoped ENNReal

/-- Quantitative finite data before the observation-density estimates. -/
structure RoundedMarkedData (N K s m : ℝ) (α : Type) [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (b : α → Coeff) where
  H : ℕ
  J : ℕ
  tag : α → Fin H
  b₀ : Fin H → Coeff
  w : Fin H → ℝ
  mark : Fin H → Fin J → Bool
  tag_measurable : Measurable tag
  weight_eq : ∀ j, ENNReal.ofReal (w j) = ν {l | tag l = j}
  weight_nonneg : ∀ j, 0 ≤ w j
  weight_sum : (∑ j, w j) = 1
  rounding : ∀ l i, |b l i - b₀ (tag l) i| ≤ N ^ (-10 * (m + s + 1))
  coefficient_bound : ∀ j i, |b₀ j i| ≤ K + N ^ (-10 * (m + s + 1))
  coefficient_count : (H : ℝ) ≤ (2 * K / N ^ (-10 * (m + s + 1)) + 2) ^ 5
  time_pos : 1 ≤ J
  time_scale_lower : 1 ≤ (J : ℝ) * N ^ (-m)
  time_scale_upper : (J : ℝ) * N ^ (-m) ≤ 2
  time_count : (J : ℝ) ≤ 2 * (N ^ (-m))⁻¹
  mark_floor : ∀ j z, mark j z = true →
    ENNReal.ofReal (w j / ((J : ℝ) * (2 * K))) ≤ μ (originalCell tag j z)
  mass_lower : ENNReal.ofReal (1 / (2 * K ^ 2)) ≤
    MarkedLaw (N ^ (-m)) H J b₀ w mark univ

theorem exists_rounded_marked_data {N K d s m S U c : ℝ} {angular : Bool}
    (hN : 2 ≤ N) (hK : 1 ≤ K) (hs : 0 < s) (hsm : s < m)
    (α : Type) [MeasurableSpace α] (ν : Measure α) (μ : Measure (α × ℝ))
    (b : α → Coeff) (hinput : MeshInput N K d s m S U α ν μ b c angular) :
    Nonempty (RoundedMarkedData N K s m α ν μ b) := by
  have hNp : 0 < N := by linarith
  have hm : 0 < m := lt_trans hs hsm
  have hδ : 0 < N ^ (-10 * (m + s + 1)) := Real.rpow_pos_of_pos hNp _
  have hσ : 0 < N ^ (-m) := Real.rpow_pos_of_pos hNp _
  have hσ1 : N ^ (-m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  obtain ⟨hb, hprob, hdom, hsupp, hlower, hbound, _⟩ := hinput
  have : IsProbabilityMeasure ν := hprob
  obtain ⟨H, tag, b₀, w, htag, hweight, hw, hsum, hround, hb₀, hH⟩ :=
    finite_coefficient_rounding ν b hb hδ (by linarith) hbound
  obtain ⟨J, hJ, hJlow, hJhigh, hJcount⟩ := exists_time_mesh hσ hσ1
  obtain ⟨mark, hfloor, hmass⟩ := exists_original_marking ν μ (by linarith) hσ
    hdom hsupp hlower hJ tag htag b₀ w hw hsum hweight
  exact ⟨{
    H := H, J := J, tag := tag, b₀ := b₀, w := w, mark := mark
    tag_measurable := htag, weight_eq := hweight, weight_nonneg := hw, weight_sum := hsum
    rounding := hround, coefficient_bound := hb₀, coefficient_count := hH
    time_pos := hJ, time_scale_lower := hJlow, time_scale_upper := hJhigh
    time_count := hJcount, mark_floor := hfloor, mass_lower := hmass }⟩

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
