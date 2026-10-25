/- Adapted from this LOT tree, obligation o201, session x0697, commit d395b4346c32,
   Submission/Obl/k4_horizontal_critical_rate_candidates/ContactCellGeometry.lean.
   Existing source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.Inherited.HorizontalNormalization
import Submission.Obl.k4_critical_switching_state_preparation.Inherited.ContactGridIntegration
import Submission.Obl.k4_critical_switching_state_preparation.NormalizedPredictors
import Submission.Obl.k4_critical_switching_state_preparation.Inherited.InterceptBinCount

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set Inherited

noncomputable section

/-- The horizontal reference through a physical point, with prescribed velocity. -/
def cellReference (v : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![p 1 - p 0 * v, p 2 + p 0 * (p 1 - p 0 * v), v]

/-- A normalized grid cell has physical contact volume O(H^4*delta^3).
The transverse width is H^2*delta even though its axis-aligned physical
bounding box can be much larger. -/
theorem normalized_cell_in_contact_box
    (H t₀ z₀ y₀ v₀ K δ : ℝ) (q₀ q : Fin 3 → ℝ)
    (hH : 0 ≤ H) (hK : 0 ≤ K) (_hδ : 0 ≤ δ)
    (ht₀ : |q₀ 0| ≤ 1) (hz₀ : |q₀ 1| ≤ K)
    (hgap : ∀ i, |q i - q₀ i| ≤ δ) :
    horizontalUnframe H t₀ z₀ y₀ v₀ q ∈
      contactOuterBox (horizontalUnframe H t₀ z₀ y₀ v₀ q₀ 0)
        (cellReference v₀ (horizontalUnframe H t₀ z₀ y₀ v₀ q₀))
        (2 * H * δ) (H * δ) ((K + 2) * H ^ 2 * δ) := by
  let p₀ := horizontalUnframe H t₀ z₀ y₀ v₀ q₀
  let p := horizontalUnframe H t₀ z₀ y₀ v₀ q
  have htime : p 0 - p₀ 0 = H * (q 0 - q₀ 0) := by
    dsimp [p, p₀, horizontalUnframe]
    ring
  have hZ : p 1 - referenceZ (cellReference v₀ p₀) (p 0) = H * (q 1 - q₀ 1) := by
    dsimp [p, p₀, horizontalUnframe, referenceZ, cellReference]
    ring
  have hY : contactTransverse (p₀ 0) (cellReference v₀ p₀) p =
      H ^ 2 * ((q 2 - q₀ 2) + q₀ 1 * (q 0 - q₀ 0) - q₀ 0 * (q 1 - q₀ 1)) := by
    dsimp [p, p₀, horizontalUnframe, referenceY, referenceZ, cellReference, contactTransverse]
    ring
  have hsum : |(q 2 - q₀ 2) + q₀ 1 * (q 0 - q₀ 0) - q₀ 0 * (q 1 - q₀ 1)| ≤
      (K + 2) * δ := by
    have hZgap : |q₀ 1 * (q 0 - q₀ 0)| ≤ K * δ := by
      rw [abs_mul]
      exact mul_le_mul hz₀ (hgap 0) (abs_nonneg _) hK
    have htgap : |q₀ 0 * (q 1 - q₀ 1)| ≤ δ := by
      rw [abs_mul]
      exact (mul_le_mul ht₀ (hgap 1) (abs_nonneg _) (by norm_num)).trans_eq (one_mul δ)
    have hh := (abs_sub _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add (hgap 2) hZgap)) htgap)
    nlinarith only [hh]
  apply (mem_contactOuterBox_iff _ _ _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · change |p 0 - p₀ 0| ≤ (2 * H * δ) / 2
    rw [show (2 * H * δ) / 2 = H * δ by ring, htime, abs_mul, abs_of_nonneg hH]
    exact mul_le_mul_of_nonneg_left (hgap 0) hH
  · change |p 1 - referenceZ (cellReference v₀ p₀) (p 0)| ≤ H * δ
    rw [hZ, abs_mul, abs_of_nonneg hH]
    exact mul_le_mul_of_nonneg_left (hgap 1) hH
  · change |contactTransverse (p₀ 0) (cellReference v₀ p₀) p| ≤ (K + 2) * H ^ 2 * δ
    rw [hY, abs_mul, abs_of_nonneg (sq_nonneg H)]
    exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg H)).trans_eq (by ring)

/-- Cover the physical contact cell by a sufficiently fine ORIGINAL uniform
mesh. Its native-cell count keeps the H^4 volume factor. -/
theorem original_grid_count_normalized_cell
    (H t₀ z₀ y₀ v₀ K G δ ξ : ℝ) (q₀ : Fin 3 → ℝ)
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hG : 1 ≤ G) (hξ : 0 < ξ)
    (hξt : ξ ≤ H * δ) (hξZ : 2 * G * ξ ≤ H * δ)
    (hξY : 3 * G * ξ ≤ (K + 2) * H ^ 2 * δ)
    (ht₀ : |q₀ 0| ≤ 1) (hz₀ : |q₀ 1| ≤ K)
    (hm : |horizontalUnframe H t₀ z₀ y₀ v₀ q₀ 0| ≤ 1)
    (hv : |v₀| ≤ G) (hposition : |horizontalUnframe H t₀ z₀ y₀ v₀ q₀ 1| ≤ G)
    (F : Finset (Fin 3 → ℤ))
    (hF : ∀ j ∈ F, ∃ q : Fin 3 → ℝ, (∀ i, |q i - q₀ i| ≤ δ) ∧
      horizontalUnframe H t₀ z₀ y₀ v₀ q ∈ contactGridCell ξ j) :
    (F.card : ℝ) * ξ ^ 3 ≤ 64 * (K + 2) * H ^ 4 * δ ^ 3 := by
  let p₀ := horizontalUnframe H t₀ z₀ y₀ v₀ q₀
  have hcenter : |cellReference v₀ p₀ 0 + p₀ 0 * cellReference v₀ p₀ 2| ≤ G := by
    simpa [cellReference] using hposition
  have hvelocity : |cellReference v₀ p₀ 2| ≤ G := hv
  have hcount := contactGrid_count_rectangle (m := p₀ 0) (H := 2 * H * δ)
    (A := H * δ) (B := (K + 2) * H ^ 2 * δ) (K := G) (δ := ξ)
    (p := cellReference v₀ p₀) (by positivity) (by positivity) (by positivity)
    hG hξ (by convert hξt using 1; ring) hξZ hξY hm hvelocity hcenter F
    (by
      intro j hj
      obtain ⟨q, hgap, hcell⟩ := hF j hj
      exact ⟨horizontalUnframe H t₀ z₀ y₀ v₀ q, hcell,
        normalized_cell_in_contact_box H t₀ z₀ y₀ v₀ K δ q₀ q hH hK hδ ht₀ hz₀ hgap⟩)
  convert hcount using 1
  ring

/-- An exact residual-midpoint bin and one normalized base cell put the
ORIGINAL native hidden value in a short interval. This is the value tested
by the frozen joint caps. -/
theorem native_hidden_value_in_midpoint_cell
    (A : Fin 4 → ℝ) (b : Fin 6 → ℝ) (q₀ : Fin 3 → ℝ)
    (H t₀ z₀ y₀ v₀ tm t S δ a err : ℝ) (j : ℤ)
    (hH : 0 < H) (hS : 0 ≤ S) (ha : 0 < a)
    (hA : ∀ e : Fin 3, |normalizedPredictor H t₀ z₀ y₀ v₀ A e.succ| ≤ S)
    (hgap : ∀ i, |horizontalFrame H t₀ z₀ y₀ v₀ (nativeHorizontalLine b t) i - q₀ i| ≤ δ)
    (hslope : |affineResidualSlope A b| ≤ err) (htime : |t - tm| ≤ H)
    (hbin : ⌊(affineResidualIntercept A b + tm * affineResidualSlope A b) / a⌋ = j) :
    |(b 2 + t * b 5) -
      (affineBaseEval (normalizedPredictor H t₀ z₀ y₀ v₀ A) q₀ + a * j)| ≤
        3 * S * δ + a + H * err := by
  let q := horizontalFrame H t₀ z₀ y₀ v₀ (nativeHorizontalLine b t)
  let C := normalizedPredictor H t₀ z₀ y₀ v₀ A
  have hpred := affineBaseEval_mesh_gap C q q₀ S δ hS hA hgap
  have hround := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error ha
    (affineResidualIntercept A b + tm * affineResidualSlope A b)
  rw [hbin] at hround
  have hdrift : |(t - tm) * affineResidualSlope A b| ≤ H * err := by
    rw [abs_mul]
    exact mul_le_mul htime hslope (abs_nonneg _) hH.le
  have hid : (b 2 + t * b 5) - (affineBaseEval C q₀ + a * j) =
      (affineBaseEval C q - affineBaseEval C q₀) +
        (affineResidualIntercept A b + tm * affineResidualSlope A b - a * j) +
        (t - tm) * affineResidualSlope A b := by
    have hframe : affineBaseEval C q = affineBaseEval A (nativeHorizontalLine b t) :=
      normalizedPredictor_frame H t₀ z₀ y₀ v₀ hH.ne' A _
    rw [hframe]
    dsimp [affineBaseEval, nativeHorizontalLine, affineResidualIntercept, affineResidualSlope]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add hpred hround)) hdrift)

end

end Submission.Obl.k4_critical_switching_state_preparation
