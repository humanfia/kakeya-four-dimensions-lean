/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/PredictorCellCaps.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.GraphCellCaps
import Submission.Obl.k4_horizontal_strict_parameter_step.ParameterCaps

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Lib.K4MovingMeshBoxes (basePoint)

noncomputable section

/-- A full-time predictor fit and the original joint cap give its original
physical base-cell ceiling. Both the current auxiliary event and its palette
condition remain inside the cap; no pair-fibre measure is substituted. -/
theorem predictor_base_cell_cap {α : Type} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (h : Fin 6 → ℝ)
    (condition : α × ℝ → Prop)
    {δ a C v χ K M D : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hC : 0 ≤ C)
    (hM : 0 ≤ M) (hD : 0 < D) (hv : |v| ≤ K)
    (hcondition : ∀ᵐ p ∂μ, condition p → p.2 ∈ Icc (0 : ℝ) 1 ∧
      |b p.1 3 - v| ≤ χ ∧ |b p.1 4 + b p.1 0| ≤ χ ∧ |b p.1 0| ≤ K ∧
      |predictorTimeSlope h (b p.1 0) (b p.1 1)| ≤ 2 * M)
    (hfit : ∀ᵐ p ∂μ, condition p →
      |b p.1 2 + p.2 * b p.1 5 - predictor h p.2 (b p.1 0) (b p.1 1)| ≤ a)
    (hgrad : ∀ t ∈ Icc (0 : ℝ) 1,
      |h 2 + h 3 * t| ≤ 2 * M / D ∧ |h 4 + h 5 * t| ≤ 2 * M / D)
    (hround : 2 * M * δ + (6 * M / D) * (χ + (K + 1) * δ) ≤ a)
    (hcell : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh δ (basePoint (b p.1) p.2) = q ∧
        ⌊(b p.1 2 + p.2 * b p.1 5) / a⌋ = j ∧ condition p} ≤
          ENNReal.ofReal (C * δ ^ 3)) (q : Fin 3 → ℤ) :
    μ {p | baseMesh δ (basePoint (b p.1) p.2) = q ∧ condition p} ≤
      ENNReal.ofReal (7 * C) * ENNReal.ofReal (δ ^ 3) := by
  have hfit' : ∀ᵐ p ∂μ, condition p →
      |b p.1 2 + p.2 * b p.1 5 -
        predictor h (cellParameters δ v (baseMesh δ (basePoint (b p.1) p.2)) 0)
          (cellParameters δ v (baseMesh δ (basePoint (b p.1) p.2)) 1)
          (cellParameters δ v (baseMesh δ (basePoint (b p.1) p.2)) 2)| ≤ 2 * a := by
    filter_upwards [hcondition, hfit] with p hc hf hp
    obtain ⟨ht, hvel, hcontact, hpos, hslope⟩ := hc hp
    have he := (predictor_reconstruction_error hδ ht hvel hcontact hpos hv hM hD
      hslope hgrad).trans hround
    rw [meshParameters_eq_cellParameters] at he
    exact (abs_sub_le _ (predictor h p.2 (b p.1 0) (b p.1 1)) _).trans
      ((add_le_add (hf hp) he).trans_eq (by ring))
  have hb := graph_base_cell_cap μ
    (fun p : α × ℝ => basePoint (b p.1) p.2)
    (fun p : α × ℝ => b p.1 2 + p.2 * b p.1 5) condition ha
    (fun q => predictor h (cellParameters δ v q 0)
      (cellParameters δ v q 1) (cellParameters δ v q 2)) hfit' hcell q
  exact hb.trans_eq (ENNReal.ofReal_mul (mul_nonneg (by norm_num) hC))

end

end Submission.Obl.k4_horizontal_strict_parameter_step
