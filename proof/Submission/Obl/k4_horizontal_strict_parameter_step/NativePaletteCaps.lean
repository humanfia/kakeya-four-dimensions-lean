/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativePaletteCaps.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeWidthCaps
import Submission.Obl.k4_row_cell_regularization.Palette

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_row_cell_regularization

noncomputable section

/-- A conditioned original joint cap has exactly the unchanged REAL palette
coefficient used by the matching reference budget. Auxiliary events and later
current-law restrictions add no multiplicity factor. -/
theorem joint_cell_cap_in_palette {α : Type} [MeasurableSpace α]
    (μ lam : Measure (α × ℝ)) (hdom : lam ≤ μ) (π : Measure ℝ) [IsFiniteMeasure π]
    (b : α → Fin 6 → ℝ) {N K d R re v w : ℝ}
    (hN : 0 < N) (hK : 0 ≤ K)
    (caps : OriginalWidthCapsAt N K d R μ π b)
    (hre : R⁻¹ ≤ re) (hre' : re ≤ R) (hv : R⁻¹ ≤ v) (hv' : v ≤ R)
    (hw : N ^ (-R) ≤ w) (hw1 : w ≤ 1)
    (condition : α × ℝ → Prop) (z : ℤ)
    (hcondition : ∀ p, condition p → ⌊b p.1 3 / N ^ (-v)⌋ = z)
    (q : Fin 3 → ℤ) (j : ℤ) :
    lam {p | baseMesh (N ^ (-re)) (physicalBase (b p.1) p.2) = q ∧
      ⌊(b p.1 2 + p.2 * b p.1 5) / w⌋ = j ∧ condition p} ≤
      ENNReal.ofReal (K * w ^ d * binWeight π (N ^ (-v)) z) *
        ENNReal.ofReal ((N ^ (-re)) ^ 3) := by
  have hχ : 0 < N ^ (-v) := Real.rpow_pos_of_pos hN _
  have hδ : 0 < N ^ (-re) := Real.rpow_pos_of_pos hN _
  have hwp : 0 < w := (Real.rpow_pos_of_pos hN _).trans_le hw
  have hπ : π {u : ℝ | ⌊u / N ^ (-v)⌋ = z} =
      ENNReal.ofReal (binWeight π (N ^ (-v)) z) := by
    rw [← velocityCell_eq_floor hχ]
    exact (ENNReal.ofReal_toReal (measure_ne_top π _)).symm
  have hbin := binWeight_nonneg π (N ^ (-v)) z
  have hbound := (caps re v w hre hre' hv hv' hw hw1).2 q j z
  calc
    _ ≤ μ {p | baseMesh (N ^ (-re)) (physicalBase (b p.1) p.2) = q ∧
        ⌊(b p.1 2 + p.2 * b p.1 5) / w⌋ = j ∧ condition p} := hdom _
    _ ≤ μ {p | baseMesh (N ^ (-re)) (physicalBase (b p.1) p.2) = q ∧
        ⌊(b p.1 2 + p.2 * b p.1 5) / w⌋ = j ∧ ⌊b p.1 3 / N ^ (-v)⌋ = z} :=
      measure_mono (fun p hp => ⟨hp.1, hp.2.1, hcondition p hp.2.2⟩)
    _ ≤ _ := hbound.trans_eq (by
      rw [hπ, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring)

/-- The same original palette cap allows auxiliary velocity certificates that
hold only almost everywhere under the current dominated law. -/
theorem joint_cell_cap_in_palette_ae {α : Type} [MeasurableSpace α]
    (μ lam : Measure (α × ℝ)) (hdom : lam ≤ μ) (π : Measure ℝ) [IsFiniteMeasure π]
    (b : α → Fin 6 → ℝ) {N K d R re v w : ℝ}
    (hN : 0 < N) (hK : 0 ≤ K)
    (caps : OriginalWidthCapsAt N K d R μ π b)
    (hre : R⁻¹ ≤ re) (hre' : re ≤ R) (hv : R⁻¹ ≤ v) (hv' : v ≤ R)
    (hw : N ^ (-R) ≤ w) (hw1 : w ≤ 1)
    (condition : α × ℝ → Prop) (z : ℤ)
    (hcondition : ∀ᵐ p ∂lam, condition p → ⌊b p.1 3 / N ^ (-v)⌋ = z)
    (q : Fin 3 → ℤ) (j : ℤ) :
    lam {p | baseMesh (N ^ (-re)) (physicalBase (b p.1) p.2) = q ∧
      ⌊(b p.1 2 + p.2 * b p.1 5) / w⌋ = j ∧ condition p} ≤
      ENNReal.ofReal (K * w ^ d * binWeight π (N ^ (-v)) z) *
        ENNReal.ofReal ((N ^ (-re)) ^ 3) := by
  have hb := joint_cell_cap_in_palette μ lam hdom π b hN hK caps hre hre' hv hv' hw hw1
    (fun p => condition p ∧ ⌊b p.1 3 / N ^ (-v)⌋ = z) z (fun p hp => hp.2) q j
  apply (measure_mono_ae ?_).trans hb
  filter_upwards [hcondition] with p hp he
  exact ⟨he.1, he.2.1, he.2.2, hp he.2.2⟩

end

end Submission.Obl.k4_horizontal_strict_parameter_step
