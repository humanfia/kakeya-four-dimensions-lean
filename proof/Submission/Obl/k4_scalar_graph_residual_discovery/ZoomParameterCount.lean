/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ZoomParameterCount.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomEntryPreparation
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomIncidenceCaps
import Submission.Obl.k4_scalar_grid_parameter_preparation.PaletteScaledCellCount

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation

namespace Zoom

noncomputable section

theorem quadraticCoordinates_normalizedCoeff {ρ : ℝ} (hρ : 0 < ρ)
    {l : ScalarLine} {q : Fin 5 → ℤ} (hl : cell ρ l.2 = q) (t : ℝ) :
    quadraticCoordinates (normalizedCoeff ρ l) t = position ρ q (l, t) := by
  funext e
  fin_cases e <;>
    simp [quadraticCoordinates, position, y, x, coeff, order,
      normalizedCoeff_of_coarse hρ hl]

theorem quadraticCoordinateCode_normalizedCoeff {ρ : ℝ} (hρ : 0 < ρ)
    {l : ScalarLine} {q : Fin 5 → ℤ} (hl : cell ρ l.2 = q) (h t : ℝ) :
    quadraticCoordinateCode h (normalizedCoeff ρ l) t = cell h (position ρ q (l, t)) := by
  unfold quadraticCoordinateCode cell
  rw [quadraticCoordinates_normalizedCoeff hρ hl]

/-- Count the original fine coefficient pieces in one zoom cell and one
original fine velocity bin. The same original palette factor occurs in
the prior floors and the incidence ceiling, so it cancels. -/
theorem fine_parameter_piece_count
    (μ : Measure ScalarIncidence) [IsFiniteMeasure μ] (θ : Measure ScalarLine)
    {R E : Set ScalarIncidence} (hR : MeasurableSet R) (hRE : R ⊆ E)
    {ρ β h A H η s C : ℝ} (hρ : 0 < ρ) (hh : 0 < h) (hA : 0 < A)
    (hH : 0 < H) (hη : 0 < η) (hs : 0 < s) (hC : 0 ≤ C)
    (q : Fin 5 → ℤ) (z : Fin 3 → ℤ) (c : ℤ)
    (F : Finset (Fin 5 → ℤ)) (hvel : ∀ b ∈ F, b 1 = c)
    (p : ℝ≥0∞) (hpt : p ≠ ∞)
    (hactive : ∀ b ∈ F,
      μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q b) h z) ≠ 0)
    (hprior : ∀ b ∈ F, ENNReal.ofReal (η * s / H) * p ≤ θ (parameterPiece ρ β q b))
    (hfloor : ∀ b ∈ F,
      ENNReal.ofReal (h / A) * θ (parameterPiece ρ β q b) ≤
        μ (R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q b) h z))
    (hcap : μ {v | v ∈ E ∧ (⌊v.1.2 1 / β⌋ : ℤ) = c ∧ cell h (position ρ q v) = z} ≤
      ENNReal.ofReal (H ^ 2 * h * C * s) * p) :
    (F.card : ℝ) ≤ A * H ^ 3 * C / η := by
  classical
  let cells := fun b =>
    R ∩ coefficientPhysicalEntry (normalizedCoeff ρ) (parameterPiece ρ β q b) h z
  let region := {v : ScalarIncidence |
    v ∈ E ∧ (⌊v.1.2 1 / β⌋ : ℤ) = c ∧ cell h (position ρ q v) = z}
  have hcover (b : Fin 5 → ℤ) (hb : b ∈ F) : cells b ⊆ region := by
    intro v hv
    refine ⟨hRE hv.1, ?_, ?_⟩
    · exact (congrFun hv.2.1.2 1).trans (hvel b hb)
    · rw [← quadraticCoordinateCode_normalizedCoeff hρ hv.2.1.1]
      exact hv.2.2
  by_cases hp₀ : p = 0
  · have hzero : μ region = 0 := by simpa only [hp₀, mul_zero, nonpos_iff_eq_zero] using hcap
    have hempty : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro b hb
      exact hactive b hb (le_antisymm ((measure_mono (hcover b hb)).trans_eq hzero) bot_le)
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  have hdisj : (↑F : Set (Fin 5 → ℤ)).PairwiseDisjoint cells := by
    intro b _ b' _ hne
    apply disjoint_left.mpr
    intro v hv hv'
    exact hne (hv.2.1.2.symm.trans hv'.2.1.2)
  have hmeas (b : Fin 5 → ℤ) (_ : b ∈ F) : MeasurableSet (cells b) :=
    hR.inter (measurableSet_coefficientPhysicalEntry _ (measurable_normalizedCoeff ρ)
      (measurableSet_parameterPiece ρ β q b) h z)
  have hmass (b : Fin 5 → ℤ) (hb : b ∈ F) :
      ENNReal.ofReal ((h / A) * (η * s / H)) * p ≤ μ (cells b) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ h / A), mul_assoc]
    exact (mul_le_mul_right (hprior b hb) _).trans (hfloor b hb)
  have hcount := palette_scaled_old_cell_count μ F cells hdisj hmeas region hcover
    ((h / A) * (η * s / H)) (H ^ 2 * h * C * s) (by positivity) (by positivity)
    p hp₀ hpt hmass hcap
  apply hcount.trans_eq
  field_simp

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
