import Submission.Lib.K4ModelReduction.AveragingComposition

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Uniform averaging in actual coordinates of a finite-dimensional base. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory
open scoped ENNReal

def coordinateSplit {n : ℕ} (i : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).trans
    MeasurableEquiv.prodComm

theorem coordinateSplit_measurePreserving {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (coordinateSplit i) volume
      ((volume : Measure (Fin n → ℝ)).prod volume) :=
  Measure.measurePreserving_swap.comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i)

noncomputable def coordinateAverage {n : ℕ} (i : Fin (n + 1)) (M : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    boundedMeasurableFunctions (Fin (n + 1) → ℝ) M →
      boundedMeasurableFunctions (Fin (n + 1) → ℝ) M :=
  averageInSplit (coordinateSplit i) M hρ

theorem coordinateAverage_eq {n : ℕ} (i : Fin (n + 1)) (M : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (x : Fin (n + 1) → ℝ) :
    (coordinateAverage i M hρ f).val x =
      meshAverage (fun t => f.val (Function.update x i t)) ρ (x i) := by
  change meshAverage (fun t => f.val (i.insertNth t (i.removeNth x))) ρ (x i) = _
  simp only [Fin.insertNth_removeNth]

theorem coordinateAverage_contract {n : ℕ} (i : Fin (n + 1)) (M : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (f g : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M) :
    densityL1Distance volume (coordinateAverage i M hρ f).val (coordinateAverage i M hρ g).val ≤
      densityL1Distance volume f.val g.val :=
  averageInSplit_contract volume volume (coordinateSplit i)
    (coordinateSplit_measurePreserving i) M hρ f g

theorem coordinateAverage_mass {n : ℕ} (i : Fin (n + 1)) (M : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : ∀ x, 0 ≤ f.val x) :
    (∫⁻ x, ENNReal.ofReal ((coordinateAverage i M hρ f).val x)) =
      ∫⁻ x, ENNReal.ofReal (f.val x) :=
  averageInSplit_mass volume volume (coordinateSplit i)
    (coordinateSplit_measurePreserving i) M hρ f hf

/-- Averaging a finite list of base coordinates costs only their
individual L1 errors, all measured on the original density. -/
theorem coordinate_averaging_error {n : ℕ} (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (L : List (Fin (n + 1))) (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M) :
    densityL1Distance volume (L.foldr (fun i g => coordinateAverage i M hρ g) f).val f.val ≤
      (L.map (fun i => densityL1Distance volume (coordinateAverage i M hρ f).val f.val)).sum :=
  averaging_composition_error volume M (fun i => coordinateAverage i M hρ)
    (fun i f g => coordinateAverage_contract i M hρ f g) L f

end Submission.Lib.K4ModelReduction
