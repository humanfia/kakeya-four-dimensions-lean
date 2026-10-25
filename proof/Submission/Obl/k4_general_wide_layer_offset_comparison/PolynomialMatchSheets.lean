import Submission.Obl.k4_stable_native_signal_oscillation.ComplexPolynomial
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.DiscrepancyGroups
import Submission.Obl.k4_quadratic_selector_sweep.SignFibers

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/PolynomialMatchSheets.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MvPolynomial Set
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

/-- An ordinary real quadratic is a degree-two matching sheet, with no
coefficient-height restriction. -/
def polynomialMatchSheet (P : MvPolynomial (Fin 3) ℝ) :
    EuclideanSpace ℂ (Fin 3) → ℂ :=
  fun z => eval (fun i => z i) (P.map (algebraMap ℝ ℂ))

theorem polynomialMatchSheet_isMatchSheet (P : MvPolynomial (Fin 3) ℝ)
    (hP : P.totalDegree ≤ 2) : IsMatchSheet (polynomialMatchSheet P) := by
  have hdeg := (Submission.Obl.k4_stable_native_signal_oscillation.complexification_degree P).trans hP
  refine ⟨?_, ?_, ?_⟩
  · change Submission.Obl.k4_algebraic_real_jet_comparison.HasSheetRelation 3 2
      (fun z => eval (fun i => z i) (P.map (algebraMap ℝ ℂ)))
    exact Submission.Obl.k4_stable_native_signal_oscillation.polynomial_hasSheetRelation _ hdeg
  · exact (Submission.Obl.k4_stable_native_signal_oscillation.differentiable_polynomial _).differentiableOn
  · intro x hx
    have he : polynomialMatchSheet P (emb x) = (eval (fun i => x i) P : ℂ) :=
      Submission.Obl.k4_stable_native_signal_oscillation.eval_complexification P x
    rw [he]
    simp

theorem polynomialMatchSheet_real (P : MvPolynomial (Fin 3) ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    polynomialMatchSheet P (emb x) = (eval (fun i => x i) P : ℂ) :=
  Submission.Obl.k4_stable_native_signal_oscillation.eval_complexification P x

/-- Moving time/transverse normalization; the third matching coordinate is
an independent dummy coordinate. -/
def projectedChartSubstitution (time h u v b : ℝ) : Fin 2 → MvPolynomial (Fin 3) ℝ :=
  ![C time + C h * X 0,
    C u + C v * (C time + C h * X 0) + C b * X 1]

def projectedChartPolynomial (G : MvPolynomial (Fin 2) ℝ) (time h u v b : ℝ) :
    MvPolynomial (Fin 3) ℝ := bind₁ (projectedChartSubstitution time h u v b) G

theorem projectedChartSubstitution_degree (time h u v b : ℝ) (i : Fin 2) :
    (projectedChartSubstitution time h u v b i).totalDegree ≤ 1 := by
  have hlin (a c : ℝ) : (C a + C c * (X 0 : MvPolynomial (Fin 3) ℝ)).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)
  fin_cases i
  · exact hlin _ _
  · dsimp only [projectedChartSubstitution, Matrix.cons_val_one, Matrix.cons_val_zero]
    apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      apply max_le
      · simp
      · exact (totalDegree_mul _ _).trans (by simpa using hlin time h)
    · exact (totalDegree_mul _ _).trans (by simp)

theorem projectedChartPolynomial_degree (G : MvPolynomial (Fin 2) ℝ)
    (hG : G.totalDegree ≤ 2) (time h u v b : ℝ) :
    (projectedChartPolynomial G time h u v b).totalDegree ≤ 2 :=
  (Submission.Obl.k4_quadratic_selector_sweep.totalDegree_bind_affine _
    (projectedChartSubstitution_degree time h u v b) G).trans hG

theorem projectedChartPolynomial_value (G : MvPolynomial (Fin 2) ℝ)
    (time h u v b : ℝ) (z : Fin 3 → ℝ) :
    eval z (projectedChartPolynomial G time h u v b) =
      eval ![time + h * z 0, u + v * (time + h * z 0) + b * z 1] G := by
  change eval₂Hom (RingHom.id ℝ) z (bind₁ (projectedChartSubstitution time h u v b) G) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : Fin 2 → ℝ => eval₂Hom (RingHom.id ℝ) f G)
  funext i
  fin_cases i <;> simp [projectedChartSubstitution]

/-- The affine chart recovers the original polynomial at its normalized
base point; the unused matching coordinate is arbitrary. -/
theorem projectedChartPolynomial_recover (G : MvPolynomial (Fin 2) ℝ)
    {time h u v b : ℝ} (hh : h ≠ 0) (hb : b ≠ 0)
    (native matching : Fin 3 → ℝ)
    (hzero : matching 0 = (native 0 - time) / h)
    (hone : matching 1 = (native 2 - u - native 0 * v) / b) :
    eval matching (projectedChartPolynomial G time h u v b) = eval ![native 0, native 2] G := by
  rw [projectedChartPolynomial_value, hzero, hone]
  apply congrArg (fun z : Fin 2 → ℝ => eval z G)
  ext i
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · field_simp [hh, hb] <;> ring
  · field_simp [hh, hb] <;> ring

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
