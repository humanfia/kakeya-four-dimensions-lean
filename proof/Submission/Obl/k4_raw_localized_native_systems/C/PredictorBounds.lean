import Submission.Obl.k4_raw_localized_native_systems.C.ScalarCoordinates
import Submission.Obl.k4_native_finite_terminal_atlas_lift.PolynomialBounds

/-
Adapted from this LOT tree, o178, session x0596, `PredictorBounds.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MvPolynomial
open Submission.Obl.k4_native_finite_terminal_atlas_lift

noncomputable section

theorem tangentBase_coefficientMass (a : ℝ) (v : Fin 3 → ℝ)
    {H : ℝ} (ha : |a| ≤ H) (hv : ∀ i, |v i| ≤ H) :
    coefficientMass (tangentBase a v) ≤ 4 * H := by
  unfold tangentBase
  calc
    _ ≤ coefficientMass (C a) + coefficientMass (∑ i, C (v i) * X i) :=
      coefficientMass_add _ _
    _ ≤ |a| + ∑ i, |v i| := by
      rw [coefficientMass_C]
      apply add_le_add le_rfl
      apply (coefficientMass_sum _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      simpa only [coefficientMass_C, coefficientMass_X, mul_one] using
        coefficientMass_mul (C (v i)) (X i : MvPolynomial (Fin 3) ℝ)
    _ ≤ H + ∑ _i : Fin 3, H := add_le_add ha (Finset.sum_le_sum (fun i _ => hv i))
    _ = 4 * H := by simp; ring

/-- Scalar coefficient bounds and polynomial frame bounds give polynomial
coefficient bounds after returning to original base coordinates. -/
theorem scalarPredictor_coefficientMass (t₀ q a : ℝ) (v : Fin 3 → ℝ)
    (R : MvPolynomial (Fin 2) ℝ) (hR : R.totalDegree ≤ 2)
    {H E : ℝ} (hH : 1 ≤ H) (ht : |t₀| ≤ 1) (hq : |q⁻¹| ≤ H)
    (ha : |a| ≤ H) (hv : ∀ i, |v i| ≤ H) (hE : 0 ≤ E)
    (hcoeff : ∀ e, |R.coeff e| ≤ E) :
    coefficientMass (scalarPredictor t₀ q a v R) ≤ 144 * E * H ^ 2 := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have htpoly : coefficientMass (C q⁻¹ * (X 0 - C t₀) : MvPolynomial (Fin 3) ℝ) ≤ 4 * H := by
    calc
      _ ≤ coefficientMass (C q⁻¹) * coefficientMass (X 0 - C t₀) := coefficientMass_mul _ _
      _ ≤ H * (1 + |t₀|) := by
        rw [coefficientMass_C]
        exact mul_le_mul hq (by
          simpa only [coefficientMass_X, coefficientMass_C] using
            coefficientMass_sub (X 0 : MvPolynomial (Fin 3) ℝ) (C t₀))
          (coefficientMass_nonneg _) hH0
      _ ≤ 4 * H := by nlinarith
  have hsub (i : Fin 2) :
      coefficientMass (![C q⁻¹ * (X 0 - C t₀), tangentBase a v] i) ≤ 4 * H := by
    fin_cases i
    · exact htpoly
    · exact tangentBase_coefficientMass a v ha hv
  have hmass : coefficientMass R ≤ 9 * E := by
    simpa using coefficientMass_le_of_coeff_bound R hR hE hcoeff
  calc
    _ ≤ coefficientMass R * (4 * H) ^ 2 :=
      coefficientMass_aeval R hR _ (by linarith) hsub
    _ ≤ (9 * E) * (4 * H) ^ 2 := mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = 144 * E * H ^ 2 := by ring

theorem coefficientMass_rename_le {n m D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) (f : Fin n → Fin m) :
    coefficientMass (rename f P) ≤ coefficientMass P := by
  rw [rename_eq_aeval]
  simpa only [one_pow, mul_one] using coefficientMass_aeval P hP (X ∘ f)
    (show (1 : ℝ) ≤ 1 from le_rfl) (fun i => by simp only [Function.comp_apply, coefficientMass_X, le_refl])

theorem nativeCorrection_coefficient_bound (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ q a : ℝ) (v : Fin 3 → ℝ)
    (R : MvPolynomial (Fin 2) ℝ) (hR : R.totalDegree ≤ 2)
    {H E V : ℝ} (hH : 1 ≤ H) (ht : |t₀| ≤ 1) (hq : |q⁻¹| ≤ H)
    (ha : |a| ≤ H) (hv : ∀ i, |v i| ≤ H) (hE : 0 ≤ E) (hV : 0 ≤ V)
    (hcoeffP : ∀ e, |P.coeff e| ≤ V) (hcoeffR : ∀ e, |R.coeff e| ≤ E)
    (e : Fin 4 →₀ ℕ) :
    |(nativeCorrection P (scalarPredictor t₀ q a v R)).coeff e| ≤
      81 * V + 144 * E * H ^ 2 := by
  have hmass : coefficientMass P ≤ 81 * V := by
    simpa using coefficientMass_le_of_coeff_bound P hP hV hcoeffP
  have hpred := scalarPredictor_coefficientMass t₀ q a v R hR hH ht hq ha hv hE hcoeffR
  calc
    _ ≤ coefficientMass (nativeCorrection P (scalarPredictor t₀ q a v R)) :=
      abs_coeff_le_coefficientMass (nativeCorrection P (scalarPredictor t₀ q a v R)) e
    _ ≤ coefficientMass P + coefficientMass (rename Fin.castSucc (scalarPredictor t₀ q a v R)) :=
      coefficientMass_sub P (rename Fin.castSucc (scalarPredictor t₀ q a v R))
    _ ≤ coefficientMass P + coefficientMass (scalarPredictor t₀ q a v R) :=
      add_le_add le_rfl (coefficientMass_rename_le (scalarPredictor t₀ q a v R)
        ((scalarPredictor_degree t₀ q a v R).trans hR) Fin.castSucc)
    _ ≤ 81 * V + 144 * E * H ^ 2 := add_le_add hmass hpred

end
end Submission.Obl.k4_raw_localized_native_systems.C
