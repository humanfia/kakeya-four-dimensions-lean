-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/ShiftCalibration.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.HeavyCalibration
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ShiftBudget
import Submission.Obl.k4_eligibility_sign_description.Families

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Filter MeasureTheory MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation

variable {α : Type*} [MeasurableSpace α] (p : Model α)

theorem init_point_eq_base (k : ℕ) (u : α × ℝ) :
    Fin.init (p.x k u.1 u.2) = p.base k u := by
  funext i
  fin_cases i <;> rfl

/-- Calibrate both base parts of a true quadratic after an arbitrary affine
shift, using only an original heavy-state mass floor. -/
theorem eventually_shifted_quadratic_calibration (hp : p.Valid) {C : ℝ}
    (hC : 1 ≤ C) (hcal : MeshCalibration C)
    (H : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k)
    (hHsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ k in atTop, ∀ τ : Measure (α × ℝ), τ ≤ p.μ k →
      ENNReal.ofReal (p.N k ^ (-6 * s)) ≤ τ Set.univ →
      ∀ (a₀ : ℝ), p.a k s ≤ a₀ → a₀ ≤ 1 →
      ∀ (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 →
      (∀ᵐ u ∂τ,
        |eval (p.x k u.1 u.2) F| ≤ p.K k * a₀ ∧
        |eval (p.x k u.1 u.2) (pderiv 3 F)| ≤ p.K k ∧
        |eval (p.x k u.1 u.2) (pderiv 3 (pderiv 3 F))| ≤ p.K k / a₀ ∧
        |eval (p.x k u.1 u.2) (Submission.Lib.K4ContactNormalization.affineBase L) -
          p.x k u.1 u.2 3| ≤ H k) →
      (∀ e, |(restrictBase (translatedTest L F)).coeff e| ≤ p.N k ^ (39 * s)) ∧
      (∀ e, |(restrictBase (pderiv 3 (translatedTest L F))).coeff e| ≤
        p.N k ^ (39 * s)) := by
  filter_upwards [eventually_heavy_quadratic_calibration p hp hC hcal hs,
    eventually_shifted_base_values p hp H hH hHsub hs] with k hcoeff hval
  intro τ hτ hmass a₀ ha₀ ha₁ L F hF hfit
  have hdegree : (translatedTest L F).totalDegree ≤ 2 :=
    (translatedTest_degree L F).trans hF
  have hboth : ∀ᵐ u ∂τ,
      |eval (p.base k u) (restrictBase (translatedTest L F))| ≤ p.N k ^ (2 * s) ∧
      |eval (p.base k u) (restrictBase (pderiv 3 (translatedTest L F)))| ≤
        p.N k ^ (2 * s) := by
    filter_upwards [hfit] with u hu
    have h := hval a₀ ha₀ ha₁ L F hF (p.x k u.1 u.2) hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
    simpa only [init_point_eq_base] using h
  constructor
  · exact hcoeff τ hτ hmass _ ((totalDegree_restrictBase _).trans hdegree)
      (hboth.mono (fun _ hu => hu.1))
  · exact hcoeff τ hτ hmass _ ((totalDegree_restrictBase _).trans
      ((Submission.Obl.k4_eligibility_sign_description.degree_pderiv_le _ _).trans hdegree))
      (hboth.mono (fun _ hu => hu.2))

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
