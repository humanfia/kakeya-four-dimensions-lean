-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/DiscriminantFromGroup.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/DiscriminantFromGroup.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.BaseTranslation
import Submission.Lib.K4PolynomialRemezThree.OriginalMass

/-!
# The native discriminant conditions from the group

At a point of the group's native sheet (small native fit `|a w² + B w + C| ≤ ε`, hidden
derivative `2 a w + B` between `A₁⁻¹` and `A₁`, and `4 |a| ε ≤ (2 A₁²)⁻¹`) the native base
discriminant `B² - 4 a C` lies in `[1/(2A₁²), A₁² + 1]`. A group measure on the unit cube of
block coordinates, dominated by `β` times volume and of mass at least `m`, then bounds every
coefficient of the discriminant by multivariate Remez (accepted lib K4PolynomialRemezThree).
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial MeasureTheory Set

lemma eval_nativeBaseDiscriminant {n : ℕ} (a : ℝ) (B C₀ : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    eval x (nativeBaseDiscriminant a B C₀) = (eval x B) ^ 2 - 4 * a * eval x C₀ := by
  simp [nativeBaseDiscriminant]

/-- The discriminant window at a point of the native sheet. -/
theorem discriminant_window {a ε A₁ bu cu w : ℝ} (hA₁ : 2 ≤ A₁)
    (hfit : |a * w ^ 2 + bu * w + cu| ≤ ε)
    (hlo : A₁⁻¹ ≤ |2 * a * w + bu|) (hhi : |2 * a * w + bu| ≤ A₁)
    (hsmall : 4 * |a| * ε ≤ (2 * A₁ ^ 2)⁻¹) :
    1 / (2 * A₁ ^ 2) ≤ bu ^ 2 - 4 * a * cu ∧ bu ^ 2 - 4 * a * cu ≤ A₁ ^ 2 + 1 := by
  have hA0 : 0 < A₁ := by linarith
  have hdisc : bu ^ 2 - 4 * a * cu =
      (2 * a * w + bu) ^ 2 - 4 * a * (a * w ^ 2 + bu * w + cu) := by ring
  have hq2lo : (A₁⁻¹) ^ 2 ≤ (2 * a * w + bu) ^ 2 := by
    rw [← sq_abs (2 * a * w + bu)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hA0.le) hlo 2
  have hq2hi : (2 * a * w + bu) ^ 2 ≤ A₁ ^ 2 := by
    rw [← sq_abs (2 * a * w + bu)]
    exact pow_le_pow_left₀ (abs_nonneg _) hhi 2
  have hcorr : |4 * a * (a * w ^ 2 + bu * w + cu)| ≤ (2 * A₁ ^ 2)⁻¹ := by
    rw [abs_mul, abs_mul]
    calc |4| * |a| * |a * w ^ 2 + bu * w + cu| ≤ |4| * |a| * ε := by gcongr
      _ = 4 * |a| * ε := by norm_num
      _ ≤ (2 * A₁ ^ 2)⁻¹ := hsmall
  have hcorr' := abs_le.mp hcorr
  have hAsq : (A₁⁻¹) ^ 2 = (A₁ ^ 2)⁻¹ := by rw [inv_pow]
  have hhalf : (2 * A₁ ^ 2)⁻¹ = (A₁ ^ 2)⁻¹ / 2 := by
    rw [mul_inv, div_eq_mul_inv]; ring
  have hsmall' : (2 * A₁ ^ 2)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    nlinarith
  constructor
  · rw [hdisc, one_div]
    have : (2 * A₁ ^ 2)⁻¹ ≤ (A₁ ^ 2)⁻¹ - (2 * A₁ ^ 2)⁻¹ := by rw [hhalf]; linarith
    linarith [hcorr'.1, hcorr'.2]
  · rw [hdisc]
    linarith [hcorr'.1, hcorr'.2]

/-- Coefficient bounds for the native discriminant from a dominated group measure on the cube. -/
theorem discriminant_coeff_bound_of_group (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ)
      (a : ℝ) (B C₀ : MvPolynomial (Fin 3) ℝ), B.totalDegree ≤ d → C₀.totalDegree ≤ d →
      ∀ (m β ε A₁ : ℝ), 0 < m → 0 < β → m ≤ β → 2 ≤ A₁ → 4 * |a| * ε ≤ (2 * A₁ ^ 2)⁻¹ →
      ENNReal.ofReal m ≤ μ univ →
      (∀ U : Set (Fin 3 → ℝ), MeasurableSet U → μ (Z ⁻¹' U) ≤ ENNReal.ofReal β * volume U) →
      (∀ᵐ ω ∂μ, Z ω ∈ Icc (0 : Fin 3 → ℝ) 1 ∧ ∃ w : ℝ,
        |a * w ^ 2 + eval (Z ω) B * w + eval (Z ω) C₀| ≤ ε ∧
        A₁⁻¹ ≤ |2 * a * w + eval (Z ω) B| ∧ |2 * a * w + eval (Z ω) B| ≤ A₁) →
      ∀ e, |(nativeBaseDiscriminant a B C₀).coeff e| ≤
        C * (32 * (((2 * d : ℕ) : ℝ) + 1) / (m / β)) ^ (3 * (2 * d)) * (A₁ ^ 2 + 1) := by
  obtain ⟨C, hC, hbound⟩ :=
    Submission.Lib.K4PolynomialRemezThree.exists_coefficient_bound_from_dominated_mass (2 * d)
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ Z a B C₀ hB hC0 m β ε A₁ hm hβ hmβ hA₁ hsmall hmass hdom htrace
  have hdeg : (nativeBaseDiscriminant a B C₀).totalDegree ≤ 2 * d :=
    nativeBaseDiscriminant_totalDegree d a B C₀ hB hC0
  have hA0 : (0 : ℝ) ≤ A₁ ^ 2 + 1 := by positivity
  apply hbound Ω μ Z _ hdeg m β (A₁ ^ 2 + 1) hm hβ hmβ hA0 hmass hdom
  filter_upwards [htrace] with ω hω
  obtain ⟨hcube, w, hfit, hlo, hhi⟩ := hω
  refine ⟨hcube, ?_⟩
  rw [eval_nativeBaseDiscriminant]
  obtain ⟨h1, h2⟩ := discriminant_window hA₁ hfit hlo hhi hsmall
  rw [abs_le]
  constructor
  · have : 0 < 1 / (2 * A₁ ^ 2) := by positivity
    linarith
  · exact h2

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
