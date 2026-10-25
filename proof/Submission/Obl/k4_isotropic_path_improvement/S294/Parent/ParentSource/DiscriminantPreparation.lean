-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.DiscriminantPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/DiscriminantPreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/DiscriminantPreparation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/DiscriminantPreparation.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/DiscriminantPreparation.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_stable_native_signal_oscillation.Hidden
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials
import Submission.Lib.K4PolynomialRemezThree.OriginalMass

/-!
# Discriminant height from an original heavy native entry

The source base cap and entry floor control the discriminant coefficients.
No coefficient envelope from the input format enters this bound.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial
open k4_stable_native_signal_oscillation k4_quadratic_atlas_normalization

noncomputable section

/-- The accepted native discriminant bound and original-law polynomial
coefficient comparison supply one fixed coefficient constant. The measure
is unnormalized and may be a later submeasure of the original packet. -/
theorem original_native_discriminant_coefficients :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (w : Ω → ℝ)
      (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ 2 →
      ∀ K a m β : ℝ, 2 ≤ K → 0 < a → 0 < m → 0 < β → m ≤ β →
      |curvature P 3| ≤ K / a → ENNReal.ofReal m ≤ μ univ →
      (∀ U : Set (Fin 3 → ℝ), MeasurableSet U →
        μ (Z ⁻¹' U) ≤ ENNReal.ofReal β * volume U) →
      (∀ᵐ x ∂μ, Z x ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
        |eval (Fin.snoc (Z x) (w x)) P| ≤ K * a ∧
        |eval (Fin.snoc (Z x) (w x)) (pderiv 3 P)| ≤ K) →
      ∀ d, |(baseDiscriminant P).coeff d| ≤
        C * (96 / (m / β)) ^ 6 * K ^ 4 := by
  obtain ⟨C, hC, hcoeff⟩ :=
    Submission.Lib.K4PolynomialRemezThree.exists_coefficient_bound_from_dominated_mass 2
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ Z w P hP K a m β hK ha hm hβ hmβ hcurv hmass hdom hae
  have htrace : ∀ᵐ x ∂μ, Z x ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
      |eval (Z x) (baseDiscriminant P)| ≤ K ^ 4 := by
    filter_upwards [hae] with x hx
    refine ⟨hx.1, ?_⟩
    rw [eval_baseDiscriminant P hP (Z x) (w x)]
    exact discriminant_bound P (Fin.snoc (Z x) (w x)) 3 hK ha hcurv hx.2.1 hx.2.2
  have hh := hcoeff Ω μ Z (baseDiscriminant P) (baseDiscriminant_degree P hP)
    m β (K ^ 4) hm hβ hmβ (by positivity) hmass hdom htrace
  norm_num at hh
  exact hh

/-- Polynomial original entry floors and base caps give a polynomial
discriminant height. The exponent is chosen before the native equation,
entry, source measure, and all format data. -/
theorem original_native_discriminant_coefficient_power (q : ℕ) :
    ∃ e : ℕ, 4 ≤ e ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (w : Ω → ℝ)
      (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ 2 →
      ∀ K a : ℝ, 2 ≤ K → 0 < a → |curvature P 3| ≤ K / a →
      ENNReal.ofReal ((K ^ q)⁻¹) ≤ μ univ →
      (∀ U : Set (Fin 3 → ℝ), MeasurableSet U →
        μ (Z ⁻¹' U) ≤ ENNReal.ofReal (K ^ q) * volume U) →
      (∀ᵐ x ∂μ, Z x ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
        |eval (Fin.snoc (Z x) (w x)) P| ≤ K * a ∧
        |eval (Fin.snoc (Z x) (w x)) (pderiv 3 P)| ≤ K) →
      ∀ d, |(baseDiscriminant P).coeff d| ≤ K ^ e := by
  obtain ⟨C, hC, hcoeff⟩ := original_native_discriminant_coefficients
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt (C * (96 : ℝ) ^ 6)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨e + 12 * q + 4, by omega, ?_⟩
  intro Ω _ μ Z w P hP K a hK ha hcurv hmass hdom hae d
  have hKp : 0 < K := by linarith
  have hKone : 1 ≤ K := by linarith
  have hmβ : (K ^ q)⁻¹ ≤ K ^ q := by
    exact (inv_le_one_of_one_le₀ (one_le_pow₀ hKone)).trans (one_le_pow₀ hKone)
  have hc := hcoeff μ Z w P hP K a (K ^ q)⁻¹ (K ^ q) hK ha
    (by positivity) (by positivity) hmβ hcurv hmass hdom hae d
  have hconst : C * (96 : ℝ) ^ 6 ≤ K ^ e :=
    he.le.trans (pow_le_pow_left₀ (by norm_num) hK e)
  have hid : C * (96 / ((K ^ q)⁻¹ / K ^ q)) ^ 6 * K ^ 4 =
      (C * (96 : ℝ) ^ 6) * K ^ (12 * q + 4) := by
    field_simp
    ring
  rw [hid] at hc
  exact hc.trans ((mul_le_mul_of_nonneg_right hconst (by positivity)).trans_eq
    (by simp only [pow_add, mul_assoc]))

/-- In the small-curvature case the SAME height parameter controls every
coefficient and supplies a positive central discriminant at almost every
original base point. These are the numeric inputs for the local analytic
branch construction, chosen independently of the source format. -/
theorem original_native_discriminant_preparation (q : ℕ) :
    ∃ e : ℕ, 4 ≤ e ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (w : Ω → ℝ)
      (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ 2 →
      ∀ K a : ℝ, 2 ≤ K → 0 < a → |curvature P 3| ≤ K / a →
      |curvature P 3| ≤ (K ^ 5 * a)⁻¹ →
      ENNReal.ofReal ((K ^ q)⁻¹) ≤ μ univ →
      (∀ U : Set (Fin 3 → ℝ), MeasurableSet U →
        μ (Z ⁻¹' U) ≤ ENNReal.ofReal (K ^ q) * volume U) →
      (∀ᵐ x ∂μ, Z x ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
        |eval (Fin.snoc (Z x) (w x)) P| ≤ K * a ∧
        K⁻¹ ≤ |eval (Fin.snoc (Z x) (w x)) (pderiv 3 P)| ∧
        |eval (Fin.snoc (Z x) (w x)) (pderiv 3 P)| ≤ K) →
      (∀ d, |(baseDiscriminant P).coeff d| ≤ K ^ e) ∧
      ∀ᵐ x ∂μ, ((K ^ e)⁻¹) ^ 2 ≤ eval (Z x) (baseDiscriminant P) := by
  obtain ⟨e, he, hcoeff⟩ := original_native_discriminant_coefficient_power q
  refine ⟨e, he, ?_⟩
  intro Ω _ μ Z w P hP K a hK ha hcurv hsmall hmass hdom hae
  have hKp : 0 < K := by linarith
  have hKone : 1 ≤ K := by linarith
  refine ⟨hcoeff μ Z w P hP K a hK ha hcurv hmass hdom ?_, ?_⟩
  · filter_upwards [hae] with x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.2⟩
  · have hpower : 2 * K ≤ K ^ e := by
      have htwo : 2 * K ≤ K ^ 2 := by nlinarith
      exact htwo.trans (pow_le_pow_right₀ hKone (by omega))
    have hinv : (K ^ e)⁻¹ ≤ K⁻¹ / 2 := by
      convert inv_anti₀ (show 0 < 2 * K by positivity) hpower using 1 <;> field_simp
    have hfloor : ((K ^ e)⁻¹) ^ 2 ≤ (K⁻¹) ^ 2 / 2 := by
      calc
        _ ≤ (K⁻¹ / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hinv 2
        _ ≤ _ := by nlinarith [sq_nonneg K⁻¹]
    filter_upwards [hae] with x hx
    rw [eval_baseDiscriminant P hP (Z x) (w x)]
    exact hfloor.trans (discriminant_floor P (Fin.snoc (Z x) (w x)) 3
      hK ha hsmall hx.2.1 hx.2.2.1)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
