-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.ModelEH1
import Submission.Obl.k4_finite_affine_parent_sources.Original

namespace Submission.Obl.k4_finite_affine_parent_sources

open MvPolynomial
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

namespace PFrame

/-- The native child derivative uses the PARENT hidden derivative unit B. -/
theorem eval_normTest_derivative
    (Φ : PFrame) (hq : Φ.F.q ≠ 0) (hD : IsUnit Φ.F.D.det)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hsc : Φ.sc = B / δ)
    (Q : MvPolynomial (Fin 4) ℝ) (l : Trajectory) (t : ℝ) :
    eval (exS Φ.eb l t) (pderiv 3 (Φ.normTest δ Q)) =
      eval (x l (Φ.F.t₀ + Φ.F.q * t)) (pderiv 3 Q) / B := by
  have hsc₀ : Φ.sc ≠ 0 := by rw [hsc]; positivity
  rw [Φ.pderiv_normTest, smul_eval, Φ.eval_normTest_at hq hD hsc₀, hsc]
  field_simp
  rfl

/-- Curvature is in parent hidden units, independently of the child width. -/
theorem eval_normTest_second_derivative
    (Φ : PFrame) (hq : Φ.F.q ≠ 0) (hD : IsUnit Φ.F.D.det)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hsc : Φ.sc = B / δ)
    (Q : MvPolynomial (Fin 4) ℝ) (l : Trajectory) (t : ℝ) :
    eval (exS Φ.eb l t) (pderiv 3 (pderiv 3 (Φ.normTest δ Q))) =
      δ * eval (x l (Φ.F.t₀ + Φ.F.q * t)) (pderiv 3 (pderiv 3 Q)) / B ^ 2 := by
  have hsc₀ : Φ.sc ≠ 0 := by rw [hsc]; positivity
  rw [Φ.pderiv_normTest, Derivation.map_smul, Φ.pderiv_normTest, smul_smul, smul_eval,
    Φ.eval_normTest_at hq hD hsc₀, hsc]
  field_simp
  rfl

/-- An actual child whole-block fit normalizes at its actual thickness
ratio, keeping both its original polynomial and the parent B unit. -/
theorem fitS_normTest
    (Φ : PFrame) (hq : Φ.F.q ≠ 0) (hD : IsUnit Φ.F.D.det)
    {B δ₀ δ₁ κ : ℝ} (hB : 0 < B) (hδ₀ : 0 < δ₀) (hδ₁ : 0 < δ₁)
    (hsc : Φ.sc = B / δ₀) (Q : MvPolynomial (Fin 4) ℝ) (l : Trajectory)
    (I I' : Set ℝ) (hI : ∀ t ∈ I', Φ.F.t₀ + Φ.F.q * t ∈ I)
    (hfit : Fits κ δ₁ B Q l I) :
    fitS Φ.eb κ (δ₁ / δ₀) (Φ.normTest δ₀ Q) l I' := by
  have hsc₀ : Φ.sc ≠ 0 := by rw [hsc]; positivity
  intro t ht
  obtain ⟨hv, hd, hdd⟩ := hfit _ (hI t ht)
  rw [Φ.eval_normTest_at hq hD hsc₀, Φ.eval_normTest_derivative hq hD hB hδ₀ hsc,
    Φ.eval_normTest_second_derivative hq hD hB hδ₀ hsc]
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos (inv_pos.mpr hδ₀)]
    calc
      _ ≤ δ₀⁻¹ * (κ * δ₁) := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = κ * (δ₁ / δ₀) := by ring
  · rw [abs_div, abs_of_pos hB]
    exact (div_le_iff₀ hB).mpr hd
  · rw [abs_div, abs_mul, abs_of_pos hδ₀, abs_of_pos (sq_pos_of_pos hB)]
    calc
      _ ≤ δ₀ * (κ * B ^ 2 / δ₁) / B ^ 2 := by gcongr
      _ = κ / (δ₁ / δ₀) := by field_simp

/-- The native incidence derivative lower bound is inherited with no
rescaling loss beyond the chosen slack. -/
theorem normTest_derivative_lower
    (Φ : PFrame) (hq : Φ.F.q ≠ 0) (hD : IsUnit Φ.F.D.det)
    {B δ κ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hsc : Φ.sc = B / δ)
    (Q : MvPolynomial (Fin 4) ℝ) (l : Trajectory) (t : ℝ)
    (hder : B / κ ≤ |eval (x l (Φ.F.t₀ + Φ.F.q * t)) (pderiv 3 Q)|) :
    κ⁻¹ ≤ |eval (exS Φ.eb l t) (pderiv 3 (Φ.normTest δ Q))| := by
  rw [Φ.eval_normTest_derivative hq hD hB hδ hsc, abs_div, abs_of_pos hB,
    le_div_iff₀ hB]
  simpa only [div_eq_mul_inv, mul_comm] using hder

end PFrame

/-- Rounding true path depths only changes the three whole-block fit
allowances by the stated two-sided thickness comparisons. -/
theorem fitS_of_thickness_comparison
    {α : Type} (b : α → Fin 6 → ℝ) (l : α) (I : Set ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) {κ K a a' : ℝ}
    (hvalue : κ * a' ≤ K * a) (hder : κ ≤ K) (hcurv : κ / a' ≤ K / a)
    (hfit : fitS b κ a' Q l I) : fitS b K a Q l I := by
  intro t ht
  obtain ⟨hv, hd, hdd⟩ := hfit t ht
  exact ⟨hv.trans hvalue, hd.trans hder, hdd.trans hcurv⟩

end

end Submission.Obl.k4_finite_affine_parent_sources
