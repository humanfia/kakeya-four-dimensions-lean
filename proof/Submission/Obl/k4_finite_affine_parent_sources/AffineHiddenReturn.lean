-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.QuadraticReturn
import Submission.Obl.k4_finite_affine_parent_sources.PolynomialBudgets
import Submission.Lib.K4ContactNormalization.ResidualNormalization

namespace Submission.Obl.k4_finite_affine_parent_sources

open MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

/-- Subtracting an affine function of native time and base preserves the
class of affine trajectories. The accepted residual normalization is used
at residual scale one, so the hidden derivative unit is unchanged. -/
def hiddenShear {α : Type} (b : α → Fin 6 → ℝ) (a : Fin 4 → ℝ) : α → Fin 6 → ℝ :=
  fun l => residualCoeff a 1 (b l)

lemma hiddenShear_base {α : Type} (b : α → Fin 6 → ℝ) (a : Fin 4 → ℝ) (l : α) :
    hiddenShear b a l 0 = b l 0 ∧ hiddenShear b a l 1 = b l 1 ∧
      hiddenShear b a l 3 = b l 3 ∧ hiddenShear b a l 4 = b l 4 := by
  simp [hiddenShear, residualCoeff]

lemma measurable_hiddenShear {α : Type} [MeasurableSpace α]
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (a : Fin 4 → ℝ) :
    Measurable (hiddenShear b a) := by
  unfold hiddenShear residualCoeff
  fun_prop

lemma eval_hiddenShear {α : Type} (b : α → Fin 6 → ℝ) (a : Fin 4 → ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) (l : α) (t : ℝ) :
    eval (exS b l t) (residualLift a 1 Q) = eval (exS (hiddenShear b a) l t) Q := by
  simpa only [one_mul, exS, hiddenShear, point] using eval_residualLift a 1 Q (b l) t

lemma eval_pderiv_hiddenShear {α : Type} (b : α → Fin 6 → ℝ) (a : Fin 4 → ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) (l : α) (t : ℝ) :
    eval (exS b l t) (pderiv (3 : Fin 4) (residualLift a 1 Q)) =
      eval (exS (hiddenShear b a) l t) (pderiv 3 Q) :=
  eval_pderiv_residualLift a one_ne_zero Q (b l) t

lemma eval_second_pderiv_hiddenShear {α : Type} (b : α → Fin 6 → ℝ) (a : Fin 4 → ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) (l : α) (t : ℝ) :
    eval (exS b l t) (pderiv (3 : Fin 4) (pderiv 3 (residualLift a 1 Q))) =
      eval (exS (hiddenShear b a) l t) (pderiv 3 (pderiv 3 Q)) := by
  simpa only [inv_one, one_mul, exS, hiddenShear, point]
    using eval_second_pderiv_residualLift a one_ne_zero Q (b l) t

/-- The affine correction changes neither the whole-block fit constant
nor its thickness or hidden derivative lower bound. -/
lemma fitS_hiddenShear_iff {α : Type} (b : α → Fin 6 → ℝ) (a : Fin 4 → ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) (l : α) (I : Set ℝ) (H c : ℝ) :
    fitS (hiddenShear b a) H c Q l I ↔ fitS b H c (residualLift a 1 Q) l I := by
  simp only [fitS, eval_hiddenShear, eval_pderiv_hiddenShear, eval_second_pderiv_hiddenShear]

namespace PFrame

/-- Original test corresponding to a candidate after an affine hidden
correction. Both substitutions are affine, hence preserve degree two. -/
def affineLift (Φ : PFrame) (a : Fin 4 → ℝ) (δ : ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  Φ.liftE δ (residualLift a 1 Q)

lemma totalDegree_affineLift_le (Φ : PFrame) (a : Fin 4 → ℝ) (δ : ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) : (Φ.affineLift a δ Q).totalDegree ≤ Q.totalDegree :=
  (Φ.totalDegree_liftE_le δ _).trans (residualLift_degree a 1 Q)

lemma fitS_affine_return (Φ : PFrame) (hq : Φ.F.q ≠ 0) (a : Fin 4 → ℝ)
    (δ B c c₀ H C : ℝ) (hδ : 0 < δ) (hB : 0 ≤ B) (hc : 0 < c) (hc₀ : 0 < c₀)
    (hsc : Φ.sc = B / δ) (Q : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (I I' : Set ℝ)
    (hI : ∀ t ∈ I, (t - Φ.F.t₀) / Φ.F.q ∈ I')
    (hfit : fitS (hiddenShear Φ.eb a) H c Q l I')
    (hvalue : δ * (H * c) ≤ C * c₀) (hfirst : H ≤ C)
    (hsecond : H * c₀ ≤ C * δ * c) :
    Fits C c₀ B (Φ.affineLift a δ Q) l I :=
  Φ.fitS_return hq δ B c c₀ H C hδ hB hc hc₀ hsc _ l I I' hI
    ((fitS_hiddenShear_iff Φ.eb a Q l I' H c).mp hfit) hvalue hfirst hsecond

lemma affine_lower_return (Φ : PFrame) (hq : Φ.F.q ≠ 0) (a : Fin 4 → ℝ)
    (δ B H C : ℝ) (hδ : δ ≠ 0) (hB : 0 ≤ B) (hH : 0 < H) (hHC : H ≤ C)
    (hsc : Φ.sc = B / δ) (Q : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ)
    (hlower : H⁻¹ ≤ |eval (exS (hiddenShear Φ.eb a) l ((t - Φ.F.t₀) / Φ.F.q))
      (pderiv (3 : Fin 4) Q)|) :
    B / C ≤ |eval (Submission.Lib.K4XInterface.gx l t)
      (pderiv (3 : Fin 4) (Φ.affineLift a δ Q))| := by
  apply Φ.lower_return hq δ B H C hδ hB hH hHC hsc (residualLift a 1 Q) l t
  rwa [eval_pderiv_hiddenShear]

/-- The affine correction has an explicit coefficient cost, so it fits
the fixed original-coordinate polynomial budget chosen before epsilon. -/
lemma coeff_affineLift_quadratic_le
    (Φ : PFrame) (a : Fin 4 → ℝ) (δ : ℝ) (Q : MvPolynomial (Fin 4) ℝ)
    (hQ : Q.totalDegree ≤ 2) (H : ℝ) (hcoeff : ∀ e, |Q.coeff e| ≤ H)
    (e : Fin 4 →₀ ℕ) :
    |(Φ.affineLift a δ Q).coeff e| ≤
      81 * |δ| * H * residualBudget a 1 ^ 2 * Φ.substBudget ^ 2 := by
  have hR : (residualLift a 1 Q).totalDegree ≤ 2 := (residualLift_degree a 1 Q).trans hQ
  have hL : coeffL1 Q ≤ 81 * H := by
    simpa using coeffL1_le_of_coeff_le Q hQ H hcoeff
  have hRL : coeffL1 (residualLift a 1 Q) ≤ coeffL1 Q * residualBudget a 1 ^ 2 := by
    unfold residualLift
    apply (coeffL1_C_mul_le _ _).trans
    simp only [abs_one, one_mul]
    apply (coeffL1_bind₁_le (residualSubst a 1) (residualBudget a 1)
      (one_le_residualBudget a 1) (coeffL1_residualSubst a 1) Q).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (one_le_residualBudget a 1) hQ) (coeffL1_nonneg Q)
  calc
    _ ≤ coeffL1 (Φ.affineLift a δ Q) := abs_coeff_le_coeffL1 _ _
    _ ≤ |δ| * (coeffL1 (residualLift a 1 Q) * Φ.substBudget ^ (residualLift a 1 Q).totalDegree) :=
      Φ.coeffL1_liftE_le δ _
    _ ≤ |δ| * (coeffL1 (residualLift a 1 Q) * Φ.substBudget ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ Φ.one_le_substBudget hR) (coeffL1_nonneg _))
        (abs_nonneg _)
    _ ≤ |δ| * ((coeffL1 Q * residualBudget a 1 ^ 2) * Φ.substBudget ^ 2) := by
      gcongr
    _ ≤ |δ| * (((81 * H) * residualBudget a 1 ^ 2) * Φ.substBudget ^ 2) := by
      gcongr
    _ = _ := by ring

end PFrame

end

end Submission.Obl.k4_finite_affine_parent_sources
