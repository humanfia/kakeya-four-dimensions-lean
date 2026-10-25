import Submission.Obl.k4_original_prior_line_extraction.TranslatedWindows
import Submission.Obl.k4_matching_switching_target_certificate.JetBins

namespace Submission.Obl.k4_original_prior_line_extraction

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable def lineFunction (F : Base → ℝ) (v y : Base) (M : ℝ) : ℝ → ℝ :=
  fun t => M⁻¹ * F (y + (windowStep * t) • v)

lemma directionalJet_shift (F : Base → ℝ) (v y : Base) (m : ℕ) (s : ℝ) :
    iteratedDeriv m (fun u : ℝ => F ((y + s • v) + u • v)) 0 =
      iteratedDeriv m (fun u : ℝ => F (y + u • v)) s := by
  have heq : (fun u : ℝ => F ((y + s • v) + u • v)) =
      (fun u : ℝ => (fun z : ℝ => F (y + z • v)) (s + u)) := by
    funext u
    change F (y + s • v + u • v) = F (y + (s + u) • v)
    rw [add_smul, add_assoc]
  rw [heq]
  have h := congrFun (iteratedDeriv_comp_const_add m (fun u : ℝ => F (y + u • v)) s) 0
  simpa only [add_zero] using h

lemma lineFunction_jet (F : Base → ℝ) (v y : Base) (M : ℝ) (m : ℕ) (t : ℝ) :
    iteratedDeriv m (lineFunction F v y M) t =
      M⁻¹ * windowStep ^ m *
        iteratedDeriv m (fun u : ℝ => F ((y + (windowStep * t) • v) + u • v)) 0 := by
  unfold lineFunction
  rw [iteratedDeriv_const_mul_field]
  have h := congrFun (Submission.Obl.k4_matching_switching_target_certificate.iteratedDeriv_comp_affine
    (fun u : ℝ => F (y + u • v)) 0 windowStep m) t
  simp only [zero_add] at h
  rw [h, directionalJet_shift]
  ring

lemma lineFunction_contDiffOn {F : Base → ℝ} (v y : Base) (M : ℝ) (N : ℕ)
    (hf : ContDiffOn ℝ N (fun s : ℝ => F (y + s • v)) (Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ N (lineFunction F v y M) (Ioo (-1 : ℝ) 2) := by
  have haff : ContDiff ℝ N (fun t : ℝ => windowStep * t) := by fun_prop
  have hmaps : MapsTo (fun t : ℝ => windowStep * t) (Ioo (-1 : ℝ) 2) (Ioo (-1 : ℝ) 1) := by
    intro t ht
    dsimp [windowStep]
    constructor <;> linarith [ht.1, ht.2]
  exact contDiffOn_const.mul (hf.comp haff.contDiffOn hmaps)

lemma lineFunction_bound {F : Base → ℝ} {v y : Base} (hv : ‖v‖ = 1)
    (hy : ‖y‖ ≤ (9 : ℝ) / 16) {M T : ℝ} (hM : 0 < M) (hT : 0 ≤ T) (m : ℕ)
    (hbound : ∀ x : Base, ‖x‖ ≤ (3 : ℝ) / 4 →
      |iteratedDeriv m (fun u : ℝ => F (x + u • v)) 0| ≤ T * M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |iteratedDeriv m (lineFunction F v y M) t| ≤ T := by
  have hr : windowStep ≤ 1 := by norm_num [windowStep]
  have hrpow : windowStep ^ m ≤ 1 := pow_le_one₀ windowStep_pos.le hr
  calc
    |iteratedDeriv m (lineFunction F v y M) t| =
        M⁻¹ * windowStep ^ m *
          |iteratedDeriv m (fun u : ℝ => F ((y + (windowStep * t) • v) + u • v)) 0| := by
      rw [lineFunction_jet, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hM),
        abs_of_nonneg (pow_nonneg windowStep_pos.le m)]
    _ ≤ M⁻¹ * windowStep ^ m * (T * M) :=
      mul_le_mul_of_nonneg_left (hbound _ (window_point_bound hv hy ht)) (mul_nonneg (inv_nonneg.mpr hM.le) (pow_nonneg windowStep_pos.le m))
    _ = windowStep ^ m * T := by field_simp
    _ ≤ T := mul_le_of_le_one_left hT hrpow

lemma lineFunction_gap {F G : Base → ℝ} (v y : Base) {M δ : ℝ}
    (hM : 0 < M) (hδ : 0 ≤ δ) {m K : ℕ} (hmK : m ≤ K) {t : ℝ}
    (hgap : δ * M ≤
      |iteratedDeriv m (fun u : ℝ => F ((y + (windowStep * t) • v) + u • v)) 0 -
        iteratedDeriv m (fun u : ℝ => G ((y + (windowStep * t) • v) + u • v)) 0|) :
    windowStep ^ K * δ ≤
      |iteratedDeriv m (lineFunction F v y M) t -
        iteratedDeriv m (lineFunction G v y M) t| := by
  have hr : windowStep ≤ 1 := by norm_num [windowStep]
  have hrpow : windowStep ^ K ≤ windowStep ^ m :=
    pow_le_pow_of_le_one windowStep_pos.le hr hmK
  calc
    windowStep ^ K * δ ≤ windowStep ^ m * δ :=
      mul_le_mul_of_nonneg_right hrpow hδ
    _ = M⁻¹ * windowStep ^ m * (δ * M) := by field_simp
    _ ≤ M⁻¹ * windowStep ^ m *
        |iteratedDeriv m (fun u : ℝ => F ((y + (windowStep * t) • v) + u • v)) 0 -
          iteratedDeriv m (fun u : ℝ => G ((y + (windowStep * t) • v) + u • v)) 0| :=
      mul_le_mul_of_nonneg_left hgap
        (mul_nonneg (inv_nonneg.mpr hM.le) (pow_nonneg windowStep_pos.le m))
    _ = |iteratedDeriv m (lineFunction F v y M) t -
        iteratedDeriv m (lineFunction G v y M) t| := by
      rw [lineFunction_jet, lineFunction_jet, ← mul_sub,
        abs_mul, abs_of_nonneg
          (mul_nonneg (inv_nonneg.mpr hM.le) (pow_nonneg windowStep_pos.le m))]

end Submission.Obl.k4_original_prior_line_extraction
