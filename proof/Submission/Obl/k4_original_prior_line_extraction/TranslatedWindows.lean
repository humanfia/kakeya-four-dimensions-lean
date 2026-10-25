import Submission.Obl.k4_original_prior_line_extraction.FiniteDensities

namespace Submission.Obl.k4_original_prior_line_extraction

open MeasureTheory Set Filter
open scoped ENNReal

abbrev Base := EuclideanSpace ℝ (Fin 3)

/-- A fixed short time scale leaves room for the required extended domain. -/
noncomputable def windowStep : ℝ := 1 / 16

lemma windowStep_pos : 0 < windowStep := by norm_num [windowStep]

noncomputable def windowVolume : ℝ :=
  (volume (Metric.closedBall (0 : Base) 1)).toReal + 1

lemma windowVolume_pos : 0 < windowVolume := by
  unfold windowVolume
  positivity

noncomputable def windowMass {A : Type*} [Fintype A]
    (f : A → Base → ℝ≥0∞) (v y : Base) : ℝ≥0∞ :=
  ∑ a, ∫⁻ t in Icc (0 : ℝ) 1, f a (y + (windowStep * t) • v)

lemma measurable_windowMass {A : Type*} [Fintype A]
    {f : A → Base → ℝ≥0∞} (hf : ∀ a, Measurable (f a)) (v : Base) :
    Measurable (windowMass f v) := by
  apply Finset.measurable_sum
  intro a _
  exact ((hf a).comp (by fun_prop :
    Measurable (fun p : Base × ℝ => p.1 + (windowStep * p.2) • v))).lintegral_prod_right'

/-- Averaging translated windows reproduces the entire original base mass. -/
lemma lintegral_windowMass {A : Type*} [Fintype A]
    {f : A → Base → ℝ≥0∞} (hf : ∀ a, Measurable (f a)) (v : Base) :
    (∫⁻ y, windowMass f v y) = ∑ a, ∫⁻ x, f a x := by
  unfold windowMass
  have hmeas (a : A) : Measurable
      (fun y : Base => ∫⁻ t in Icc (0 : ℝ) 1, f a (y + (windowStep * t) • v)) :=
    ((hf a).comp (by fun_prop :
      Measurable (fun p : Base × ℝ => p.1 + (windowStep * p.2) • v))).lintegral_prod_right'
  rw [lintegral_finsetSum Finset.univ (fun a _ => hmeas a)]
  apply Finset.sum_congr rfl
  intro a _
  rw [lintegral_lintegral_swap
    (μ := (volume : Measure Base)) (ν := (volume : Measure ℝ).restrict (Icc 0 1))
    (f := fun y t => f a (y + (windowStep * t) • v))
    (((hf a).comp (by fun_prop :
      Measurable (fun p : Base × ℝ => p.1 + (windowStep * p.2) • v))).aemeasurable)]
  simp only [lintegral_add_right_eq_self]
  simp [Real.volume_Icc]

lemma window_start_bound {v y : Base} (hv : ‖v‖ = 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hx : ‖y + (windowStep * t) • v‖ ≤ (1 : ℝ) / 2) :
    ‖y‖ ≤ (9 : ℝ) / 16 := by
  have hrt : 0 ≤ windowStep * t := mul_nonneg windowStep_pos.le ht.1
  have hn : ‖(windowStep * t) • v‖ ≤ windowStep := by
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg hrt]
    exact mul_le_of_le_one_right windowStep_pos.le ht.2
  have hy := norm_sub_le (y + (windowStep * t) • v) ((windowStep * t) • v)
  simp only [add_sub_cancel_right] at hy
  calc
    ‖y‖ ≤ ‖y + (windowStep * t) • v‖ + ‖(windowStep * t) • v‖ := hy
    _ ≤ (1 : ℝ) / 2 + windowStep := add_le_add hx hn
    _ = (9 : ℝ) / 16 := by norm_num [windowStep]

lemma window_point_bound {v y : Base} (hv : ‖v‖ = 1)
    (hy : ‖y‖ ≤ (9 : ℝ) / 16) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖y + (windowStep * t) • v‖ ≤ (3 : ℝ) / 4 := by
  have hrt : 0 ≤ windowStep * t := mul_nonneg windowStep_pos.le ht.1
  have hn : ‖(windowStep * t) • v‖ ≤ windowStep := by
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg hrt]
    exact mul_le_of_le_one_right windowStep_pos.le ht.2
  calc
    ‖y + (windowStep * t) • v‖ ≤ ‖y‖ + ‖(windowStep * t) • v‖ := norm_add_le _ _
    _ ≤ (9 : ℝ) / 16 + windowStep := add_le_add hy hn
    _ ≤ (3 : ℝ) / 4 := by norm_num [windowStep]

lemma windowMass_eq_zero_outside {A : Type*} [Fintype A]
    {f : A → Base → ℝ≥0∞} (v : Base) (hv : ‖v‖ = 1)
    (hsupp : ∀ a x, f a x ≠ 0 → ‖x‖ ≤ (1 : ℝ) / 2)
    {y : Base} (hy : ¬ ‖y‖ ≤ (9 : ℝ) / 16) : windowMass f v y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a _
  calc
    (∫⁻ t in Icc (0 : ℝ) 1, f a (y + (windowStep * t) • v)) =
        ∫⁻ t in Icc (0 : ℝ) 1, (0 : ℝ≥0∞) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      by_contra hn
      exact hy (window_start_bound hv ht (hsupp a _ hn))
    _ = 0 := by simp

lemma windowMass_le {A : Type*} [Fintype A]
    {f : A → Base → ℝ≥0∞} (hf : ∀ a, Measurable (f a)) (v y : Base)
    (S : ℝ≥0∞) (hbound : ∀ x, ∑ a, f a x ≤ S) : windowMass f v y ≤ S := by
  rw [windowMass, ← lintegral_finsetSum (μ := (volume : Measure ℝ).restrict (Icc 0 1))
    (f := fun a t => f a (y + (windowStep * t) • v)) Finset.univ
    (fun a _ => (hf a).comp (by fun_prop :
      Measurable (fun t : ℝ => y + (windowStep * t) • v)))]
  calc
    (∫⁻ t in Icc (0 : ℝ) 1, ∑ a, f a (y + (windowStep * t) • v)) ≤
        ∫⁻ t in Icc (0 : ℝ) 1, S := lintegral_mono (fun t => hbound _)
    _ = S := by simp [Real.volume_Icc]

/-- A translated short line has a fixed fraction of the total mass. -/
lemma exists_mass_window {A : Type*} [Fintype A]
    {f : A → Base → ℝ≥0∞} (hf : ∀ a, Measurable (f a))
    (v : Base) (hv : ‖v‖ = 1)
    (hsupp : ∀ a x, f a x ≠ 0 → ‖x‖ ≤ (1 : ℝ) / 2)
    {q : ℝ} (hq : 0 < q) (hmass : ENNReal.ofReal q ≤ ∑ a, ∫⁻ x, f a x) :
    ∃ y : Base, ‖y‖ ≤ (9 : ℝ) / 16 ∧
      ENNReal.ofReal (q / windowVolume) ≤ windowMass f v y := by
  classical
  by_contra h
  push_neg at h
  let C : Set Base := Metric.closedBall 0 1
  have hC : MeasurableSet C := measurableSet_closedBall
  have hvol : volume C ≠ ∞ := measure_closedBall_lt_top.ne
  have hle (y : Base) : windowMass f v y ≤
      C.indicator (fun _ => ENNReal.ofReal (q / windowVolume)) y := by
    by_cases hy : ‖y‖ ≤ (9 : ℝ) / 16
    · have hyC : y ∈ C := by
        change dist y 0 ≤ 1
        simpa only [dist_zero_right] using hy.trans (by norm_num : (9 : ℝ) / 16 ≤ 1)
      rw [indicator_of_mem hyC]
      exact (h y hy).le
    · rw [windowMass_eq_zero_outside v hv hsupp hy]
      exact bot_le
  have hlt : ENNReal.ofReal (q / windowVolume) * volume C < ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_toReal hvol, ← ENNReal.ofReal_mul
      (div_nonneg hq.le windowVolume_pos.le)]
    apply (ENNReal.ofReal_lt_ofReal_iff hq).mpr
    have hvolnonneg := ENNReal.toReal_nonneg (a := volume C)
    have hVC : (volume C).toReal < windowVolume := by
      dsimp [C, windowVolume]
      linarith
    calc
      q / windowVolume * (volume C).toReal < q / windowVolume * windowVolume :=
        mul_lt_mul_of_pos_left hVC (div_pos hq windowVolume_pos)
      _ = q := div_mul_cancel₀ q windowVolume_pos.ne'
  have hcontra : ENNReal.ofReal q < ENNReal.ofReal q := calc
    ENNReal.ofReal q ≤ ∑ a, ∫⁻ x, f a x := hmass
    _ = ∫⁻ y, windowMass f v y := (lintegral_windowMass hf v).symm
    _ ≤ ∫⁻ y, C.indicator (fun _ => ENNReal.ofReal (q / windowVolume)) y :=
      lintegral_mono hle
    _ = ENNReal.ofReal (q / windowVolume) * volume C := by
      rw [lintegral_indicator hC, setLIntegral_const]
    _ < ENNReal.ofReal q := hlt
  exact lt_irrefl _ hcontra

end Submission.Obl.k4_original_prior_line_extraction
