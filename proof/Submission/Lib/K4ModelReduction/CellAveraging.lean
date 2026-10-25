import Submission.Lib.K4ModelReduction.PolynomialTranslation

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-!
Uniform redistribution inside mesh cells, the one-dimensional averaging
step in the supplied paper's joint base-flattening lemma.
-/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

def meshCell (ρ x : ℝ) : Set ℝ :=
  Icc (ρ * (⌊x / ρ⌋ : ℝ)) (ρ * (⌊x / ρ⌋ : ℝ) + ρ)

theorem meshCell_volume (ρ x : ℝ) : volume (meshCell ρ x) = ENNReal.ofReal ρ := by
  rw [meshCell, Real.volume_Icc]
  congr 1
  ring

theorem mem_meshCell {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) : x ∈ meshCell ρ x := by
  have hleft := Int.floor_le (x / ρ)
  have hright := Int.lt_floor_add_one (x / ρ)
  rw [le_div_iff₀ hρ] at hleft
  rw [div_lt_iff₀ hρ] at hright
  constructor <;> nlinarith

private theorem meshCell_dist_le {ρ x y z : ℝ}
    (hy : y ∈ meshCell ρ x) (hz : z ∈ meshCell ρ x) : dist y z ≤ ρ := by
  have hh := Real.dist_le_of_mem_Icc hy hz
  simpa only [add_sub_cancel_left] using hh

/-- Uniform averaging of a density over the cell containing `x`. -/
noncomputable def meshAverage (f : ℝ → ℝ) (ρ x : ℝ) : ℝ :=
  ∫ y, f y ∂ProbabilityTheory.cond volume (meshCell ρ x)

theorem meshCell_law_isProbabilityMeasure {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    IsProbabilityMeasure (ProbabilityTheory.cond volume (meshCell ρ x)) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (by rw [meshCell_volume]; positivity) (by rw [meshCell_volume]; exact ENNReal.ofReal_ne_top)

theorem meshAverage_eq_integral_indicator (f : ℝ → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    meshAverage f ρ x = ρ⁻¹ * ∫ y, (meshCell ρ x).indicator f y := by
  have hcellm : MeasurableSet (meshCell ρ x) := measurableSet_Icc
  rw [meshAverage, ProbabilityTheory.cond, integral_smul_measure, meshCell_volume,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hρ.le, smul_eq_mul,
    integral_indicator hcellm]

/-- The cell-average table is jointly measurable in the remaining
parameters and the base coordinate being averaged. -/
theorem meshAverage_measurable {Y : Type*} [MeasurableSpace Y]
    (f : Y → ℝ → ℝ) (hf : Measurable (Function.uncurry f))
    {ρ : ℝ} (hρ : 0 < ρ) :
    Measurable (fun z : Y × ℝ => meshAverage (f z.1) ρ z.2) := by
  let T : Set ((Y × ℝ) × ℝ) := {q | q.2 ∈ meshCell ρ q.1.2}
  have hanchor : Measurable (fun q : (Y × ℝ) × ℝ => ρ * (⌊q.1.2 / ρ⌋ : ℝ)) := by
    fun_prop
  have hT : MeasurableSet T :=
    (measurableSet_le hanchor measurable_snd).inter
      (measurableSet_le measurable_snd (hanchor.add_const ρ))
  let G : ((Y × ℝ) × ℝ) → ℝ := T.indicator (fun q => f q.1.1 q.2)
  have hG : Measurable G :=
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).indicator hT
  have hI : Measurable (fun z : Y × ℝ => ∫ t : ℝ, G (z, t)) :=
    hG.stronglyMeasurable.integral_prod_right'.measurable
  have heq : (fun z : Y × ℝ => meshAverage (f z.1) ρ z.2) =
      (fun z => ρ⁻¹ * ∫ t : ℝ, G (z, t)) := by
    funext z
    rw [meshAverage_eq_integral_indicator _ hρ]
    rfl
  rw [heq]
  exact measurable_const.mul hI

theorem meshAverage_abs_le (f : ℝ → ℝ) {ρ M : ℝ} (hρ : 0 < ρ)
    (hbound : ∀ y, |f y| ≤ M) (x : ℝ) : |meshAverage f ρ x| ≤ M := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond volume (meshCell ρ x)) :=
    meshCell_law_isProbabilityMeasure hρ x
  have hh := norm_integral_le_of_norm_le_const
    (μ := ProbabilityTheory.cond volume (meshCell ρ x))
    (Filter.Eventually.of_forall (fun y => show ‖f y‖ ≤ M by simpa only [Real.norm_eq_abs] using hbound y))
  simpa only [meshAverage, Real.norm_eq_abs, measureReal_def, measure_univ,
    ENNReal.toReal_one, mul_one] using hh

theorem meshAverage_eq_of_constant (f : ℝ → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (x c : ℝ)
    (hconst : ∀ y ∈ meshCell ρ x, f y = c) : meshAverage f ρ x = c := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond volume (meshCell ρ x)) :=
    meshCell_law_isProbabilityMeasure hρ x
  apply integral_eq_const
  exact ProbabilityTheory.ae_cond_of_forall_mem measurableSet_Icc hconst

/-- Averaging a bounded fiber inside mesh cells changes it only in cells
next to a boundary, with total error linear in mesh width and boundary count. -/
theorem cell_averaging_error_bound
    (f : ℝ → ℝ) (F : Finset ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M)
    (hconst : ∀ x y, (∀ a ∈ F, dist x y < dist x a) → f x = f y)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ x : ℝ, ENNReal.ofReal |meshAverage f ρ x - f x| ≤
      ENNReal.ofReal (4 * M * (F.card : ℝ) * ρ) := by
  classical
  let S : Set ℝ := ⋃ a : F, closedBall (a : ℝ) ρ
  have hSm : MeasurableSet S := MeasurableSet.iUnion fun _ => measurableSet_closedBall
  have heq (x : ℝ) (hx : x ∉ S) : meshAverage f ρ x = f x := by
    apply meshAverage_eq_of_constant f hρ x (f x)
    intro y hy
    apply Eq.symm
    apply hconst
    intro a ha
    have hfar : ρ < dist x a := lt_of_not_ge (fun hle => hx (mem_iUnion.mpr ⟨⟨a, ha⟩, hle⟩))
    exact (meshCell_dist_le (mem_meshCell hρ x) hy).trans_lt hfar
  have hpoint (x : ℝ) : ENNReal.ofReal |meshAverage f ρ x - f x| ≤
      S.indicator (fun _ => ENNReal.ofReal (2 * M)) x := by
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      apply ENNReal.ofReal_le_ofReal
      calc
        |meshAverage f ρ x - f x| ≤ |meshAverage f ρ x| + |f x| := abs_sub _ _
        _ ≤ M + M := add_le_add (meshAverage_abs_le f hρ hbound x) (hbound x)
        _ = 2 * M := by ring
    · rw [indicator_of_notMem hx, heq x hx, sub_self, abs_zero, ENNReal.ofReal_zero]
  have hvolume : volume S ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal (2 * ρ) := by
    calc
      volume S ≤ ∑ a : F, volume (closedBall (a : ℝ) ρ) := measure_iUnion_fintype_le _ _
      _ = _ := by
        simp only [Real.volume_closedBall, Finset.sum_const, Finset.card_univ,
          Fintype.card_coe, nsmul_eq_mul]
  calc
    _ ≤ ∫⁻ x : ℝ, S.indicator (fun _ => ENNReal.ofReal (2 * M)) x := lintegral_mono hpoint
    _ = ENNReal.ofReal (2 * M) * volume S := lintegral_indicator_const hSm _
    _ ≤ ENNReal.ofReal (2 * M) * ((F.card : ℝ≥0∞) * ENNReal.ofReal (2 * ρ)) :=
      mul_le_mul_right hvolume _
    _ = _ := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- Uniform-cell averaging of a polynomial sign table has error bounded
by mesh width times total polynomial degree, independently of coefficients. -/
theorem polynomial_cell_averaging_error_bound
    {ι : Type*} [Fintype ι] (p : ι → Polynomial ℝ)
    (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x, |f x| ≤ M)
    (hdepend : ∀ x y, (∀ i, (p i).eval x ≤ 0 ↔ (p i).eval y ≤ 0) → f x = f y)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ x : ℝ, ENNReal.ofReal |meshAverage f ρ x - f x| ≤
      ENNReal.ofReal (4 * M * ((∑ i, (p i).natDegree : ℕ) : ℝ) * ρ) := by
  have hreal : ((polynomialBoundaries p).card : ℝ) ≤ ((∑ i, (p i).natDegree : ℕ) : ℝ) := by
    exact_mod_cast polynomialBoundaries_card_le p
  refine (cell_averaging_error_bound f (polynomialBoundaries p) M hM hbound
    (polynomial_pattern_locally_constant p f hdepend) hρ).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hreal (by positivity)) hρ.le

end Submission.Lib.K4ModelReduction
