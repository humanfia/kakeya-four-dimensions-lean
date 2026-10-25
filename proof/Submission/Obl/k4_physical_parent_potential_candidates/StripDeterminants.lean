import Submission.Lib.K4OriginalCellSampling.GeneralPosition
import Submission.Lib.K4ContinuousKakeya.Incidence

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MeasureTheory Set
open Submission.Lib.K4OriginalCellSampling.Sampling
open scoped ENNReal

noncomputable section

/-- The strip test gives determinant-success mass for the original finite law.
Only the proof uses a probability law; the conclusion retains its original mass. -/
theorem triple_determinant_mass_of_strip_breadth
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (v : Ω → EuclideanSpace ℝ (Fin 2)) (hv : Measurable v)
    {δ : ℝ} (hδ : 0 < δ) (κ : ℝ≥0∞)
    (hstrip : ∀ (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ), ‖n‖ = 1 →
      μ {p | |inner ℝ n (v p) - t| ≤ δ} ≤ κ * μ univ) :
    (1 - 54 * κ) * (μ univ) ^ 3 ≤
      Measure.pi (fun _ : Fin 3 => μ)
        {p | δ ^ 2 ≤ |tripleDet (v (p 0)) (v (p 1)) (v (p 2))|} := by
  by_cases hzero : μ univ = 0
  · simp [hzero]
  let ν : Measure Ω := (μ univ)⁻¹ • μ
  have hmassfin : μ univ ≠ ⊤ := measure_ne_top μ _
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hzero hmassfin⟩
  let law : Measure (EuclideanSpace ℝ (Fin 2)) := ν.map v
  haveI hlaw : IsProbabilityMeasure law := ⟨by
    dsimp [law]
    rw [Measure.map_apply hv MeasurableSet.univ, preimage_univ]
    exact measure_univ⟩
  have hbreadth : StripBreadth law δ κ := by
    intro n t hn
    have hm : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) |
        |inner ℝ n x - t| ≤ δ} := by
      exact measurableSet_le (by fun_prop) measurable_const
    change (ν.map v) _ ≤ _
    rw [Measure.map_apply hv hm]
    change (μ univ)⁻¹ * μ {p | |inner ℝ n (v p) - t| ≤ δ} ≤ κ
    calc
      _ ≤ (μ univ)⁻¹ * (κ * μ univ) := mul_le_mul' le_rfl (hstrip n t hn)
      _ = κ := by rw [mul_left_comm, ENNReal.inv_mul_cancel hzero hmassfin, mul_one]
  have hbad := general_position_of_breadth law hδ hbreadth 2
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one, show (2 : ℝ≥0∞) * 3 ^ 3 = 54 by norm_num] at hbad
  let G : Set (Fin 3 → EuclideanSpace ℝ (Fin 2)) :=
    {p | δ ^ 2 ≤ |tripleDet (p 0) (p 1) (p 2)|}
  have hsub : Gᶜ ⊆ {p : Fin 3 → EuclideanSpace ℝ (Fin 2) |
      ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        |tripleDet (p i) (p j) (p k)| < δ ^ 2} := by
    intro p hp
    exact ⟨0, 1, 2, by decide, by decide, by decide, lt_of_not_ge hp⟩
  have hcompl : Measure.pi (fun _ : Fin 3 => law) Gᶜ ≤ 54 * κ :=
    (measure_mono hsub).trans hbad
  have hprob : 1 - 54 * κ ≤ Measure.pi (fun _ : Fin 3 => law) G := by
    apply tsub_le_iff_right.mpr
    calc
      1 = Measure.pi (fun _ : Fin 3 => law) univ := measure_univ.symm
      _ ≤ Measure.pi (fun _ : Fin 3 => law) G +
          Measure.pi (fun _ : Fin 3 => law) Gᶜ := by
        rw [← union_compl_self G]
        exact measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl hcompl
  have hG : MeasurableSet G := by
    dsimp [G, tripleDet, lift]
    exact measurableSet_le measurable_const (by fun_prop)
  have hmap : Measurable fun p : Fin 3 → Ω => fun i => v (p i) :=
    Measurable.of_eval fun i => hv.comp (measurable_pi_apply i)
  have hgood : 1 - 54 * κ ≤ Measure.pi (fun _ : Fin 3 => ν)
      {p | δ ^ 2 ≤ |tripleDet (v (p 0)) (v (p 1)) (v (p 2))|} := by
    rw [← Measure.pi_map_pi (fun _ : Fin 3 => hv.aemeasurable),
      Measure.map_apply hmap hG] at hprob
    exact hprob
  have hμν : (μ univ).toNNReal • ν = μ := by
    dsimp [ν]
    rw [ENNReal.smul_def, smul_smul, ENNReal.coe_toNNReal hmassfin,
      ENNReal.mul_inv_cancel hzero hmassfin, one_smul]
  have hscale := Submission.Lib.K4ContinuousKakeya.pi_smul
    (fun _ : Fin 3 => ν) (μ univ).toNNReal
  simp only [hμν, Fintype.card_fin, ENNReal.coe_toNNReal hmassfin] at hscale
  rw [hscale, Measure.smul_apply, smul_eq_mul]
  simpa only [mul_comm] using mul_le_mul' (show (μ univ) ^ 3 ≤ (μ univ) ^ 3 from le_rfl) hgood

/-- Unit directions of the actual base lines. -/
def unitLift (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  ‖lift v‖⁻¹ • lift v

theorem norm_lift_sq (v : EuclideanSpace ℝ (Fin 2)) :
    ‖lift v‖ ^ 2 = 1 + ‖v‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, lift, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

theorem one_le_norm_lift (v : EuclideanSpace ℝ (Fin 2)) : 1 ≤ ‖lift v‖ := by
  nlinarith [norm_lift_sq v, norm_nonneg (lift v), sq_nonneg ‖v‖]

theorem norm_lift_le (v : EuclideanSpace ℝ (Fin 2)) : ‖lift v‖ ≤ 1 + ‖v‖ := by
  nlinarith [norm_lift_sq v, norm_nonneg (lift v), norm_nonneg v]

theorem norm_unitLift (v : EuclideanSpace ℝ (Fin 2)) : ‖unitLift v‖ = 1 := by
  have hpos : 0 < ‖lift v‖ := lt_of_lt_of_le one_pos (one_le_norm_lift v)
  simp only [unitLift, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ hpos.ne'

theorem measurable_unitLift : Measurable unitLift := by
  have hlift : Continuous lift := by
    unfold Submission.Lib.K4OriginalCellSampling.Sampling.lift
    fun_prop
  exact ((hlift.norm.inv₀ (fun v =>
    (lt_of_lt_of_le one_pos (one_le_norm_lift v)).ne')).smul hlift).measurable

/-- A transverse triple remains transverse after normalizing each base direction.
The speed envelope costs exactly three powers. -/
theorem unitLift_determinant_lower_bound
    (v : Fin 3 → EuclideanSpace ℝ (Fin 2)) {K δ : ℝ}
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hbound : ∀ i, ‖v i‖ ≤ K)
    (hdet : δ ^ 2 ≤ |tripleDet (v 0) (v 1) (v 2)|) :
    δ ^ 2 / (1 + K) ^ 3 ≤
      |(Matrix.of fun i j : Fin 3 => unitLift (v i) j).det| := by
  have hden : 0 < 1 + K := by linarith
  have hnorm (i : Fin 3) : 0 < ‖lift (v i)‖ :=
    lt_of_lt_of_le one_pos (one_le_norm_lift _)
  have hnorm_le (i : Fin 3) : ‖lift (v i)‖ ≤ 1 + K :=
    (norm_lift_le _).trans (by linarith [hbound i])
  have hrow : (![lift (v 0), lift (v 1), lift (v 2)] :
      Fin 3 → EuclideanSpace ℝ (Fin 3)) = fun i => lift (v i) := by
    funext i
    fin_cases i <;> rfl
  have heq : (Matrix.of fun i j : Fin 3 => unitLift (v i) j).det =
      (∏ i, ‖lift (v i)‖⁻¹) * tripleDet (v 0) (v 1) (v 2) := by
    simpa only [unitLift, PiLp.smul_apply, smul_eq_mul, tripleDet, hrow, Matrix.of_apply] using
      Matrix.det_mul_column (fun i : Fin 3 => ‖lift (v i)‖⁻¹)
        (Matrix.of fun i j : Fin 3 => lift (v i) j)
  rw [heq, abs_mul, Finset.abs_prod]
  have hprod : (1 + K)⁻¹ ^ 3 ≤ ∏ i : Fin 3, |‖lift (v i)‖⁻¹| := by
    calc
      _ = ∏ _i : Fin 3, (1 + K)⁻¹ := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ => by
        rw [abs_inv, abs_norm]
        exact inv_le_inv₀ hden (hnorm i) |>.mpr (hnorm_le i)
  calc
    _ = ((1 + K)⁻¹ ^ 3) * δ ^ 2 := by simp [div_eq_mul_inv, inv_pow, mul_comm]
    _ ≤ (∏ i : Fin 3, |‖lift (v i)‖⁻¹|) * |tripleDet (v 0) (v 1) (v 2)| :=
      mul_le_mul hprod hdet (sq_nonneg _) (Finset.prod_nonneg (fun _ _ => abs_nonneg _))

/-- Breadth in one actual cell supplies the determinant mass consumed by MK3. -/
theorem unit_determinant_mass_in_cell
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S)
    (v : Ω → EuclideanSpace ℝ (Fin 2)) (hv : Measurable v)
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hbound : ∀ p ∈ S, ‖v p‖ ≤ K)
    (κ : ℝ≥0∞) (hκ : κ ≤ 1 / 1000)
    (hstrip : ∀ (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ), ‖n‖ = 1 →
      (μ.restrict S) {p | |inner ℝ n (v p) - t| ≤ δ} ≤ κ * μ S) :
    ENNReal.ofReal (((1 / 2 : ℝ) * μ.real S) ^ 3) ≤
      Measure.pi (fun _ : Fin 3 => μ)
        {p | (∀ i, p i ∈ S) ∧ δ ^ 2 / (1 + K) ^ 3 ≤
          |(Matrix.of fun i j : Fin 3 => unitLift (v (p i)) j).det|} := by
  have hsuccess := triple_determinant_mass_of_strip_breadth (μ.restrict S) v hv hδ κ
    (by simpa only [Measure.restrict_apply_univ] using hstrip)
  rw [← Measure.restrict_pi_pi (fun _ : Fin 3 => μ) (fun _ : Fin 3 => S),
    Measure.restrict_apply' (MeasurableSet.univ_pi (fun _ => hS))] at hsuccess
  simp only [Measure.restrict_apply_univ] at hsuccess
  have hcoeff : (1 / 8 : ℝ≥0∞) ≤ 1 - 54 * κ := by
    calc
      _ ≤ 1 - 54 * (1 / 1000 : ℝ≥0∞) := by
        apply ENNReal.le_sub_of_add_le_right (by finiteness)
        have h : ENNReal.ofReal ((1 : ℝ) / 8 + 54 / 1000) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal (by norm_num)
        convert h using 1 <;>
          simp [ENNReal.ofReal_add, div_eq_mul_inv]
      _ ≤ _ := by simpa only [mul_comm] using tsub_le_tsub_left (mul_le_mul_left hκ 54) 1
  have heq : ENNReal.ofReal (((1 / 2 : ℝ) * μ.real S) ^ 3) =
      (1 / 8 : ℝ≥0∞) * (μ S) ^ 3 := by
    rw [ENNReal.ofReal_pow (mul_nonneg (by norm_num) measureReal_nonneg),
      ENNReal.ofReal_mul (by norm_num), measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ S), mul_pow]
    norm_num [ENNReal.ofReal_div_of_pos]
    rw [← ENNReal.inv_pow]
    norm_num
  rw [heq]
  refine (mul_le_mul' hcoeff le_rfl).trans (hsuccess.trans (measure_mono ?_))
  intro p hp
  refine ⟨fun i => hp.2 i (mem_univ _), ?_⟩
  exact unitLift_determinant_lower_bound (fun i => v (p i)) hK hδ.le
    (fun i => hbound _ (hp.2 i (mem_univ _))) hp.1

end

end Submission.Obl.k4_physical_parent_potential_candidates
