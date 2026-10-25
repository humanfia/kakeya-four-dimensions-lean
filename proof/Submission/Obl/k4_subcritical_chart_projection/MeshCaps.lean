import Submission.Obl.k4_subcritical_chart_projection.Model
import Submission.Obl.k4_horizontal_supercritical_three_projections.ChartDefs
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.RectangularGrid
import Submission.Obl.k4_scalar_capped_heavy_potential.InterceptLists

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory
open scoped ENNReal BigOperators
open Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

/-- A short signal menu may depend on its original base cell. All additional
conditions and the original palette weight remain in the cell cap. -/
theorem finite_diameter_cap {Ω Q : Type*} [MeasurableSpace Ω] [DecidableEq Q]
    (μ : Measure Ω) (E : Set Ω) (code : Ω → Q) (value : Ω → ℝ)
    (condition : Ω → Prop) (F : Finset Q) {a : ℝ} (ha : 0 < a)
    (hcover : ∀ p ∈ E, code p ∈ F ∧ condition p)
    (hdiam : ∀ p ∈ E, ∀ p' ∈ E, code p = code p' →
      |value p - value p'| ≤ 2 * a)
    (L : ℝ≥0∞)
    (hcap : ∀ q j, μ {p | code p = q ∧ ⌊value p / a⌋ = j ∧ condition p} ≤ L) :
    μ E ≤ (F.card : ℝ≥0∞) * 9 * L := by
  classical
  obtain ⟨J, hJ, hmem⟩ :=
    Submission.Obl.k4_scalar_capped_heavy_potential.intercept_bin_lists_of_diameter
      E code value ha (by norm_num : (0 : ℝ) ≤ 2) hdiam
  have hJ' (q : Q) : (J q).card ≤ 9 := by
    exact_mod_cast hJ q
  have hsub : E ⊆ ⋃ q ∈ F, ⋃ j ∈ J q,
      {p | code p = q ∧ ⌊value p / a⌋ = j ∧ condition p} := by
    intro p hp
    exact mem_biUnion (hcover p hp).1
      (mem_biUnion (hmem p hp) ⟨rfl, rfl, (hcover p hp).2⟩)
  calc
    _ ≤ μ (⋃ q ∈ F, ⋃ j ∈ J q,
        {p | code p = q ∧ ⌊value p / a⌋ = j ∧ condition p}) := measure_mono hsub
    _ ≤ ∑ q ∈ F, μ (⋃ j ∈ J q,
        {p | code p = q ∧ ⌊value p / a⌋ = j ∧ condition p}) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ F, ∑ j ∈ J q,
        μ {p | code p = q ∧ ⌊value p / a⌋ = j ∧ condition p} :=
      Finset.sum_le_sum (fun q _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ q ∈ F, (9 : ℝ≥0∞) * L := by
      apply Finset.sum_le_sum
      intro q _
      calc
        _ ≤ ∑ _j ∈ J q, L := Finset.sum_le_sum (fun j _ => hcap q j)
        _ = ((J q).card : ℝ≥0∞) * L := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul' (by exact_mod_cast hJ' q) le_rfl
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- Integrate the original joint caps over a sheared box, using only the
pairwise hidden-signal diameter in each original base cell. -/
theorem rectangular_diameter_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 3 → ℝ) (value : Ω → ℝ)
    (condition : Ω → Prop) (E : Set Ω)
    {δ a A B C H V : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hA : δ ≤ A) (hB : δ ≤ B) (hC : δ ≤ C) (hH : 1 ≤ H) (hV : 0 ≤ V)
    (t₀ p r v w τ : ℝ) (hw : |w| ≤ H) (hv : |v| ≤ H) (hτ : |τ| ≤ H)
    (hE : ∀ z ∈ E, |point z 0 - t₀| ≤ A ∧
      |point z 1 - (p + point z 0 * v)| ≤ B ∧
      |point z 2 - (r - point z 0 * w) - τ * (point z 1 - (p + point z 0 * v))| ≤ C ∧
      condition z)
    (hdiam : ∀ z ∈ E, ∀ z' ∈ E,
      (fun i => ⌊point z i / δ⌋) = (fun i => ⌊point z' i / δ⌋) →
      |value z - value z'| ≤ 2 * a)
    (weight : ℝ≥0∞)
    (hcap : ∀ c j, μ {z | (fun i => ⌊point z i / δ⌋) = c ∧
      ⌊value z / a⌋ = j ∧ condition z} ≤ ENNReal.ofReal (V * δ ^ 3) * weight) :
    μ E ≤ ENNReal.ofReal (7371 * H ^ 3 * A * B * C * V) * weight := by
  let Q := rectangularGrid δ A B C t₀ p r v w τ
  have hcover (z : Ω) (hz : z ∈ E) :
      (fun i => ⌊point z i / δ⌋) ∈ Q ∧ condition z := by
    obtain ⟨ht, hZ, hY, hc⟩ := hE z hz
    refine ⟨?_, hc⟩
    have heq : (fun i => ⌊point z i / δ⌋) =
        ![⌊point z 0 / δ⌋, ⌊point z 1 / δ⌋, ⌊point z 2 / δ⌋] := by
      ext i
      fin_cases i <;> rfl
    rw [heq]
    exact mem_rectangularGrid hδ ht hZ hY
  have hm := finite_diameter_cap μ E (fun z i => ⌊point z i / δ⌋) value condition Q
    ha hcover hdiam (ENNReal.ofReal (V * δ ^ 3) * weight) hcap
  have hcard := card_rectangularGrid_volume hδ hA hB hC hH t₀ p r v w τ hw hv hτ
  change (Q.card : ℝ) ≤ _ at hcard
  have hreal : (Q.card : ℝ) * 9 * (V * δ ^ 3) ≤
      7371 * H ^ 3 * A * B * C * V := by
    calc
      _ = (Q.card : ℝ) * (9 * (V * δ ^ 3)) := by ring
      _ ≤ (819 * H ^ 3 * A * B * C / δ ^ 3) * (9 * (V * δ ^ 3)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by field_simp; ring
  have heq : (Q.card : ℝ≥0∞) * 9 * ENNReal.ofReal (V * δ ^ 3) =
      ENNReal.ofReal ((Q.card : ℝ) * 9 * (V * δ ^ 3)) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (Q.card : ℝ) * 9),
      ENNReal.ofReal_mul (Nat.cast_nonneg Q.card)]
    norm_num
  calc
    _ ≤ (Q.card : ℝ≥0∞) * 9 * (ENNReal.ofReal (V * δ ^ 3) * weight) := hm
    _ = ENNReal.ofReal ((Q.card : ℝ) * 9 * (V * δ ^ 3)) * weight := by
      rw [← heq]
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl

/-- Diameter of an ordinary floor cell, in its physical units. -/
theorem floor_diameter {a x y : ℝ} (ha : 0 < a) (h : ⌊x / a⌋ = ⌊y / a⌋) :
    |x - y| ≤ a := by
  have ht := (Int.abs_sub_lt_one_of_floor_eq_floor h).le
  rw [← sub_div, abs_div, abs_of_pos ha] at ht
  simpa only [one_mul] using (div_le_iff₀ ha).mp ht

/-- Time and parameter slopes are controlled by the norm on the full chart
square. The raw predictor coefficients do not enter this estimate. -/
theorem predictor_pair_variation {g : Fin 6 → ℝ} {pc qc D H t t' p q p' q' δ E : ℝ}
    (hD : 0 < D) (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
    (hp : p ∈ Icc pc (pc + D)) (hq : q ∈ Icc qc (qc + D))
    (hp' : p' ∈ Icc pc (pc + D)) (hq' : q' ∈ Icc qc (qc + D))
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc pc (pc + D),
      ∀ q ∈ Icc qc (qc + D), |predictor g t p q| ≤ H)
    (hδ : |t - t'| ≤ δ) (hE : |p - p'| + |q - q'| ≤ E) :
    |predictor g t p q - predictor g t' p' q'| ≤ 2 * H * δ + (2 * H / D) * E := by
  have hH : 0 ≤ H := (abs_nonneg _).trans (hnorm t ht p hp q hq)
  have hδ₀ : 0 ≤ δ := (abs_nonneg _).trans hδ
  have hpc : pc ∈ Icc pc (pc + D) := ⟨le_rfl, by linarith⟩
  have hqc : qc ∈ Icc qc (qc + D) := ⟨le_rfl, by linarith⟩
  obtain ⟨h2, h4⟩ := Submission.Lib.K4FullTimeLayers.affine_square_slopes hD
    (hnorm t ht pc hpc qc hqc)
    (hnorm t ht (pc + D) ⟨by linarith, le_rfl⟩ qc hqc)
    (hnorm t ht pc hpc (qc + D) ⟨by linarith, le_rfl⟩)
  have htime : |g 1 + g 3 * p' + g 5 * q'| ≤ 2 * H := by
    have h0 := hnorm 0 (by norm_num) p' hp' q' hq'
    have h1 := hnorm 1 (by norm_num) p' hp' q' hq'
    calc
      _ = |predictor g 1 p' q' - predictor g 0 p' q'| := by
        unfold predictor Submission.Lib.K4FullTimeLayers.parameterPredictor
        congr 1
        ring
      _ ≤ |predictor g 1 p' q'| + |predictor g 0 p' q'| := abs_sub _ _
      _ ≤ _ := by linarith
  have hid : predictor g t p q - predictor g t' p' q' =
      (g 2 + g 3 * t) * (p - p') + (g 4 + g 5 * t) * (q - q') +
        (t - t') * (g 1 + g 3 * p' + g 5 * q') := by
    unfold predictor Submission.Lib.K4FullTimeLayers.parameterPredictor
    ring
  rw [hid]
  calc
    _ ≤ |(g 2 + g 3 * t) * (p - p')| + |(g 4 + g 5 * t) * (q - q')| +
        |(t - t') * (g 1 + g 3 * p' + g 5 * q')| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (2 * H / D) * |p - p'| + (2 * H / D) * |q - q'| + δ * (2 * H) := by
      simp only [abs_mul]
      gcongr
    _ = 2 * H * δ + (2 * H / D) * (|p - p'| + |q - q'|) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hE (show 0 ≤ 2 * H / D by positivity))


def physicalBase (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4]

/-- One physical mesh cell and one velocity bin control the two static
intercepts. This is where the horizontal defect is used. -/
theorem parameter_cell_variation {b b' : Fin 6 → ℝ} {t t' χ H : ℝ}
    (hχ : 0 < χ) (hH : 1 ≤ H)
    (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
    (hb : ∀ e, |b e| ≤ H) (hb' : ∀ e, |b' e| ≤ H)
    (hhor : |b 4 + b 0| ≤ χ) (hhor' : |b' 4 + b' 0| ≤ χ)
    (hv : ⌊b 3 / χ⌋ = ⌊b' 3 / χ⌋)
    (hcell : (fun i => ⌊physicalBase b t i / χ⌋) =
      (fun i => ⌊physicalBase b' t' i / χ⌋)) :
    |t - t'| ≤ χ ∧ |b 0 - b' 0| + |b 1 - b' 1| ≤ 10 * H * χ := by
  have htcell : |t - t'| ≤ χ :=
    floor_diameter hχ (congrArg (fun c => c 0) hcell)
  have hZ : |(b 0 + t * b 3) - (b' 0 + t' * b' 3)| ≤ χ :=
    floor_diameter hχ (congrArg (fun c => c 1) hcell)
  have hY : |(b 1 + t * b 4) - (b' 1 + t' * b' 4)| ≤ χ :=
    floor_diameter hχ (congrArg (fun c => c 2) hcell)
  have hv' : |b 3 - b' 3| ≤ χ := floor_diameter hχ hv
  have ht'abs : |t'| ≤ 1 := by simpa only [abs_of_nonneg ht'.1] using ht'.2
  have hp : |b 0 - b' 0| ≤ (H + 2) * χ := by
    calc
      _ = |((b 0 + t * b 3) - (b' 0 + t' * b' 3)) -
          (t - t') * b 3 - t' * (b 3 - b' 3)| := by congr 1; ring
      _ ≤ |(b 0 + t * b 3) - (b' 0 + t' * b' 3)| +
          |(t - t') * b 3| + |t' * (b 3 - b' 3)| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ χ + χ * H + 1 * χ := by
        simp only [abs_mul]
        gcongr
        exact hb 3
      _ = _ := by ring
  have h4 : |b 4 - b' 4| ≤ (H + 4) * χ := by
    calc
      _ = |(b 4 + b 0) - (b' 4 + b' 0) - (b 0 - b' 0)| := by congr 1; ring
      _ ≤ |b 4 + b 0| + |b' 4 + b' 0| + |b 0 - b' 0| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ χ + χ + (H + 2) * χ := add_le_add (add_le_add hhor hhor') hp
      _ = _ := by ring
  have hq : |b 1 - b' 1| ≤ (2 * H + 5) * χ := by
    calc
      _ = |((b 1 + t * b 4) - (b' 1 + t' * b' 4)) -
          (t - t') * b 4 - t' * (b 4 - b' 4)| := by congr 1; ring
      _ ≤ |(b 1 + t * b 4) - (b' 1 + t' * b' 4)| +
          |(t - t') * b 4| + |t' * (b 4 - b' 4)| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ χ + χ * H + 1 * ((H + 4) * χ) := by
        simp only [abs_mul]
        gcongr
        exact hb 4
      _ = _ := by ring
  refine ⟨htcell, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hH) hχ.le]

/-- Static intercepts stay in the closed square on which the predictor
norm was supplied. -/
theorem parameter_mem {p D : ℝ} {P : ℤ} (hD : 0 < D) (hP : ⌊p / D⌋ = P) :
    p ∈ Icc ((P : ℝ) * D) ((P : ℝ) * D + D) := by
  obtain ⟨hlo, hhi⟩ :=
    Submission.Obl.k4_horizontal_supercritical_three_projections.floor_cell_mem (x := p) hD
  rw [hP] at hlo hhi
  exact ⟨hlo, by linarith⟩

/-- The chart's full-square norm resolves its predictor on the fine
physical mesh, uniformly in the number of charts. -/
theorem predictor_physical_cell_variation {b b' g : Fin 6 → ℝ}
    {P Q : ℤ} {t t' χ D H : ℝ}
    (hχ : 0 < χ) (hD : 0 < D) (hD₁ : D ≤ 1) (hH : 1 ≤ H)
    (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
    (hb : ∀ e, |b e| ≤ H) (hb' : ∀ e, |b' e| ≤ H)
    (hhor : |b 4 + b 0| ≤ χ) (hhor' : |b' 4 + b' 0| ≤ χ)
    (hv : ⌊b 3 / χ⌋ = ⌊b' 3 / χ⌋)
    (hp : ⌊b 0 / D⌋ = P) (hq : ⌊b 1 / D⌋ = Q)
    (hp' : ⌊b' 0 / D⌋ = P) (hq' : ⌊b' 1 / D⌋ = Q)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ p ∈ Icc ((P : ℝ) * D) (((P : ℝ) + 1) * D),
      ∀ q ∈ Icc ((Q : ℝ) * D) (((Q : ℝ) + 1) * D), |predictor g t p q| ≤ H)
    (hcell : (fun i => ⌊physicalBase b t i / χ⌋) =
      (fun i => ⌊physicalBase b' t' i / χ⌋)) :
    |predictor g t (b 0) (b 1) - predictor g t' (b' 0) (b' 1)| ≤ 24 * H ^ 2 * χ / D := by
  obtain ⟨htcell, hparam⟩ := parameter_cell_variation hχ hH ht ht' hb hb' hhor hhor' hv hcell
  have hn : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ p ∈ Icc ((P : ℝ) * D) ((P : ℝ) * D + D),
      ∀ q ∈ Icc ((Q : ℝ) * D) ((Q : ℝ) * D + D), |predictor g t p q| ≤ H := by
    convert hnorm using 2 <;> ring
  have hv := predictor_pair_variation hD ht ht'
    (parameter_mem hD hp) (parameter_mem hD hq)
    (parameter_mem hD hp') (parameter_mem hD hq') hn htcell hparam
  apply hv.trans
  apply (le_div_iff₀ hD).mpr
  have hH₀ : 0 ≤ H := by linarith
  have hmul := mul_le_mul_of_nonneg_left hD₁ (show 0 ≤ 2 * H * χ by positivity)
  have hHsq : H ≤ H ^ 2 := by nlinarith
  have hmore := mul_le_mul_of_nonneg_right hHsq (show 0 ≤ 2 * χ by positivity)
  field_simp at *
  nlinarith only [hmul, hmore, mul_nonneg (sq_nonneg H) hχ.le]

end Submission.Obl.k4_subcritical_chart_projection
