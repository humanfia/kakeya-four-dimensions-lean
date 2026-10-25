import Submission.Obl.k4_subcritical_chart_projection.MeshCaps
import Submission.Obl.k4_horizontal_supercritical_three_projections.CellCaps

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_horizontal_supercritical_three_projections
open Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

/-- A corrected hidden bin in a scalar chart has the original joint-cap
ceiling, including the angular intercept-width gain. -/
theorem corrected_sliced_cell_cap {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (π : Measure ℝ)
    {χ D σ a w d H K β pa : ℝ} {P Q vbin : ℤ} {z : Fin 2 → ℤ} {j : ℤ}
    (g : Fin 6 → ℝ)
    (hχ : 0 < χ) (hD : 0 < D) (hD₁ : D ≤ 1) (hσ : 0 < σ)
    (ha : 0 < a) (hw : 0 < w) (hH : 1 ≤ H) (hK : 0 ≤ K)
    (hχσ : χ ≤ D * σ) (hχσ₂ : χ ≤ D * σ ^ 2)
    (hσβ : σ ≤ β) (hβ₁ : β ≤ 1)
    (hpa : |2 * ((P : ℝ) * D) - pa| ≤ 5 * H)
    (hsmall : 24 * H ^ 2 * χ / D ≤ a * w)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ p ∈ Icc ((P : ℝ) * D) (((P : ℝ) + 1) * D),
      ∀ q ∈ Icc ((Q : ℝ) * D) (((Q : ℝ) + 1) * D), |predictor g t p q| ≤ H)
    (hcap : DirectionCap μ b π K χ χ (a * w) d vbin)
    (E : Set (α × ℝ))
    (hE : ∀ p ∈ E, p.1 ∈ chartSet b H χ D χ P Q vbin ∧
      p.2 ∈ Icc (0 : ℝ) 1 ∧
      Submission.Obl.k4_subcritical_chart_projection.chartCell D σ P Q (b p.1) p.2 = z ∧
      ⌊chartSignal a g (b p.1) p.2 / w⌋ = j ∧
      |b p.1 0 - pa| ≤ D * β ∧ (∀ e, |b p.1 e| ≤ H)) :
    μ E ≤ ENNReal.ofReal (8 * 10 ^ 6 * H ^ 3 * K * σ ^ 2 * β * D ^ 2 * (a * w) ^ d) *
      π {x | ⌊x / χ⌋ = vbin} := by
  classical
  rcases E.eq_empty_or_nonempty with hE0 | ⟨p₀, hp₀⟩
  · rw [hE0, measure_empty]; exact bot_le
  obtain ⟨hc₀, ht₀, hz₀, -, -, -⟩ := hE p₀ hp₀
  have hH₀ : 0 ≤ H := by linarith
  have hβ : 0 ≤ β := hσ.le.trans hσβ
  have hσ₁ : σ ≤ 1 := hσβ.trans hβ₁
  have hχ₁ : χ ≤ 1 := by nlinarith [mul_le_mul hD₁ hσ₁ hσ.le zero_le_one]
  have hz₀' : Submission.Obl.k4_horizontal_supercritical_three_projections.chartCell
      D σ P Q (b p₀.1) p₀.2 = z := hz₀
  have hτ : (z 0 : ℝ) * σ ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨hlo, -, -, -⟩ := chartCell_corner hσ hz₀'
    have hz : (0 : ℤ) ≤ z 0 := by
      have heq : ⌊p₀.2 / σ⌋ = z 0 := by rw [← hz₀]; rfl
      rw [← heq]
      exact Int.floor_nonneg.mpr (div_nonneg ht₀.1 hσ.le)
    exact ⟨mul_nonneg (by exact_mod_cast hz) hσ.le, hlo.trans ht₀.2⟩
  have hv : |(vbin : ℝ) * χ| ≤ 5 * H := by
    have hh := (chartSet_bounds hD hχ hc₀).2.2.2.2.2.2.2.1
    linarith
  have hA : χ ≤ σ := by nlinarith
  have hB : χ ≤ D * β + χ := le_add_of_nonneg_left (by positivity)
  have hC : χ ≤ D * σ + σ * (D * β) + χ + χ := by
    have hh : 0 ≤ D * σ + σ * (D * β) := by positivity
    linarith
  have hbox (p : α × ℝ) (hp : p ∈ E) :
      |physicalBase (b p.1) p.2 0 - (z 0 : ℝ) * σ| ≤ σ ∧
      |physicalBase (b p.1) p.2 1 - (pa + p.2 * ((vbin : ℝ) * χ))| ≤ D * β + χ ∧
      |physicalBase (b p.1) p.2 2 -
          (((Q : ℝ) * D + D * ((z 1 : ℝ) * σ)) - p.2 * (2 * ((P : ℝ) * D) - pa)) -
          ((z 0 : ℝ) * σ) *
            (physicalBase (b p.1) p.2 1 - (pa + p.2 * ((vbin : ℝ) * χ)))| ≤
        D * σ + σ * (D * β) + χ + χ ∧ ⌊b p.1 3 / χ⌋ = vbin := by
    obtain ⟨hc, ht, hz, hj, hpa', hb⟩ := hE p hp
    obtain ⟨-, -, -, -, -, hvel, -, -, -, -, hhor⟩ := chartSet_bounds hD hχ hc
    have hz' : Submission.Obl.k4_horizontal_supercritical_three_projections.chartCell
        D σ P Q (b p.1) p.2 = z := hz
    obtain ⟨htlo, hthi, hRlo, hRhi⟩ := chartCell_corner hσ hz'
    have htime : |p.2 - (z 0 : ℝ) * σ| ≤ σ := by
      rw [abs_le]; constructor <;> linarith
    have hR : |scalarParameter p.2 ((b p.1 0 - P * D) / D)
        ((b p.1 1 - Q * D) / D) - (z 1 : ℝ) * σ| ≤ σ := by
      rw [abs_le]; constructor <;> linarith
    obtain ⟨hZ, hY⟩ := scalar_cell_physical_box (b p.1) hD ht hτ htime hpa' hvel hhor hR
    exact ⟨htime, hZ, hY, hc.2.2.2.2.2⟩
  have hdiam : ∀ p ∈ E, ∀ p' ∈ E,
      (fun i => ⌊physicalBase (b p.1) p.2 i / χ⌋) =
        (fun i => ⌊physicalBase (b p'.1) p'.2 i / χ⌋) →
      |(b p.1 2 + p.2 * b p.1 5) - (b p'.1 2 + p'.2 * b p'.1 5)| ≤ 2 * (a * w) := by
    intro p hp p' hp' hcell
    obtain ⟨hc, ht, hz, hj, -, hb⟩ := hE p hp
    obtain ⟨hc', ht', hz', hj', -, hb'⟩ := hE p' hp'
    have hsignal : |chartSignal a g (b p.1) p.2 - chartSignal a g (b p'.1) p'.2| ≤ w :=
      floor_diameter hw (hj.trans hj'.symm)
    have hpred := predictor_physical_cell_variation hχ hD hD₁ hH ht ht' hb hb'
      hc.2.2.1 hc'.2.2.1 (hc.2.2.2.2.2.trans hc'.2.2.2.2.2.symm)
      hc.2.2.2.1 hc.2.2.2.2.1 hc'.2.2.2.1 hc'.2.2.2.2.1 hnorm hcell
    have hid : (b p.1 2 + p.2 * b p.1 5) - (b p'.1 2 + p'.2 * b p'.1 5) =
        a * (chartSignal a g (b p.1) p.2 - chartSignal a g (b p'.1) p'.2) +
          (predictor g p.2 (b p.1 0) (b p.1 1) -
            predictor g p'.2 (b p'.1 0) (b p'.1 1)) := by
      unfold chartSignal
      field_simp
      ring
    rw [hid]
    calc
      _ ≤ |a * (chartSignal a g (b p.1) p.2 - chartSignal a g (b p'.1) p'.2)| +
          |predictor g p.2 (b p.1 0) (b p.1 1) - predictor g p'.2 (b p'.1 0) (b p'.1 1)| :=
        abs_add_le _ _
      _ ≤ a * w + a * w := by
        rw [abs_mul, abs_of_pos ha]
        exact add_le_add (mul_le_mul_of_nonneg_left hsignal ha.le) (hpred.trans hsmall)
      _ = _ := by ring
  have hm := rectangular_diameter_cap μ (fun p => physicalBase (b p.1) p.2)
    (fun p => b p.1 2 + p.2 * b p.1 5) (fun p => ⌊b p.1 3 / χ⌋ = vbin) E
    hχ (mul_pos ha hw) hA hB hC (by linarith : 1 ≤ 5 * H)
    (show 0 ≤ K * (a * w) ^ d by positivity)
    ((z 0 : ℝ) * σ) pa ((Q : ℝ) * D + D * ((z 1 : ℝ) * σ))
    ((vbin : ℝ) * χ) (2 * ((P : ℝ) * D) - pa) ((z 0 : ℝ) * σ)
    hpa hv (by rw [abs_of_nonneg hτ.1]; linarith [hτ.2]) hbox hdiam
    (π {x | ⌊x / χ⌋ = vbin}) (fun c j => by
      convert hcap c j using 1 <;> first | rfl | (congr 2; ring))
  apply hm.trans
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hvol := scalar_cell_box_volume hD.le hσ.le hσβ hβ₁ hχ.le hχσ hχ.le hχσ
  have hvol' : σ * (D * β + χ) * (D * σ + σ * (D * β) + χ + χ) ≤
      8 * D ^ 2 * σ ^ 2 * β := hvol
  have hprod : 0 ≤ (H ^ 3 * K * (a * w) ^ d) * (D ^ 2 * σ ^ 2 * β) := by positivity
  calc
    _ = (7371 * 125 * H ^ 3 * K * (a * w) ^ d) *
        (σ * (D * β + χ) * (D * σ + σ * (D * β) + χ + χ)) := by ring
    _ ≤ (7371 * 125 * H ^ 3 * K * (a * w) ^ d) * (8 * D ^ 2 * σ ^ 2 * β) :=
      mul_le_mul_of_nonneg_left hvol' (by positivity)
    _ ≤ _ := by nlinarith only [hprod]


/-- A whole corrected chart has the same original reference numerator,
up to a fixed power of its subpower norm bound. -/
theorem corrected_whole_chart_cap {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (π : Measure ℝ)
    {χ D a d H K : ℝ} {P Q vbin : ℤ} (g : Fin 6 → ℝ)
    (hχ : 0 < χ) (hD : 0 < D) (hD₁ : D ≤ 1) (ha : 0 < a)
    (hH : 2 ≤ H) (hK : 0 ≤ K) (hχD : χ ≤ D) (hd : d ≤ 1)
    (hsmall : 24 * H ^ 2 * χ / D ≤ a)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ p ∈ Icc ((P : ℝ) * D) (((P : ℝ) + 1) * D),
      ∀ q ∈ Icc ((Q : ℝ) * D) (((Q : ℝ) + 1) * D), |predictor g t p q| ≤ H)
    (hcap : DirectionCap μ b π K χ χ (a * H ^ 2) d vbin)
    (E : Set (α × ℝ))
    (hE : ∀ p ∈ E, p.1 ∈ chartSet b H χ D χ P Q vbin ∧
      p.2 ∈ Icc (0 : ℝ) 1 ∧ |chartSignal a g (b p.1) p.2| ≤ H ∧
      (∀ e, |b p.1 e| ≤ H)) :
    μ E ≤ ENNReal.ofReal (2 * 10 ^ 6 * H ^ 5 * K * D ^ 2 * a ^ d) *
      π {x | ⌊x / χ⌋ = vbin} := by
  classical
  rcases E.eq_empty_or_nonempty with hE0 | ⟨p₀, hp₀⟩
  · rw [hE0, measure_empty]; exact bot_le
  obtain ⟨hc₀, -, -, -⟩ := hE p₀ hp₀
  have hH₁ : 1 ≤ H := by linarith
  have hH₀ : 0 ≤ H := by linarith
  have hχ₁ : χ ≤ 1 := hχD.trans hD₁
  have hpc : |(P : ℝ) * D| ≤ 3 * H := by
    have hh := (chartSet_bounds hD hχ hc₀).2.2.2.2.2.2.1
    linarith
  have hv : |(vbin : ℝ) * χ| ≤ 3 * H := by
    have hh := (chartSet_bounds hD hχ hc₀).2.2.2.2.2.2.2.1
    linarith
  have hbox (p : α × ℝ) (hp : p ∈ E) :
      |physicalBase (b p.1) p.2 0 - 0| ≤ 1 ∧
      |physicalBase (b p.1) p.2 1 - ((P : ℝ) * D + p.2 * ((vbin : ℝ) * χ))| ≤ D + χ ∧
      |physicalBase (b p.1) p.2 2 - ((Q : ℝ) * D - p.2 * ((P : ℝ) * D)) -
        0 * (physicalBase (b p.1) p.2 1 - ((P : ℝ) * D + p.2 * ((vbin : ℝ) * χ)))| ≤
          2 * D + χ ∧ ⌊b p.1 3 / χ⌋ = vbin := by
    obtain ⟨hc, ht, hs, hb⟩ := hE p hp
    obtain ⟨-, -, -, -, hpD, hvel, -, -, -, -, hhor⟩ := chartSet_bounds hD hχ hc
    have hqD : |b p.1 1 - (Q : ℝ) * D| ≤ D := by
      obtain ⟨hlo, hhi⟩ := parameter_mem hD hc.2.2.2.2.1
      rw [abs_le]; constructor <;> linarith
    have ht₁ : |p.2| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
    refine ⟨by simpa [physicalBase] using ht₁, ?_, ?_, hc.2.2.2.2.2⟩
    · change |(b p.1 0 + p.2 * b p.1 3) - ((P : ℝ) * D + p.2 * ((vbin : ℝ) * χ))| ≤ _
      calc
        _ = |(b p.1 0 - (P : ℝ) * D) + p.2 * (b p.1 3 - (vbin : ℝ) * χ)| := by
          congr 1; ring
        _ ≤ |b p.1 0 - (P : ℝ) * D| + |p.2| * |b p.1 3 - (vbin : ℝ) * χ| := by
          simpa only [abs_mul] using abs_add_le (b p.1 0 - (P : ℝ) * D)
            (p.2 * (b p.1 3 - (vbin : ℝ) * χ))
        _ ≤ _ := by nlinarith [mul_le_mul ht₁ hvel (abs_nonneg _) zero_le_one]
    · simp only [zero_mul, sub_zero]
      change |(b p.1 1 + p.2 * b p.1 4) - ((Q : ℝ) * D - p.2 * ((P : ℝ) * D))| ≤ _
      calc
        _ = |(b p.1 1 - (Q : ℝ) * D) + p.2 *
            ((b p.1 4 + b p.1 0) - (b p.1 0 - (P : ℝ) * D))| := by congr 1; ring
        _ ≤ |b p.1 1 - (Q : ℝ) * D| + |p.2| *
            (|b p.1 4 + b p.1 0| + |b p.1 0 - (P : ℝ) * D|) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
        _ ≤ D + 1 * (χ + D) := add_le_add hqD
          (mul_le_mul ht₁ (add_le_add hhor hpD)
            (add_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one)
        _ = _ := by ring
  have hdiam : ∀ p ∈ E, ∀ p' ∈ E,
      (fun i => ⌊physicalBase (b p.1) p.2 i / χ⌋) =
        (fun i => ⌊physicalBase (b p'.1) p'.2 i / χ⌋) →
      |(b p.1 2 + p.2 * b p.1 5) - (b p'.1 2 + p'.2 * b p'.1 5)| ≤ 2 * (a * H ^ 2) := by
    intro p hp p' hp' hcell
    obtain ⟨hc, ht, hs, hb⟩ := hE p hp
    obtain ⟨hc', ht', hs', hb'⟩ := hE p' hp'
    have hpred := predictor_physical_cell_variation hχ hD hD₁ hH₁ ht ht' hb hb'
      hc.2.2.1 hc'.2.2.1 (hc.2.2.2.2.2.trans hc'.2.2.2.2.2.symm)
      hc.2.2.2.1 hc.2.2.2.2.1 hc'.2.2.2.1 hc'.2.2.2.2.1 hnorm hcell
    have hsignal : |chartSignal a g (b p.1) p.2 - chartSignal a g (b p'.1) p'.2| ≤ H + H :=
      (abs_sub _ _).trans (add_le_add hs hs')
    have hid : (b p.1 2 + p.2 * b p.1 5) - (b p'.1 2 + p'.2 * b p'.1 5) =
        a * (chartSignal a g (b p.1) p.2 - chartSignal a g (b p'.1) p'.2) +
          (predictor g p.2 (b p.1 0) (b p.1 1) -
            predictor g p'.2 (b p'.1 0) (b p'.1 1)) := by
      unfold chartSignal
      field_simp
      ring
    rw [hid]
    calc
      _ ≤ |a * (chartSignal a g (b p.1) p.2 - chartSignal a g (b p'.1) p'.2)| +
          |predictor g p.2 (b p.1 0) (b p.1 1) - predictor g p'.2 (b p'.1 0) (b p'.1 1)| :=
        abs_add_le _ _
      _ ≤ a * (H + H) + a := by
        rw [abs_mul, abs_of_pos ha]
        exact add_le_add (mul_le_mul_of_nonneg_left hsignal ha.le) (hpred.trans hsmall)
      _ ≤ _ := by nlinarith [mul_nonneg ha.le (sq_nonneg (H - 1))]
  have hm := rectangular_diameter_cap μ (fun p => physicalBase (b p.1) p.2)
    (fun p => b p.1 2 + p.2 * b p.1 5) (fun p => ⌊b p.1 3 / χ⌋ = vbin) E
    hχ (show 0 < a * H ^ 2 by positivity) hχ₁
    (show χ ≤ D + χ by linarith) (show χ ≤ 2 * D + χ by linarith)
    (show 1 ≤ 3 * H by linarith) (show 0 ≤ K * (a * H ^ 2) ^ d by positivity)
    0 ((P : ℝ) * D) ((Q : ℝ) * D) ((vbin : ℝ) * χ) ((P : ℝ) * D) 0
    hpc hv (by simp; linarith) hbox hdiam
    (π {x | ⌊x / χ⌋ = vbin}) (fun c j => by
      convert hcap c j using 1 <;> first | rfl | (congr 2; ring))
  have hpow : (a * H ^ 2) ^ d ≤ a ^ d * H ^ 2 := by
    rw [Real.mul_rpow ha.le (sq_nonneg H)]
    gcongr
    calc
      _ ≤ (H ^ 2) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith : 1 ≤ H ^ 2) hd
      _ = _ := Real.rpow_one _
  apply hm.trans
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hvol : (D + χ) * (2 * D + χ) ≤ 6 * D ^ 2 := by nlinarith
  have hfactor : 0 ≤ H ^ 3 * K * a ^ d := by positivity
  calc
    _ = (7371 * 27 * H ^ 3 * K) * ((D + χ) * (2 * D + χ)) * (a * H ^ 2) ^ d := by ring
    _ ≤ (7371 * 27 * H ^ 3 * K) * (6 * D ^ 2) * (a ^ d * H ^ 2) := by
      gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hfactor (sq_nonneg (D * H))]

end Submission.Obl.k4_subcritical_chart_projection
