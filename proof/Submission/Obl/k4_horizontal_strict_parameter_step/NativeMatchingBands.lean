/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at a5c0b1bcb6dacb66c2e29bec68dd8eae37c23e9d, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeMatchingBands.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeComparisonData
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeBandReturn
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeIntegratedBand
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeWholeColour

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_row_cell_regularization

noncomputable section

attribute [local instance] sum_measurableSingletonClass

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

def physical (i : c.Index) : Fin 6 → ℝ :=
  c.support.table.physicalPredictors c.group (cfg.j k s) c.frame c.hH c.L i

def band (i : c.Index) (r : ℝ) : Set (Fin c.support.table.count × (Fin 3 → ℝ)) :=
  {p | c.comparison.colour (c.comparison.source p.1) = c.comparison.colour i ∧
    |predictor (c.comparison.coefficients i)
        (c.comparison.coordinates p 0) (c.comparison.coordinates p 1) (c.comparison.coordinates p 2) -
      predictor (c.comparison.coefficients (c.comparison.source p.1))
        (c.comparison.coordinates p 0) (c.comparison.coordinates p 1) (c.comparison.coordinates p 2)| ≤ r}

theorem measurable_band (i : c.Index) (r : ℝ) : MeasurableSet (c.band i r) := by
  have hx : Measurable c.comparison.coordinates := ComparisonFrame.measurable_markedCoordinates _
  have he (e : Fin 3) : Measurable (fun p => c.comparison.coordinates p e) :=
    (measurable_pi_apply e).comp ((WithLp.measurable_ofLp 2 (Fin 3 → ℝ)).comp hx)
  have hquery : Measurable (fun p => predictor (c.comparison.coefficients i)
      (c.comparison.coordinates p 0) (c.comparison.coordinates p 1) (c.comparison.coordinates p 2)) := by
    exact (((measurable_const.add (measurable_const.mul (he 0))).add
      ((measurable_const.add (measurable_const.mul (he 0))).mul (he 1))).add
      ((measurable_const.add (measurable_const.mul (he 0))).mul (he 2)))
  have hsource := c.comparison.predictorPair.w_measurable
  have hlab : Measurable (fun p : Fin c.support.table.count × (Fin 3 → ℝ) =>
      c.comparison.colour (c.comparison.source p.1)) :=
    (measurable_of_countable (fun j => c.comparison.colour (c.comparison.source j))).comp measurable_fst
  exact (measurableSet_eq_fun hlab measurable_const).inter
    (measurableSet_le (hquery.sub hsource).abs measurable_const)

def originalBand (i : c.Index) (w : ℝ) : Set (α × ℝ) :=
  {p | p ∈ c.support.event ∧
    c.support.table.colour c.group (cfg.j k s)
      (c.support.table.source c.group (cfg.j k s) (c.support.table.mark p)) =
        c.support.table.colour c.group (cfg.j k s) i ∧
    |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
      predictor (c.physical i) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ w}

theorem measurable_originalBand (i : c.Index) (w : ℝ) : MeasurableSet (c.originalBand i w) := by
  have hb : Measurable (fun p : α × ℝ => cfg.b k p.1) :=
    c.measurable_b.comp measurable_fst
  have ht : Measurable (fun p : α × ℝ => p.2) := measurable_snd
  have hfit : Measurable (fun p : α × ℝ =>
      cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
        predictor (c.physical i) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)) := by
    unfold predictor
    fun_prop
  have hlab : Measurable (fun p : α × ℝ => c.support.table.colour c.group (cfg.j k s)
      (c.support.table.source c.group (cfg.j k s) (c.support.table.mark p))) :=
    (measurable_of_countable (fun j => c.support.table.colour c.group (cfg.j k s)
      (c.support.table.source c.group (cfg.j k s) j))).comp c.support.table.mark_measurable
  exact c.support.measurable.inter ((measurableSet_eq_fun hlab measurable_const).inter
    (measurableSet_le hfit.abs measurable_const))

/-- Matching bands at legal original scalar widths return to the original
joint cap with the full time-parameter area factor and original palette. -/
theorem small_band_cap (i : c.Index) {r w : ℝ}
    (hAw : c.A ≤ w) (hw1 : w ≤ 1) (hrw : r + 3 * c.A ≤ w) :
    c.comparison.law (c.band i r) ≤ ENNReal.ofReal
      (25200 * cfg.K k * w ^ cfg.d * binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀))
        ((c.support.table.colour c.group (cfg.j k s) i).1 0) * cfg.timeLength k s * c.D ^ 2) := by
  letI := c.finite_palette
  let B : Fin c.support.table.count → Set (Fin 3 → ℝ) := fun j => {z | (j, z) ∈ c.band i r}
  have hB (j : Fin c.support.table.count) : MeasurableSet (B j) :=
    (measurable_const.prodMk measurable_id) (c.measurable_band i r)
  have htransfer : c.comparison.law (c.band i r) ≤ σ (c.originalBand i w) := by
    apply c.comparison.event_bound (c.originalBand i w) (c.measurable_originalBand i w) B hB
    change ∀ᵐ p ∂σ, _
    filter_upwards [c.support.conull] with p hp z hz hzB
    have hχ : 0 < cfg.N k ^ (-cfg.e₀) := Real.rpow_pos_of_pos c.N_pos _
    have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
    have htpos : ∀ g j, 0 < (c.frame (g, j)).timeScale := by
      intro g j
      change 0 < 16 * cfg.timeLength k s
      positivity
    have hdpos : ∀ g j, 0 < (c.frame (g, j)).parameterScale := by
      intro g j
      change 0 < 16 * c.D
      exact mul_pos (by norm_num) c.D_pos
    have hc : c.support.table.colour c.group (cfg.j k s) i =
        c.support.table.colour c.group (cfg.j k s)
          (c.support.table.source c.group (cfg.j k s) (c.support.table.mark p)) := hzB.1.symm
    have hb := cfg.observed_band_return c.layer c.support.table c.frame (fun g j => rfl)
      htpos hdpos c.L c.slopes c.N_pos c.K_one c.M_nonneg c.D_pos c.D_one hχ
      (c.velocity_width.trans c.D_one) rfl (Real.rpow_pos_of_pos c.N_pos _) c.mesh_one
      c.source_fit c.round_jitter c.support.unit c.support.coefficients c.support.contact
      p hp i hc z hz hzB.2
    exact ⟨hp, hzB.1, hb.trans hrw⟩
  exact htransfer.trans (cfg.observed_integrated_band c.support c.layer c.dominated c.caps
    c.re_lower c.re_upper c.velocity_lower c.velocity_upper (c.width_lower.trans hAw) hw1
    c.frame (fun g j => rfl) c.L c.slopes c.N_pos c.K_one c.M_nonneg c.D_pos c.D_one
    (Real.rpow_pos_of_pos c.N_pos _) c.velocity_width rfl c.mesh_time c.mesh_parameter
    (c.round_cell.trans hAw) i)

/-- Wider matching bands are bounded by the complete original colour. -/
theorem whole_band_cap (i : c.Index) (r : ℝ) :
    c.comparison.law (c.band i r) ≤ ENNReal.ofReal
      (64800 * cfg.K k ^ 2 * binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀))
        ((c.support.table.colour c.group (cfg.j k s) i).1 0) * cfg.timeLength k s * c.D ^ 2) := by
  letI := c.finite_palette
  have heq : σ {p | c.comparison.colour (c.comparison.source (c.comparison.mark p)) =
      c.comparison.colour i} = σ {p | p ∈ c.support.event ∧
        c.comparison.colour (c.comparison.source (c.comparison.mark p)) = c.comparison.colour i} := by
    apply measure_congr
    filter_upwards [c.support.conull] with p hp
    simp only [hp, true_and]
  calc
    _ ≤ c.comparison.law {p | c.comparison.colour (c.comparison.source p.1) =
        c.comparison.colour i} := measure_mono (fun p hp => hp.1)
    _ = σ {p | c.comparison.colour (c.comparison.source (c.comparison.mark p)) =
        c.comparison.colour i} := c.comparison.original_mark_mass
          (fun j => c.comparison.colour (c.comparison.source j) = c.comparison.colour i)
    _ = _ := heq
    _ ≤ _ := cfg.observed_whole_colour_cap c.support c.layer c.dominated c.caps
      c.re_lower c.re_upper c.velocity_lower c.velocity_upper
      (c.width_lower.trans c.width_upper) c.N_pos c.K_one c.D_pos c.D_one
      (Real.rpow_pos_of_pos c.N_pos _) c.velocity_width rfl c.mesh_time c.mesh_parameter i

/-- All band widths satisfy the original-palette matching estimate. The two
width regimes use the legal original joint cap and the whole colour cap. -/
theorem band_cap (hd : 0 ≤ cfg.d) (hd1 : cfg.d ≤ 1) (i : c.Index)
    {V : ℝ} (hAV : 2 * c.A ≤ V) :
    c.comparison.law (c.band i (2 * V)) ≤
      ENNReal.ofReal (16 * cfg.K k * c.comparison.density (c.comparison.colour i) *
        (V / c.A) ^ cfg.d) := by
  have hA : 0 < c.A := (Real.rpow_pos_of_pos c.N_pos _).trans_le c.width_lower
  have hV : 0 < V := by linarith
  have hVp : 0 ≤ V ^ cfg.d := Real.rpow_nonneg hV.le _
  have hfour : (4 : ℝ) ^ cfg.d ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hd1
  have hpow : c.A ^ cfg.d * (V / c.A) ^ cfg.d = V ^ cfg.d := by
    rw [Real.div_rpow hV.le hA.le]
    exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos hA _).ne'
  have hLab : c.comparison.colour i = c.support.table.colour c.group (cfg.j k s) i := rfl
  let W := cfg.timeLength k s * c.D ^ 2 * binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀))
    ((c.comparison.colour i).1 0)
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg hq.le (sq_nonneg _)) (binWeight_nonneg _ _ _)
  have hρ : 16 * cfg.K k * c.comparison.density (c.comparison.colour i) * (V / c.A) ^ cfg.d =
      (458752 * cfg.K k ^ 2 * V ^ cfg.d) * W := by
    rw [c.comparison_density]
    calc
      _ = 458752 * cfg.K k ^ 2 * (c.A ^ cfg.d * (V / c.A) ^ cfg.d) * W := by dsimp [W]; simp only [hLab]; ring
      _ = _ := by rw [hpow]
  by_cases hw1 : 4 * V ≤ 1
  · apply (c.small_band_cap i (r := 2 * V) (w := 4 * V)
      (by linarith) hw1 (by linarith)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [hρ]
    have hcoef : 25200 * cfg.K k * (4 * V) ^ cfg.d ≤
        458752 * cfg.K k ^ 2 * V ^ cfg.d := by
      calc
        _ = 25200 * cfg.K k * ((4 : ℝ) ^ cfg.d * V ^ cfg.d) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hV.le]
        _ ≤ 25200 * cfg.K k * (4 * V ^ cfg.d) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfour hVp) (by have := c.K_one; positivity)
        _ = 100800 * cfg.K k * V ^ cfg.d := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by have := c.K_one; nlinarith) hVp
    calc
      _ = (25200 * cfg.K k * (4 * V) ^ cfg.d) * W := by dsimp [W]; simp only [hLab]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hW
  · apply (c.whole_band_cap i (2 * V)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [hρ]
    have hlarge : 1 ≤ (4 * V) ^ cfg.d := Real.one_le_rpow (by linarith) hd
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hV.le] at hlarge
    have hpower : 1 ≤ 4 * V ^ cfg.d :=
      hlarge.trans (mul_le_mul_of_nonneg_right hfour hVp)
    have hcoef : 64800 * cfg.K k ^ 2 ≤ 458752 * cfg.K k ^ 2 * V ^ cfg.d := by
      have hh : (64800 : ℝ) ≤ 458752 * V ^ cfg.d := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (cfg.K k))]
    calc
      _ = (64800 * cfg.K k ^ 2) * W := by dsimp [W]; simp only [hLab]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hW

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
