-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.FirstMoment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_close_pair_moment.Measure

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_jet_close_pair_moment (strip measurableSet_strip)

/-- The vertical strip about any continuous graph has area `4 * δ`. -/
theorem volume_strip (δ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    volume (strip δ g) = ENNReal.ofReal (4 * δ) := by
  exact WangZahlLot.Obl.wz_jet_close_pair_moment.volume_strip hg

/-- Multiplicity in a specified finite subfamily. -/
def finiteMultiplicity {ι : Type*} (A : Finset ι) (δ : ℝ) (g : ι → ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ≥0∞ :=
  ∑ i ∈ A, (strip δ (g i)).indicator (fun _ => 1) p

theorem measurable_finiteMultiplicity {ι : Type*} (A : Finset ι) (δ : ℝ)
    {g : ι → ℝ → ℝ} (hg : ∀ i ∈ A, Continuous (g i)) :
    Measurable (finiteMultiplicity A δ g) := by
  exact Finset.measurable_sum A fun i hi =>
    measurable_const.indicator (measurableSet_strip (δ := δ) (hg i hi))

/-- The exact first moment retains the cardinality of the chosen subfamily. -/
theorem lintegral_finiteMultiplicity {ι : Type*} (A : Finset ι) (δ : ℝ)
    {g : ι → ℝ → ℝ} (hg : ∀ i ∈ A, Continuous (g i)) :
    (∫⁻ p, finiteMultiplicity A δ g p) = ENNReal.ofReal (4 * δ * A.card) := by
  unfold finiteMultiplicity
  rw [lintegral_finsetSum A (fun i hi =>
    measurable_const.indicator (measurableSet_strip (δ := δ) (hg i hi)))]
  have hterm (i : ι) (hi : i ∈ A) :
      (∫⁻ p, (strip δ (g i)).indicator (fun _ => (1 : ℝ≥0∞)) p) =
        ENNReal.ofReal (4 * δ) := by
    rw [lintegral_indicator (measurableSet_strip (δ := δ) (hg i hi))]
    simp [volume_strip δ (hg i hi)]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul' (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_comm]

/-- Markov's inequality for the multiplicity of continuous graph strips. -/
theorem volume_rich_le_firstMoment {ι : Type*} (A : Finset ι) {δ μ : ℝ}
    {g : ι → ℝ → ℝ} (hg : ∀ i ∈ A, Continuous (g i)) (hμ : 0 < μ) :
    volume {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p} ≤
      ENNReal.ofReal (4 * δ * A.card / μ) := by
  calc
    _ ≤ (∫⁻ p, finiteMultiplicity A δ g p) / ENNReal.ofReal μ :=
      meas_ge_le_lintegral_div (measurable_finiteMultiplicity A δ hg).aemeasurable
        (ne_of_gt (ENNReal.ofReal_pos.mpr hμ)) ENNReal.ofReal_ne_top
    _ = _ := by
      rw [lintegral_finiteMultiplicity A δ hg, ENNReal.ofReal_div_of_pos hμ]

/-- A square-root bound on the richness upgrades the first moment to the
`μ ^ (-3/2)` form. The set may impose additional restrictions. -/
theorem volume_subset_rich_le {ι : Type*} (A B : Finset ι) {δ μ F : ℝ}
    {g : ι → ℝ → ℝ} (hg : ∀ i ∈ A, Continuous (g i))
    (hδ : 0 ≤ δ) (hμ : 0 < μ) (hF : μ ^ (1 / 2 : ℝ) ≤ F)
    {E : Set (ℝ × ℝ)}
    (hE : E ⊆ {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p}) :
    volume E ≤ ENNReal.ofReal
      (4 * F * δ * ((A.card : ℝ) + (B.card : ℝ)) * μ ^ (-(3 / 2 : ℝ))) := by
  have hF0 : 0 ≤ F := (Real.rpow_nonneg hμ.le _).trans hF
  have hid : μ ^ (1 / 2 : ℝ) * μ ^ (-(3 / 2 : ℝ)) = μ⁻¹ := by
    rw [← Real.rpow_add hμ]
    norm_num [Real.rpow_neg_one]
  calc
    volume E ≤ volume {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p} :=
      measure_mono hE
    _ ≤ ENNReal.ofReal (4 * δ * A.card / μ) := volume_rich_le_firstMoment A hg hμ
    _ ≤ ENNReal.ofReal
        (4 * F * δ * ((A.card : ℝ) + (B.card : ℝ)) * μ ^ (-(3 / 2 : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        4 * δ * (A.card : ℝ) / μ =
            4 * δ * (A.card : ℝ) * (μ ^ (1 / 2 : ℝ) * μ ^ (-(3 / 2 : ℝ))) := by
          rw [hid, div_eq_mul_inv]
        _ ≤ 4 * δ * (A.card : ℝ) * (F * μ ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hF (Real.rpow_nonneg hμ.le _)) (by positivity)
        _ ≤ 4 * δ * ((A.card : ℝ) + (B.card : ℝ)) * (F * μ ^ (-(3 / 2 : ℝ))) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Nat.cast_nonneg B.card))
              (by positivity)) (by positivity)
        _ = _ := by ring

/-- For `τ ≥ 1/10`, the far-scale hypothesis already bounds the square root of
richness by five times the allowed power loss. -/
theorem sqrt_richness_le_of_large_exponent {δ μ D τ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hμ : 0 ≤ μ) (hD : D ≤ 20)
    (hscale : δ * μ * δ ^ (-8 * τ) ≤ D) (hτ : 1 / 10 ≤ τ) :
    μ ^ (1 / 2 : ℝ) ≤ 5 * δ ^ (-τ) := by
  have hinv : δ * δ ^ (-8 * τ) * δ ^ (8 * τ - 1) = 1 := by
    calc
      δ * δ ^ (-8 * τ) * δ ^ (8 * τ - 1) =
          δ ^ (1 : ℝ) * δ ^ (-8 * τ) * δ ^ (8 * τ - 1) := by rw [Real.rpow_one]
      _ = δ ^ (1 + -8 * τ + (8 * τ - 1)) := by
        rw [Real.rpow_add hδ, Real.rpow_add hδ]
      _ = 1 := by
        convert Real.rpow_zero δ using 1
        congr 1
        ring
  have hmu : μ ≤ 20 * δ ^ (8 * τ - 1) := by
    calc
      μ = (δ * μ * δ ^ (-8 * τ)) * δ ^ (8 * τ - 1) := by
        calc
          μ = μ * (δ * δ ^ (-8 * τ) * δ ^ (8 * τ - 1)) := by rw [hinv, mul_one]
          _ = _ := by ring
      _ ≤ 20 * δ ^ (8 * τ - 1) :=
        mul_le_mul_of_nonneg_right (hscale.trans hD) (Real.rpow_nonneg hδ.le _)
  have hexp : δ ^ (8 * τ - 1) ≤ δ ^ (-2 * τ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hpower : (δ ^ (-τ)) ^ 2 = δ ^ (-2 * τ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hδ.le]
    congr 1
    ring
  have hbound : μ ≤ 25 * (δ ^ (-τ)) ^ 2 := by
    calc
      μ ≤ 20 * δ ^ (8 * τ - 1) := hmu
      _ ≤ 20 * δ ^ (-2 * τ) := mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ 25 * δ ^ (-2 * τ) := by nlinarith [Real.rpow_nonneg hδ.le (-2 * τ)]
      _ = _ := by rw [hpower]
  rw [← Real.sqrt_eq_rpow]
  have hpos := Real.rpow_pos_of_pos hδ (-τ)
  nlinarith [Real.sqrt_nonneg μ, Real.sq_sqrt hμ]

/-- The full required area expression for the elementary parameter range.
Only one of the two richness conditions is needed in this range. -/
theorem area_bound_of_large_exponent {ι : Type*} (A B : Finset ι)
    {δ μ D τ K : ℝ} {g : ι → ℝ → ℝ}
    (hg : ∀ i ∈ A, Continuous (g i)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hμ : 0 < μ) (hD : D ≤ 20) (hK : 1 ≤ K)
    (hscale : δ * μ * δ ^ (-8 * τ) ≤ D) (hτ : 1 / 10 ≤ τ)
    {E : Set (ℝ × ℝ)}
    (hE : E ⊆ {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p}) :
    volume E ≤ ENNReal.ofReal
      (20 * δ ^ (-τ) * K ^ (1 : ℝ) * δ *
        ((A.card : ℝ) + (B.card : ℝ)) * μ ^ (-(3 / 2 : ℝ))) := by
  have hs := sqrt_richness_le_of_large_exponent hδ hδ1 hμ.le hD hscale hτ
  have hsK : μ ^ (1 / 2 : ℝ) ≤ 5 * δ ^ (-τ) * K := by
    exact hs.trans (le_mul_of_one_le_right (by positivity) hK)
  convert volume_subset_rich_le A B hg hδ.le hμ hsK hE using 1
  congr 1
  rw [Real.rpow_one]
  ring

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
