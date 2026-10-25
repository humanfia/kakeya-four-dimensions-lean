-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.RescaledMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.AffineRescaling
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.ClassMass

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- Applying the cinematic estimate after horizontal rescaling gives a class mass estimate
at the relative scale `r/rho`. -/
theorem rescaled_planar_class_mass {f : ℝ → ℝ} (hf : Continuous f)
    {r ρ c η ε : ℝ} (hρ : 0 < ρ) {n : ℕ} (q₀ : Space) (q : Fin n → Space)
    (T : Fin n → Set (ℝ × ℝ))
    (hT : ∀ i, T i ⊆ graphStrip r f c (q₀ + ρ • q i))
    (hC : CinematicMomentAt (r / ρ) η ε f)
    (hnorm : ∀ i, ‖q i‖ ≤ 10)
    (hsep : ∀ i j, i ≠ j → r / ρ ≤ dist (q i) (q j))
    (hcount : ∀ (b : Space) (s : ℝ), r / ρ ≤ s → s ≤ 1 →
      (ncard {i | q i ∈ ball b s} : ℝ) ≤ (r / ρ) ^ (-η) * (s / (r / ρ))) :
    (∑ i, volume (T i)) ^ 3 ≤ ENNReal.ofReal ρ ^ 2 *
      volume (⋃ i, T i) * ENNReal.ofReal ((r / ρ) ^ (-ε)) ^ 2 := by
  let Φ := normalizeProjection hf.measurable c q₀ ρ hρ.ne'
  let U : Fin n → Set (ℝ × ℝ) := fun i => Φ '' T i
  have hUS (i : Fin n) : U i ⊆ graphStrip (r / ρ) f 0 (q i) :=
    (image_mono (hT i)).trans (normalizeProjection_graphStrip hf.measurable r c q₀ (q i) hρ)
  have hm := hC n q hnorm hsep hcount
  have hh := sum_outer_measure_cubed_le_moment (T := U) volume
    (fun i => measurableSet_graphStrip hf (r / ρ) 0 (q i)) hUS
  have hmass : (∑ i, volume (T i)) = ENNReal.ofReal ρ * ∑ i, volume (U i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => volume_normalizeProjection hf.measurable c q₀ hρ (T i))
  have hvol : volume (⋃ i, T i) = ENNReal.ofReal ρ * volume (⋃ i, U i) := by
    have hv := volume_normalizeProjection hf.measurable c q₀ hρ (⋃ i, T i)
    simpa only [image_iUnion] using hv
  calc
    _ = ENNReal.ofReal ρ ^ 3 * (∑ i, volume (U i)) ^ 3 := by rw [hmass, mul_pow]
    _ ≤ ENNReal.ofReal ρ ^ 3 * (volume (⋃ i, U i) * ENNReal.ofReal ((r / ρ) ^ (-ε)) ^ 2) :=
      mul_le_mul' le_rfl (hh.trans (mul_le_mul' le_rfl (pow_le_pow_left' hm 2)))
    _ = _ := by rw [hvol]; ring


/-- Coefficients centered and normalized to a unit parameter ball. -/
def normalizedParameters (ρ : ℝ) (q₀ q : Space) : Space := ρ⁻¹ • (q - q₀)

lemma parameters_eq_center_add {ρ : ℝ} (hρ : ρ ≠ 0) (q₀ q : Space) :
    q = q₀ + ρ • normalizedParameters ρ q₀ q := by
  simp [normalizedParameters, smul_smul, hρ]

lemma dist_normalizedParameters_center {ρ : ℝ} (hρ : 0 < ρ) (q₀ q b : Space) :
    dist (normalizedParameters ρ q₀ q) b = dist q (q₀ + ρ • b) / ρ := by
  rw [dist_eq_norm, dist_eq_norm]
  have he : normalizedParameters ρ q₀ q - b = ρ⁻¹ • (q - (q₀ + ρ • b)) := by
    simp [normalizedParameters, smul_sub, smul_add, smul_smul, hρ.ne', sub_sub]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
  ring

lemma dist_normalizedParameters {ρ : ℝ} (hρ : 0 < ρ) (q₀ q q' : Space) :
    dist (normalizedParameters ρ q₀ q) (normalizedParameters ρ q₀ q') = dist q q' / ρ := by
  rw [dist_normalizedParameters_center hρ, ← parameters_eq_center_add hρ.ne']

lemma normalizedParameters_mem_ball {ρ : ℝ} (hρ : 0 < ρ) (q₀ q b : Space) (s : ℝ) :
    normalizedParameters ρ q₀ q ∈ ball b s ↔ q ∈ ball (q₀ + ρ • b) (ρ * s) := by
  simp only [mem_ball, dist_normalizedParameters_center hρ, div_lt_iff₀ hρ, mul_comm s ρ]

/-- The relative-scale cinematic hypothesis controls any class with the corresponding
local Katz--Tao count, with no assumption on its common parameter center. -/
theorem rescaled_planar_class_mass_of_local_count {f : ℝ → ℝ} (hf : Continuous f)
    {r ρ c η ε : ℝ} (hr : 0 < r) (hρ : 0 < ρ) {n : ℕ}
    (q₀ : Space) (q : Fin n → Space) (T : Fin n → Set (ℝ × ℝ))
    (hT : ∀ i, T i ⊆ graphStrip r f c (q i))
    (hdiam : ∀ i, dist (q i) q₀ ≤ ρ)
    (hsep : ∀ i j, i ≠ j → r ≤ dist (q i) (q j))
    (hcount : ∀ (b : Space) (s : ℝ), r ≤ s → s ≤ ρ →
      (ncard {i | q i ∈ ball b s} : ℝ) ≤ (r / ρ) ^ (-η) * (s / r))
    (hC : CinematicMomentAt (r / ρ) η ε f) :
    (∑ i, volume (T i)) ^ 3 ≤ ENNReal.ofReal ρ ^ 2 *
      volume (⋃ i, T i) * ENNReal.ofReal ((r / ρ) ^ (-ε)) ^ 2 := by
  apply rescaled_planar_class_mass (c := c) (η := η) hf hρ q₀ (fun i => normalizedParameters ρ q₀ (q i)) T
  · intro i
    rw [← parameters_eq_center_add hρ.ne']
    exact hT i
  · exact hC
  · intro i
    have hh := dist_normalizedParameters_center hρ q₀ (q i) 0
    simp only [smul_zero, add_zero, dist_zero_right] at hh
    rw [hh]
    exact ((div_le_one hρ).mpr (hdiam i)).trans (by norm_num)
  · intro i j hij
    rw [dist_normalizedParameters hρ]
    exact div_le_div_of_nonneg_right (hsep i j hij) hρ.le
  · intro b s hrs hs1
    simp_rw [normalizedParameters_mem_ball hρ]
    have hh := hcount (q₀ + ρ • b) (ρ * s)
      (by have hh := (div_le_iff₀ hρ).mp hrs; nlinarith)
      (by nlinarith)
    convert hh using 1
    congr 1
    field_simp

/-- A local cinematic class of transverse tube shadings obeys the sharp rescaled cubic bound. -/
theorem rescaled_tube_class_mass {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    {δ h ρ c η ε : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h) (hρ : 0 < ρ)
    {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space) (q₀ : Space)
    (hv : ∀ i, ‖v i‖ = 1) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hY : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hclass : ∀ i, |slope (v i) 0 - c| ≤ h)
    (hdiam : ∀ i, dist (parameters (x i) (v i)) q₀ ≤ ρ)
    (hsep : ∀ i j, i ≠ j → 12 * δ + h ≤
      dist (parameters (x i) (v i)) (parameters (x j) (v j)))
    (hcount : ∀ (b : Space) (s : ℝ), 12 * δ + h ≤ s → s ≤ ρ →
      (ncard {i | parameters (x i) (v i) ∈ ball b s} : ℝ) ≤
        ((12 * δ + h) / ρ) ^ (-η) * (s / (12 * δ + h)))
    (hC : CinematicMomentAt ((12 * δ + h) / ρ) η ε f) :
    (∑ i, volume (Y i)) ^ 3 ≤ ENNReal.ofReal (6 * δ) ^ 3 * ENNReal.ofReal ρ ^ 2 *
      volume (projection f '' (⋃ i, Y i)) *
        ENNReal.ofReal (((12 * δ + h) / ρ) ^ (-ε)) ^ 2 := by
  have hT (i : Fin n) : projection f '' Y i ⊆
      graphStrip (12 * δ + h) f c (parameters (x i) (v i)) :=
    ((image_mono (hY i)).trans
      (projection_tube_subset_strip hf hderiv hf0 (hv i) (htrans i) (hball i))).trans
        (graphStrip_subset_of_abs_sub_le (hclass i))
  have ha := rescaled_planar_class_mass_of_local_count hf.continuous
    (by linarith : 0 < 12 * δ + h) hρ q₀ (fun i => parameters (x i) (v i))
    (fun i => projection f '' Y i) hT hdiam hsep hcount hC
  rw [← image_iUnion] at ha
  have hm : (∑ i, volume (Y i)) ≤
      ENNReal.ofReal (6 * δ) * ∑ i, volume (projection f '' Y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      volume_le_projection_volume hf.continuous.measurable hδ (hv i) (htrans i) (hY i)
  calc
    _ ≤ (ENNReal.ofReal (6 * δ) * ∑ i, volume (projection f '' Y i)) ^ 3 :=
      pow_le_pow_left' hm 3
    _ = ENNReal.ofReal (6 * δ) ^ 3 * (∑ i, volume (projection f '' Y i)) ^ 3 := mul_pow _ _ _
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul' (le_refl (ENNReal.ofReal (6 * δ) ^ 3)) ha

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
