-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.LightClass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.RescaledMass
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.StripNeighborhood
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.GridDensity

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

lemma graphStrip_subset_parameter_near {f : ℝ → ℝ}
    (hf : ∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 3) {r ρ c : ℝ} {q q₀ : Space}
    (hqq : dist q q₀ ≤ ρ) : graphStrip r f c q ⊆ graphStrip (r + 7 * ρ) f c q₀ := by
  rintro p ⟨hpz, hpu⟩
  have hb (i : Fin 3) : |q i - q₀ i| ≤ ρ := (abs_coordinate_sub_le_dist q q₀ i).trans hqq
  have hρ : 0 ≤ ρ := dist_nonneg.trans hqq
  have hz : |p.2| ≤ 1 := abs_le.mpr hpz
  have hdiff : |(q 0 + c * p.2 + q 1 * f p.2 + q 2 * p.2 * f p.2) -
      (q₀ 0 + c * p.2 + q₀ 1 * f p.2 + q₀ 2 * p.2 * f p.2)| ≤ 7 * ρ := by
    calc
      _ = |(q 0 - q₀ 0) + (q 1 - q₀ 1) * f p.2 + (q 2 - q₀ 2) * p.2 * f p.2| := by
        congr 1
        ring
      _ ≤ |q 0 - q₀ 0| + |(q 1 - q₀ 1) * f p.2| + |(q 2 - q₀ 2) * p.2 * f p.2| :=
        abs_add_three _ _ _
      _ = |q 0 - q₀ 0| + |q 1 - q₀ 1| * |f p.2| + |q 2 - q₀ 2| * |p.2| * |f p.2| := by
        simp only [abs_mul]
      _ ≤ ρ + ρ * 3 + ρ * 1 * 3 := by gcongr <;> first | exact hb _ | exact hf _ hpz
      _ = _ := by ring
  refine ⟨hpz, ?_⟩
  calc
    _ ≤ |p.1 - (q 0 + c * p.2 + q 1 * f p.2 + q 2 * p.2 * f p.2)| +
        |(q 0 + c * p.2 + q 1 * f p.2 + q 2 * p.2 * f p.2) -
          (q₀ 0 + c * p.2 + q₀ 1 * f p.2 + q₀ 2 * p.2 * f p.2)| := abs_sub_le _ _ _
    _ ≤ r + 7 * ρ := add_le_add hpu hdiff

/-- The total mass over the light planar grid is small for each cinematic parameter class. -/
theorem light_tube_class_mass {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    {δ h ρ c η ε : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h)
    (hrρ : 12 * δ + h ≤ ρ) (hρ1 : ρ ≤ 1) (hc : |c| ≤ 3)
    {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space) (q₀ : Space) (hq₀ : ‖q₀‖ ≤ 6)
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
    (hC : CinematicMomentAt ((12 * δ + h) / ρ) η ε f)
    {X L : Set (ℝ × ℝ)} {θ : ℝ≥0∞}
    (hX : projection f '' (⋃ i, Y i) ⊆ X)
    (hlight : ∀ S : Set (ℝ × ℝ), volume (X ∩ L ∩ S) ≤ θ * volume (thickening ρ S)) :
    (∑ i, volume (Y i ∩ projection f ⁻¹' L)) ^ 3 ≤
      ENNReal.ofReal (6 * δ) ^ 3 * ENNReal.ofReal ρ ^ 2 *
        (θ * ENNReal.ofReal (432 * ρ)) *
          ENNReal.ofReal (((12 * δ + h) / ρ) ^ (-ε)) ^ 2 := by
  have hρ : 0 < ρ := (by linarith : 0 < 12 * δ + h).trans_le hrρ
  let Z : Fin n → Set Space := fun i => Y i ∩ projection f ⁻¹' L
  let S := graphStrip (12 * δ + h + 7 * ρ) f c q₀
  have hZ (i : Fin n) : Z i ⊆ Tube δ (x i) (v i) := inter_subset_left.trans (hY i)
  have hproj : projection f '' (⋃ i, Z i) ⊆ X ∩ L ∩ S := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, ⟨hpY, hpL⟩⟩ := mem_iUnion.mp hp
    refine ⟨⟨hX (mem_image_of_mem _ (mem_iUnion.mpr ⟨i, hpY⟩)), hpL⟩, ?_⟩
    apply graphStrip_subset_parameter_near (fun z hz => normalized_slope_bound hf hderiv hf0 hz) (hdiam i)
    apply graphStrip_subset_of_abs_sub_le (hclass i)
    exact projection_tube_subset_strip hf hderiv hf0 (hv i) (htrans i) (hball i)
      (mem_image_of_mem _ (hY i hpY))
  have hfm := hf.continuous.measurable
  have hb : |q₀ 1| ≤ 6 := (abs_coordinate_le_norm q₀ 1).trans hq₀
  have hd : |q₀ 2| ≤ 6 := (abs_coordinate_le_norm q₀ 2).trans hq₀
  have hL : |c| + 2 * |q₀ 1| + 5 * |q₀ 2| ≤ 45 := by linarith
  have hstrip : volume (thickening ρ S) ≤ ENNReal.ofReal (432 * ρ) := by
    have hs := volume_thickening_graph_strip
      (g := fun z => q₀ 0 + c * z + q₀ 1 * f z + q₀ 2 * z * f z) (by fun_prop)
      hρ hρ1 (by linarith : 0 ≤ 12 * δ + h + 7 * ρ)
      (by linarith : 12 * δ + h + 7 * ρ ≤ 8 * ρ)
      (by norm_num : (0 : ℝ) ≤ 45) (by norm_num : (0 : ℝ) ≤ 8)
      (fun z hz w hw => (graph_center_lipschitz hf hderiv hf0 c q₀ hz hw).trans
        (mul_le_mul_of_nonneg_right hL (abs_nonneg _)))
    norm_num at hs
    simpa only [S, graphStrip, mem_Icc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 432),
      ENNReal.ofReal_ofNat] using hs
  have ha : volume (projection f '' (⋃ i, Z i)) ≤ θ * ENNReal.ofReal (432 * ρ) :=
    (measure_mono hproj).trans ((hlight S).trans (mul_le_mul' le_rfl hstrip))
  exact (rescaled_tube_class_mass hf hderiv hf0 hδ hh hρ x v Z q₀ hv htrans hball hZ
    hclass hdiam hsep hcount hC).trans (mul_le_mul' (mul_le_mul' le_rfl ha) le_rfl)

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
