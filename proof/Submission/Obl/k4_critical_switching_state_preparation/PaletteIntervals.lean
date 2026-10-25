import Submission.Obl.k4_critical_switching_state_preparation.NativePaletteCaps
import Submission.Obl.k4_critical_switching_state_preparation.ShiftedPalette
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

/-- Eight original mesh bins cover a radius-three interval. -/
theorem palette_interval_le_of_mesh (π : Measure ℝ) {r K S : ℝ} (hr : 0 < r)
    (hcap : ∀ j : ℤ, π {w | ⌊w / r⌋ = j} ≤ ENNReal.ofReal (K * r ^ S)) (z : ℝ) :
    π (Icc (z - 3 * r) (z + 3 * r)) ≤ ENNReal.ofReal (8 * K * r ^ S) := by
  obtain ⟨J, hJ, hcover⟩ := scalar_interval_bin_cover z r 3 hr (by norm_num)
  have hsub : Icc (z - 3 * r) (z + 3 * r) ⊆ ⋃ j ∈ J, {w | ⌊w / r⌋ = j} := by
    intro w hw
    exact mem_iUnion₂.mpr ⟨⌊w / r⌋, hcover w (abs_le.mpr
      ⟨by linarith [hw.1], by linarith [hw.2]⟩), rfl⟩
  have hJ' : (J.card : ℝ≥0∞) ≤ ENNReal.ofReal 8 := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc
    _ ≤ π (⋃ j ∈ J, {w | ⌊w / r⌋ = j}) := measure_mono hsub
    _ ≤ ∑ j ∈ J, π {w | ⌊w / r⌋ = j} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ J, ENNReal.ofReal (K * r ^ S) := Finset.sum_le_sum (fun j _ => hcap j)
    _ = (J.card : ℝ≥0∞) * ENNReal.ofReal (K * r ^ S) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal (K * r ^ S) := mul_le_mul' hJ' le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

/-- Exact shifted velocity bins inherit interval bounds at every larger scale. -/
theorem shiftedPalette_interval_le_of_mesh (π : Measure ℝ) {h r K S : ℝ}
    (hh : 0 < h) (hhr : h ≤ r)
    (hcap : ∀ j : ℤ, π {w | ⌊w / r⌋ = j} ≤ ENNReal.ofReal (K * r ^ S))
    (c z : ℝ) :
    shiftedPalette π h c (Icc (z - r) (z + r)) ≤ ENNReal.ofReal (8 * K * r ^ S) := by
  calc
    _ ≤ π (Icc (z + c - (r + 2 * h)) (z + c + (r + 2 * h))) :=
      shiftedPalette_interval_le π hh c z r
    _ ≤ π (Icc (z + c - 3 * r) (z + c + 3 * r)) :=
      measure_mono (Icc_subset_Icc (by linarith) (by linarith))
    _ ≤ _ := palette_interval_le_of_mesh π (hh.trans_le hhr) hcap (z + c)

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The uniform native scale caps control a single real mesh of any fixed depth
in a compact positive range, before translating its velocity. -/
theorem Valid.eventually_palette_grid_range (h : cfg.Valid) {b a : ℝ}
    (hb : 0 < b) (hba : b ≤ a) :
    ∀ᶠ k in atTop, ∀ v : ℝ, b ≤ v → v ≤ a → ∀ j : ℤ,
      cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = j} ≤
        ENNReal.ofReal (cfg.K k * cfg.N k ^ (-cfg.S * v)) := by
  let R := 2 + a + b⁻¹
  have hR : 1 < R := by
    have ha0 : 0 < a := hb.trans_le hba
    have hb0 : 0 < b⁻¹ := inv_pos.mpr hb
    dsimp [R]
    linarith
  have hRb : R⁻¹ ≤ b := (inv_le_comm₀ (by linarith) hb).mpr (by dsimp [R]; linarith)
  have ha0 : 0 < a := hb.trans_le hba
  filter_upwards [h.caps R hR] with k hk v hbv hva j
  exact (hk 1 0 v (by exact (inv_le_one₀ (by linarith)).mpr (by linarith))
    (by linarith) (by norm_num) (by linarith) (hRb.trans hbv)
    (by dsimp [R] at *; have hb0 := inv_nonneg.mpr hb.le; linarith)).1 j

/-- The palette in the prepared law has the frozen interval estimate at every
radius down to the switching mesh, uniformly over all real velocity shifts. -/
theorem Valid.eventually_shifted_palette_intervals (h : cfg.Valid) {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ c z r : ℝ, cfg.N k ^ (-a) ≤ r → r ≤ 1 →
      shiftedPalette (cfg.π k) (cfg.N k ^ (-a)) c (Icc (z - r) (z + r)) ≤
        ENNReal.ofReal (cfg.N k ^ δ * r ^ cfg.S) := by
  let b := min a (δ / (2 * cfg.S))
  have hb : 0 < b := lt_min ha (by positivity [h.palette_pos])
  have hba : b ≤ a := min_le_left _ _
  have hbS : b * cfg.S ≤ δ / 2 := by
    have hb' : b ≤ δ / (2 * cfg.S) := min_le_right _ _
    have hh := (le_div_iff₀ (by positivity [h.palette_pos])).mp hb'
    nlinarith
  have hcost := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [h.scale k] : ∀ k, 1 ≤ cfg.N k) h.scale_limit
    h.subpower.1 h.subpower.2 1 hδ (A := 8) (by norm_num)
  filter_upwards [h.eventually_palette_grid_range hb hba, hcost]
    with k hgrid hcost c z r hr hr1
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 < cfg.N k := by linarith [h.scale k]
  have hω : 0 < cfg.N k ^ (-a) := Real.rpow_pos_of_pos hN _
  have hr0 : 0 < r := hω.trans_le hr
  have hK : 8 * cfg.K k ≤ cfg.N k ^ δ := by simpa using hcost.le
  by_cases hsmall : r ≤ cfg.N k ^ (-b)
  · let v := -Real.logb (cfg.N k) r
    have hvr : cfg.N k ^ (-v) = r := by
      dsimp [v]
      rw [neg_neg, Real.rpow_logb hN hN1.ne' hr0]
    have hbv : b ≤ v := by
      have hh := (Real.rpow_le_rpow_left_iff hN1).mp (hvr.trans_le hsmall)
      linarith
    have hva : v ≤ a := by
      have hh := (Real.rpow_le_rpow_left_iff hN1).mp (hr.trans_eq hvr.symm)
      linarith
    have hscale : cfg.N k ^ (-cfg.S * v) = r ^ cfg.S := by
      rw [← hvr, ← Real.rpow_mul hN.le]
      congr 1
      ring
    have hgridr : ∀ j : ℤ, cfg.π k {w | ⌊w / r⌋ = j} ≤
        ENNReal.ofReal (cfg.K k * r ^ cfg.S) := by
      intro j
      simpa only [hvr, hscale] using hgrid v hbv hva j
    exact (shiftedPalette_interval_le_of_mesh (cfg.π k) hω hr hgridr c z).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK
        (Real.rpow_nonneg hr0.le _)))
  · letI : IsProbabilityMeasure (cfg.π k) := (h.basic k).2.2.1
    letI := shiftedPalette_probability (cfg.π k) (cfg.N k ^ (-a)) c
    have hrlower : cfg.N k ^ (-b) ≤ r := (lt_of_not_ge hsmall).le
    have hone : 1 ≤ cfg.N k ^ δ * r ^ cfg.S := by
      calc
        1 ≤ cfg.N k ^ (δ + -b * cfg.S) := Real.one_le_rpow hN1.le (by linarith)
        _ = cfg.N k ^ δ * (cfg.N k ^ (-b)) ^ cfg.S := by
          rw [Real.rpow_add hN, Real.rpow_mul hN.le]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hrlower
          h.palette_pos.le) (Real.rpow_nonneg hN.le _)
    exact (measure_mono (subset_univ _)).trans (by simpa using ENNReal.ofReal_le_ofReal hone)

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
