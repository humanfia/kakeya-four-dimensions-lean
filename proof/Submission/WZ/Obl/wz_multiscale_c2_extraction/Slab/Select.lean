-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Select.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Count

/-!
# Selections in one window

* `exists_kept_height`: a height `z*` such that the shadings meeting `z*` carry, in a set of
  heights `ZR` of measure at most `W`, at least `θ² / (48 δ² W)` times the sum of the squared
  masses (Cauchy–Schwarz then compares with the square of the total mass).
* `kept_aligned`: points of kept shadings at heights near `z*` have twisted coordinate near the
  global grain set at height `z*`.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

/-- The shadings that meet a given height. -/
noncomputable def keptAt {n : ℕ} (Y : Fin n → Set Space) (z : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ q ∈ Y i, q 2 = z)

lemma mem_keptAt {n : ℕ} {Y : Fin n → Set Space} {z : ℝ} {i : Fin n} :
    i ∈ keptAt Y z ↔ ∃ q ∈ Y i, q 2 = z := by
  classical
  unfold keptAt
  simp

section

variable {σ δ s θ K N : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
  {Eo : Set Space} {f : ℝ → ℝ} {P : Space → Space}

/-- The kept height selection (Cauchy–Schwarz averaging). -/
theorem exists_kept_height (hS : FineSetup σ δ s θ K N x v Y Eo f P) {ZR : Set ℝ}
    (hZR : MeasurableSet ZR) {W : ℝ} (hW : 0 < W) (hZW : volume ZR ≤ ENNReal.ofReal W)
    {z₁ : ℝ} (hz₁ : z₁ ∈ ZR) :
    ∃ z ∈ ZR, ENNReal.ofReal (θ ^ 2 / (48 * δ ^ 2 * W)) *
        ∑ i, volume (Y i ∩ (fun p : Space => p 2) ⁻¹' ZR) ^ 2 ≤
      ∑ i ∈ keptAt Y z, volume (Y i ∩ (fun p : Space => p 2) ⁻¹' ZR) := by
  classical
  have hδ := hS.δ_pos
  have hθ := hS.θ_pos
  set m : Fin n → ℝ≥0∞ := fun i => volume (Y i ∩ (fun p : Space => p 2) ⁻¹' ZR)
  set a : ℝ≥0∞ := ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2)
  have ha0 : a ≠ 0 := by
    simp only [a, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hmt : ∀ i, m i ≠ ∞ := fun i =>
    ne_of_lt ((measure_mono (inter_subset_left.trans ((hS.sub_Eo i).trans hS.Eo_ball))).trans_lt
      measure_ball_lt_top)
  set ind : Fin n → ℝ → ℝ≥0∞ := fun i z => if ∃ q ∈ Y i, q 2 = z then 1 else 0
  -- each mass is controlled by the measure of the heights where the shading lives
  have hm_le : ∀ i, m i ≤ (∫⁻ z in ZR, ind i z) * a := by
    intro i
    rw [← lintegral_mul_const' _ _ hat]
    calc m i = ∫⁻ z in ZR, sliceArea (Y i) z := volume_inter_height_eq (hS.meas i) hZR
      _ ≤ ∫⁻ z in ZR, ind i z * a := by
          apply lintegral_mono
          intro z
          by_cases h : ∃ q ∈ Y i, q 2 = z
          · simp only [ind, if_pos h, one_mul]
            obtain ⟨q, hq, -⟩ := h
            exact sliceArea_le_of_subset_tube hδ hθ hS.θ_le (hS.v_unit i) (hS.vert i ⟨q, hq⟩)
              (hS.sub_tube i) z
          · simp only [ind, if_neg h, zero_mul, nonpos_iff_eq_zero]
            apply sliceArea_eq_zero
            intro p hp hpz
            exact h ⟨p, hp, hpz⟩
  set G : ℝ → ℝ≥0∞ := fun z => ∑ i, ind i z * m i
  have hG : ∀ z, G z = ∑ i ∈ keptAt Y z, m i := by
    intro z
    simp only [G, ind, ite_mul, one_mul, zero_mul, keptAt, Finset.sum_filter]
  -- the integral of `G`
  have hint : (∑ i, m i ^ 2) * a⁻¹ ≤ ∫⁻ z in ZR, G z := by
    calc (∑ i, m i ^ 2) * a⁻¹ = ∑ i, m i * (m i * a⁻¹) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [sq, mul_assoc]
      _ ≤ ∑ i, m i * ∫⁻ z in ZR, ind i z := by
          apply Finset.sum_le_sum
          intro i _
          gcongr
          calc m i * a⁻¹ ≤ (∫⁻ z in ZR, ind i z) * a * a⁻¹ := by gcongr; exact hm_le i
            _ = ∫⁻ z in ZR, ind i z := by
                rw [mul_assoc, ENNReal.mul_inv_cancel ha0 hat, mul_one]
      _ = ∑ i, ∫⁻ z in ZR, ind i z * m i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [lintegral_mul_const' _ _ (hmt i), mul_comm]
      _ ≤ ∫⁻ z in ZR, G z := sum_lintegral_le_lintegral_sum Finset.univ _ _
  by_cases h0 : ∑ i, m i ^ 2 = 0
  · refine ⟨z₁, hz₁, ?_⟩
    rw [h0, mul_zero]; exact zero_le
  have hsumt : ∑ i, m i ^ 2 ≠ ∞ := by
    apply ne_of_lt
    apply ENNReal.sum_lt_top.mpr
    intro i _
    exact ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr (hmt i))
  set c : ℝ≥0∞ := ENNReal.ofReal (θ ^ 2 / (48 * δ ^ 2 * W)) * ∑ i, m i ^ 2
  set S := ∑ i, m i ^ 2 with hS_def
  have e1 : c * ENNReal.ofReal W = ENNReal.ofReal (θ ^ 2 / (48 * δ ^ 2)) * S := by
    have : c * ENNReal.ofReal W =
        (ENNReal.ofReal (θ ^ 2 / (48 * δ ^ 2 * W)) * ENNReal.ofReal W) * S := by
      simp only [c]; ring
    rw [this, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    field_simp
  have e2 : ENNReal.ofReal (1 / 2) * (S * a⁻¹) = ENNReal.ofReal (θ ^ 2 / (48 * δ ^ 2)) * S := by
    have ha' : a⁻¹ = ENNReal.ofReal (θ ^ 2 / (24 * δ ^ 2)) := by
      simp only [a]
      rw [← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]
    rw [ha']
    have : ENNReal.ofReal (1 / 2) * (S * ENNReal.ofReal (θ ^ 2 / (24 * δ ^ 2))) =
        (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (θ ^ 2 / (24 * δ ^ 2))) * S := by ring
    rw [this, ← ENNReal.ofReal_mul (by norm_num)]
    congr 2
    field_simp
    ring
  have hc : c * volume ZR < ∫⁻ z in ZR, G z := by
    refine lt_of_lt_of_le ?_ hint
    calc c * volume ZR ≤ c * ENNReal.ofReal W := by gcongr
      _ = ENNReal.ofReal (1 / 2) * (S * a⁻¹) := by rw [e1, e2]
      _ < 1 * (S * a⁻¹) := by
          apply ENNReal.mul_lt_mul_left
          · exact mul_ne_zero h0 (ENNReal.inv_ne_zero.mpr hat)
          · exact ENNReal.mul_ne_top hsumt (ENNReal.inv_ne_top.mpr ha0)
          · rw [ENNReal.ofReal_lt_one]; norm_num
      _ = S * a⁻¹ := one_mul _
  obtain ⟨z, hz, hlt⟩ := exists_gt_of_mul_lt hZR G hc
  exact ⟨z, hz, by rw [← hG z]; exact hlt.le⟩

/-- Kept points near the kept height are aligned with the global grains at that height. -/
theorem kept_aligned (hS : FineSetup σ δ s θ K N x v Y Eo f P) {z₀ zs : ℝ}
    (hz₀ : z₀ ∈ Icc (-1 : ℝ) 1) {i : Fin n} (hi : i ∈ keptAt Y zs) {p : Space} (hp : p ∈ Y i)
    {H : ℝ} (hpz : |p 2 - zs| ≤ H) (hzz : |z₀ - zs| ≤ H) :
    ∃ u ∈ Reg.ProjectedSlice f Eo zs,
      |p 0 + f z₀ * p 1 - u| ≤ 4 * ((H + 2 * δ) / θ + 2 * δ) + H := by
  obtain ⟨q, hq, hq2⟩ := mem_keptAt.mp hi
  have hqE := hS.sub_Eo i hq
  refine ⟨q 0 + f (q 2) * q 1, hq2 ▸ mem_projectedSlice hqE, ?_⟩
  have hvθ := hS.vert i ⟨p, hp⟩
  have hd := tube_pair_dist hS.θ_pos (hS.v_unit i) hvθ (hS.sub_tube i hp) (hS.sub_tube i hq)
  rw [hq2] at hd
  have hfz : |f z₀| ≤ 3 := hS.f_bound z₀ hz₀
  have hq1 : |q 1| ≤ 1 := (abs_coord_lt_one (hS.Eo_ball hqE) 1).le
  have h1 := twist_sub_le (p := p) (q := q) (G := f (q 2)) hfz hq1
  have hlip : |f z₀ - f (q 2)| ≤ |z₀ - q 2| := by
    have := hS.f_lip.dist_le_mul z₀ (q 2)
    simpa [Real.dist_eq] using this
  have hzq : |z₀ - q 2| ≤ H := by rw [hq2]; exact hzz
  have hd' : dist p q ≤ (H + 2 * δ) / θ + 2 * δ := by
    refine hd.trans ?_
    gcongr
    · exact hS.θ_pos.le
  calc |p 0 + f z₀ * p 1 - (q 0 + f (q 2) * q 1)| ≤ 4 * dist p q + |f z₀ - f (q 2)| := h1
    _ ≤ 4 * ((H + 2 * δ) / θ + 2 * δ) + H := by linarith

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
