-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.DensityEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.Types
import Submission.WZ.Obl.wz_tube_packing_bound
import Submission.WZ.Obl.wz_weighted_affine_packet_balancing.Refinement

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal

theorem profile_le_card {σ u ε A δ m l N : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hu : 0 ≤ u) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 1 ≤ m) (hl : 1 ≤ l) (hN : 1 ≤ N) :
    profile σ u ε A δ m l N ≤ A * N := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hl0 : 0 < l := lt_of_lt_of_le zero_lt_one hl
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  rw [profile_eq hδ hm0 hl0 hN0]
  have hd := Real.rpow_le_one hδ.le hδ1 (by linarith : 0 ≤ u + ε + 2 - σ)
  have hmc := Real.rpow_le_one_of_one_le_of_nonpos hm (by linarith : -1 + 3 / 2 * σ ≤ 0)
  have hlc := Real.rpow_le_one_of_one_le_of_nonpos hl (neg_nonpos.mpr hσ)
  have hnc := Real.rpow_le_self_of_one_le hN (by linarith : 1 - σ ≤ 1)
  calc
    _ ≤ A * 1 * 1 * 1 * N := by gcongr
    _ = _ := by ring

/-- The scale-dependent density hypothesis in `E` can be replaced by a polynomial
loss in an arbitrary positive shading density. -/
theorem tube_estimate_with_density {σ u : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hu : 0 ≤ u) (hE : TubeEstimate σ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ A P : ℝ, 0 < A ∧ 0 < P ∧
    ∀ δ lam m l : ℝ, 0 < δ → δ ≤ 1 / 100 → 0 < lam → lam ≤ 1 → 1 ≤ m → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1) →
    (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
    (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) →
    ConvexCount δ m n x v → SlabCount δ l n x v →
    ENNReal.ofReal (profile σ u ε (A * lam ^ P) δ m l n) ≤ volume (⋃ i, Y i) := by
  obtain ⟨A₀, hA₀, η, hη, H⟩ := hE ε hε
  obtain ⟨C, hC, hpacking⟩ := WangZahlLot.wz_tube_packing_bound
  let A := min A₀ C⁻¹
  let P := 1 + 6 / η
  have hA : 0 < A := lt_min hA₀ (inv_pos.mpr hC)
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨A, P, hA, hP, ?_⟩
  intro δ lam m l hδ hδsmall hlam hlam1 hm hl n x v Y hn hv hB hsep hYm hYU hdense hconv hslab
  have hδ1 : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hlamP : 0 ≤ lam ^ P := Real.rpow_nonneg hlam.le _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hscale : δ ^ η ≤ lam
  · have hcoef : A * lam ^ P ≤ A₀ := by
      calc
        A * lam ^ P ≤ A * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one hlam.le hlam1 hP.le) hA.le
        _ = A := mul_one _
        _ ≤ A₀ := min_le_left _ _
    have hinput : Admissible δ η m l n x v Y :=
      ⟨hn, fun i => ⟨hv i, hB i, hYm i, hYU i⟩, hsep,
        WangZahlLot.Obl.wz_weighted_affine_packet_balancing.density_sum
          (Real.rpow_nonneg hδ.le η) hscale Y hdense, hconv, hslab⟩
    apply le_trans (ENNReal.ofReal_le_ofReal _) (H δ hδ hδsmall m l hm hl n x v Y hinput)
    unfold profile
    gcongr
  · have hlampow : lam ^ P ≤ lam * δ ^ (6 : ℕ) := by
      rw [show P = 1 + 6 / η from rfl, Real.rpow_add hlam, Real.rpow_one]
      apply mul_le_mul_of_nonneg_left _ hlam.le
      calc
        lam ^ (6 / η) ≤ (δ ^ η) ^ (6 / η) :=
          Real.rpow_le_rpow hlam.le (le_of_not_ge hscale) (by positivity)
        _ = δ ^ (6 : ℕ) := by
          rw [← Real.rpow_mul hδ.le]
          have he : η * (6 / η) = 6 := by field_simp
          rw [he, Real.rpow_ofNat]
    have hpack : (n : ℝ) * δ ^ (4 : ℕ) ≤ C := hpacking δ hδ hδsmall n x v hv hB hsep
    have hAC : A * C ≤ 1 := by
      calc
        A * C ≤ C⁻¹ * C := mul_le_mul_of_nonneg_right (min_le_right _ _) hC.le
        _ = _ := inv_mul_cancel₀ hC.ne'
    have hbound : profile σ u ε (A * lam ^ P) δ m l n ≤ lam * δ ^ 2 := by
      calc
        _ ≤ (A * lam ^ P) * n := profile_le_card hσ hσhalf hu hε.le
          (mul_nonneg hA.le hlamP) hδ hδ1 hm hl hn1
        _ ≤ (A * (lam * δ ^ (6 : ℕ))) * n := by gcongr
        _ = (lam * δ ^ 2) * (A * ((n : ℝ) * δ ^ (4 : ℕ))) := by ring
        _ ≤ (lam * δ ^ 2) * (A * C) := by gcongr
        _ ≤ (lam * δ ^ 2) * 1 := by gcongr
        _ = _ := mul_one _
    exact (ENNReal.ofReal_le_ofReal hbound).trans
      ((hdense ⟨0, hn⟩).trans (measure_mono (subset_iUnion Y ⟨0, hn⟩)))

end WangZahlLot.Obl.wz_flat_factored_improvement
