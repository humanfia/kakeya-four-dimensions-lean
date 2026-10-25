-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.UniformOuter.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.OuterEstimate
import Submission.WZ.Obl.wz_separated_scales_gain.Elementary

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

theorem outer_packing_bound {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1) (hB : ∀ i, tube δ (x i) (v i) ⊆ ball (0 : Space) 5)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) :
    (n : ℝ) * δ ^ 4 ≤ 1000000000000 := by
  have hvol : volume (ball (0 : Space) 5) ≤ ENNReal.ofReal 1000 := by
    rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have := Real.pi_lt_four
    norm_num at *
    linarith
  have hp := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hδ x v
    measure_ball_lt_top.ne hv hB hover
  have hh : ENNReal.ofReal ((n : ℝ) * δ ^ 4) ≤ ENNReal.ofReal 1000000000000 := by
    apply hp.trans
    calc
      _ ≤ ENNReal.ofReal 1000000 * (ENNReal.ofReal 1000) ^ 2 := by gcongr
      _ = _ := by norm_num
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hh

/-- The elementary union bound makes the outer estimate uniform up to radius one. -/
theorem uniform_outer_estimate {σ u : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2)
    (hu : 0 ≤ u) (hE : EstimateE σ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ δ lam L R : ℝ, 0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ L →
      0 < R → R ≤ 1 →
      (δ ≤ R → (fineRadius δ 1) ^ η ≤ fineContraction * lam / 16) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      0 < n → (∀ i, ‖v i‖ = 1) →
      (∀ i, tube δ (x i) (v i) ⊆ ball (0 : Space) 5) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) → RelativeCount 1 L δ x v →
      ENNReal.ofReal (A * lam * R ^ 2 * δ ^ (u + ε) * L⁻¹ * ((n : ℝ) * δ ^ 4) ^ (σ / 2)) ≤
        volume (⋃ i, Y i) := by
  obtain ⟨A, η, hA, hη, H⟩ := outer_estimate hσ0 hE hε
  let A' := min A (1 / 1000000000000)
  have hA' : 0 < A' := lt_min hA (by norm_num)
  refine ⟨A', η, hA', hη, ?_⟩
  intro δ lam L R hδ hδ1 hlam hlam1 hL hR hR1 hden n x v Y hn hv hB hover hYm hYT hind hrel
  by_cases hsmall : δ ≤ R
  · apply (ENNReal.ofReal_le_ofReal ?_).trans
      (H δ lam L hδ hδ1 hlam.le hL (hden hsmall) n x v Y hn hv hB hover hYm hYT hind hrel)
    have hR2 : R ^ 2 ≤ 1 := by nlinarith
    calc
      _ ≤ A * 1 * 1 * δ ^ (u + ε) * L⁻¹ * ((n : ℝ) * δ ^ 4) ^ (σ / 2) := by
        gcongr
        exact min_le_left _ _
      _ = _ := by ring
  · have hN := outer_packing_bound hδ x v hv hB hover
    have hpower : ((n : ℝ) * δ ^ 4) ^ (σ / 2) ≤ 1000000000000 :=
      normalized_power_le (by positivity) (by norm_num) hN (by positivity) (by linarith)
    have hpow : δ ^ (u + ε) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by linarith)
    have hLi : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
    have hRδ : R ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hR.le (not_le.mp hsmall).le 2
    apply (ENNReal.ofReal_le_ofReal ?_).trans ((hind ⟨0, hn⟩).trans
      (measure_mono (subset_iUnion Y ⟨0, hn⟩)))
    calc
      _ ≤ (1 / 1000000000000) * lam * δ ^ 2 * 1 * 1 * 1000000000000 := by
        gcongr
        exact min_le_right _ _
      _ = _ := by ring

end WangZahlLot.Obl.wz_separated_scales_gain
