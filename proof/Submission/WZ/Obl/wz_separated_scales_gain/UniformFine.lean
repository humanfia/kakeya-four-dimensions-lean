-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.UniformFine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.FineCells
import Submission.WZ.Obl.wz_separated_scales_gain.Elementary

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

theorem uniform_fine_cells {σ u : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2)
    (hu : 0 ≤ u) (hE : EstimateE σ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ b δ lam θ L R : ℝ, 0 < δ → δ ≤ b → b ≤ 1 →
      0 < lam → 0 < θ → 1 ≤ L → 0 < R → R ≤ 1 →
      ∀ K : ℕ, 0 < K → 288 * θ ^ K * b ^ 2 ≤ lam * δ ^ 2 / 2 →
      (δ / b ≤ R → (fineRadius δ b) ^ η ≤ fineContraction * lam / (64 * K)) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (a w : Space),
      0 < n → ‖w‖ = 1 → (∀ i, ‖v i‖ = 1) →
      (∀ i, tube δ (x i) (v i) ⊆ unitBall) →
      (∀ i, tube δ (x i) (v i) ⊆ tube b a w) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) → RelativeCount b L δ x v →
      ∃ s : Finset (Fin 3 → ℤ),
        (∀ z ∈ s, (tube b a w ∩ gridCell b z).Nonempty) ∧
        ENNReal.ofReal (lam / (32 * K) * b ^ 2) ≤ volume (gridUnion b s) ∧
        ∀ z ∈ s, ENNReal.ofReal (A * lam * θ / K * R ^ 2 * (δ / b) ^ (u + ε) * L⁻¹ *
          ((n : ℝ) * (δ / b) ^ 4) ^ (σ / 2)) * volume (gridCell b z) ≤
            volume ((⋃ i, Y i) ∩ gridCell b z) := by
  obtain ⟨A, η, hA, hη, H⟩ := frostman_fine_cells hσ0 hE hε
  let A' := min A (1 / (576 * 3136000000))
  have hA' : 0 < A' := lt_min hA (by norm_num)
  refine ⟨A', η, hA', hη, ?_⟩
  intro b δ lam θ L R hδ hδb hb1 hlam hθ hL hR hR1 K hK hcut hden
    n x v Y a w hn hw hv hB hTP hover hYm hYT hind hrel
  have hb : 0 < b := hδ.trans_le hδb
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hr : 0 < δ / b := div_pos hδ hb
  have hr1 : δ / b ≤ 1 := (div_le_one hb).mpr hδb
  have hSsub : (⋃ i, Y i) ⊆ tube b a w := iUnion_subset fun i => (hYT i).trans (hTP i)
  by_cases hsmall : δ / b ≤ R
  · obtain ⟨e, he⟩ := tube_in_square_prism hb1 a w hw
    obtain ⟨s, _, _, hmass, hlocal⟩ := H b δ lam θ L hδ hδb hb1 hlam hθ hL K hK hcut
      (hden hsmall) e n x v Y hn hv hB (fun i => (hTP i).trans he) hover hYm hYT hind hrel
    have hdpos : 0 < A * lam * θ / K * (δ / b) ^ (u + ε) * L⁻¹ *
        ((n : ℝ) * (δ / b) ^ 4) ^ (σ / 2) := by
      have hL0 : 0 < L := zero_lt_one.trans_le hL
      have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      positivity
    refine ⟨s, fun z hz => cell_meets_parent hb hdpos hSsub z (hlocal z hz), hmass, ?_⟩
    intro z hz
    apply le_trans (b := ENNReal.ofReal (A * lam * θ / K * (δ / b) ^ (u + ε) * L⁻¹ *
      ((n : ℝ) * (δ / b) ^ 4) ^ (σ / 2)) * volume (gridCell b z)) _ (hlocal z hz)
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hR2 : R ^ 2 ≤ 1 := by nlinarith
    have hA'0 : 0 ≤ A' := hA'.le
    calc
      _ ≤ A * lam * θ / K * 1 * (δ / b) ^ (u + ε) * L⁻¹ *
          ((n : ℝ) * (δ / b) ^ 4) ^ (σ / 2) := by
        gcongr
        exact min_le_left _ _
      _ = _ := by ring
  · obtain ⟨s, hmeet, hmass, hlocal⟩ := elementary_cells hb hb1 hδ hlam hθ hK hcut hn x v Y a w
      hw hv hYm hYT (fun i => (hYT i).trans ((hB i).trans (ball_subset_ball (by norm_num))))
      (fun i => (hYT i).trans (hTP i)) hind
    have hNr := relative_packing_bound hb hb1 hδ x v a w hw hv hTP hover
    have hpower : ((n : ℝ) * (δ / b) ^ 4) ^ (σ / 2) ≤ 3136000000 :=
      normalized_power_le (by positivity) (by norm_num) hNr (by positivity) (by linarith)
    have hpow : (δ / b) ^ (u + ε) ≤ 1 := Real.rpow_le_one hr.le hr1 (by linarith)
    have hLi : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
    have hRr : R ^ 2 ≤ (δ / b) ^ 2 := pow_le_pow_left₀ hR.le (not_le.mp hsmall).le 2
    have hscalar : A' * R ^ 2 * (δ / b) ^ (u + ε) * L⁻¹ *
        ((n : ℝ) * (δ / b) ^ 4) ^ (σ / 2) ≤ (δ / b) ^ 2 / 576 := by
      calc
        _ ≤ (1 / (576 * 3136000000)) * (δ / b) ^ 2 * 1 * 1 * 3136000000 := by
          gcongr
          exact min_le_right _ _
        _ = _ := by ring
    refine ⟨s, hmeet, hmass, ?_⟩
    intro z hz
    apply le_trans (b := ENNReal.ofReal (lam * θ / (576 * K) * (δ / b) ^ 2) *
      volume (gridCell b z)) _ (hlocal z hz)
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hh := mul_le_mul_of_nonneg_left hscalar (by positivity : 0 ≤ lam * θ / K)
    convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_separated_scales_gain
