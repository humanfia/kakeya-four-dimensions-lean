-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.FineCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.Counts
import Submission.WZ.Obl.wz_separated_scales_gain.Weight
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineCells

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- `E` on a relatively Frostman family gives the square-root cardinality normalization
in each selected cell at the parent scale. -/
theorem frostman_fine_cells {σ u : ℝ} (hσ : 0 ≤ σ) (hE : EstimateE σ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ b δ lam θ L : ℝ, 0 < δ → δ ≤ b → b ≤ 1 →
      0 < lam → 0 < θ → 1 ≤ L →
      ∀ K : ℕ, 0 < K → 288 * θ ^ K * b ^ 2 ≤ lam * δ ^ 2 / 2 →
      (fineRadius δ b) ^ η ≤ fineContraction * lam / (64 * K) →
      ∀ (e : AffineIsometryEquiv ℝ Space Space) (n : ℕ) (x v : Fin n → Space)
        (Y : Fin n → Set Space),
      0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ unitBall) →
      (∀ i, tube δ (x i) (v i) ⊆ e '' standardPrism b b) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) → RelativeCount b L δ x v →
      ∃ s : Finset (Fin 3 → ℤ), s ⊆ gridKeys b ∧
        (∀ z ∈ s, (e '' standardPrism b b ∩ gridCell b z).Nonempty) ∧
        ENNReal.ofReal (lam / (32 * K) * b ^ 2) ≤ volume (gridUnion b s) ∧
        ∀ z ∈ s,
          ENNReal.ofReal (A * lam * θ / K * (δ / b) ^ (u + ε) * L⁻¹ *
            ((n : ℝ) * (δ / b) ^ 4) ^ (σ / 2)) * volume (gridCell b z) ≤
              volume ((⋃ i, Y i) ∩ gridCell b z) := by
  obtain ⟨A, η, hA, hη, H⟩ := fine_cell_estimate hE hε
  refine ⟨A / 56, η, by positivity, hη, ?_⟩
  intro b δ lam θ L hδ hδb hb1 hlam hθ hL K hK hcut hden e n x v Y
    hn hv hB hT hover hYm hYT hind hrel
  have hb : 0 < b := hδ.trans_le hδb
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  let m := 56 * L * n * (δ / b) ^ 2
  have hm : 1 ≤ m := relative_coefficient_lower hb hL0 hδ (hδb.trans hb1) hn hv hrel
  have hconv : ConvexCount δ m x v := by
    apply convexCount_mono _ (convexCount_of_relative hb hrel)
    dsimp [m]
    have hh : 0 ≤ L * n * (δ / b) ^ 2 := by positivity
    nlinarith only [hh]
  obtain ⟨s, hs, hmeet, hmass, hlocal⟩ := H b b δ lam θ m L
    hδ hδb le_rfl hb1 hlam hθ hm hL K hK hcut hden e n x v Y
    hn hv hB hT hover hYm hYT hind hconv (fun U hU => by simpa only [pow_two] using hrel U hU)
  refine ⟨s, hs, hmeet, hmass, ?_⟩
  intro z hz
  apply le_trans (b := ENNReal.ofReal (A * lam * θ / K * (δ / b) ^ (u + ε) * m⁻¹ *
    ((n : ℝ) * (δ / b) ^ 2) * (m ^ (-(3 / 2 : ℝ)) * L * ((n : ℝ) * δ / b)) ^ (-σ)) *
      volume (gridCell b z)) _ (hlocal z hz)
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hw := frostman_weight_lower (C := 56) (by norm_num) hL (Nat.cast_pos.mpr hn)
    (div_pos hδ hb) hσ
  have hp : 0 ≤ A * lam * θ / K * (δ / b) ^ (u + ε) := by positivity
  have hh := mul_le_mul_of_nonneg_left hw hp
  have hbr : (n : ℝ) * δ / b = (n : ℝ) * (δ / b) := by ring
  rw [hbr]
  dsimp [m]
  convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_separated_scales_gain
