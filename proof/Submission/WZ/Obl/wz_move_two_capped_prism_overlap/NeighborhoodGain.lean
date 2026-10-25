-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.NeighborhoodGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Defs
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodPowers
import Submission.WZ.Obl.wz_multiscale_finite_tower.Elementary

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, NeighborhoodGain.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O A E)

/-- A retained family of fine incidences with dense neighborhoods at a fixed
power-separated radius gives the volume alternative. All auxiliary count and
small-scale side conditions are absorbed into one cutoff. -/
theorem gain_of_dense_neighborhoods {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ κ η ν d₀ : ℝ, 0 < κ ∧ 0 < η ∧ 0 < ν ∧ η ≤ ν ∧
      ν ≤ b * ω / 100 ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ B : ℝ, 0 < δ → δ ≤ d₀ → b ≤ B → B ≤ 1 →
      ∀ (n : ℕ) (x v : Fin n → V) (Y W : Fin n → Set V),
      A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i) →
      O (δ ^ ν) * ∑ i, volume (Y i) ≤ ∑ i, volume (W i) →
      (∀ i p, p ∈ W i → O (δ ^ (12 * ν) * (δ ^ (1 - B) / 2) ^ 3) ≤
        volume ((⋃ i, Y i) ∩ ball p (δ ^ (1 - B) / 2))) →
      O (κ * δ ^ (ω - b * ω / 2) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
        volume (⋃ i, Y i) := by
  let e : ℝ := b * ω / 100
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨κ, ηE, dE, hκ, hηE, hdE, hdE100, H⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.neighborhood_power_gain hσ hσ2 hω hE e he
  let ν : ℝ := min (ηE / 2) e
  have hν : 0 < ν := lt_min (half_pos hηE) he
  have hνηE : ν ≤ ηE / 2 := min_le_left _ _
  have hνe : ν ≤ e := min_le_right _ _
  have hbω : b * ω ≤ 1 := (mul_le_mul hb1 hω1 hω.le zero_le_one).trans_eq (one_mul _)
  have hν1 : ν ≤ 1 := by dsimp [e] at hνe; linarith
  let η : ℝ := ν / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hην : η ≤ ν := by dsimp [η]; linarith
  let gap : ℝ := min b (min ηE 1)
  have hgap : 0 < gap := lt_min hb (lt_min hηE zero_lt_one)
  obtain ⟨d, hd, Hd⟩ := WangZahlLot.Obl.wz_clustered_cover_volume_gain.uniform_small_power_comparison
    (C := 128) (by norm_num) hgap
  refine ⟨κ, η, ν, min (min d dE) (1 / 100), hκ, hη, hν, hην, hνe,
    lt_min (lt_min hd hdE) (by norm_num), min_le_right _ _, ?_⟩
  intro δ B hδ hδcut hbB hB1 n x v Y W hA hW hretain hdense
  have hδd : δ ≤ d := hδcut.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδE : δ ≤ dE := hδcut.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := (hδcut.trans (min_le_right _ _)).trans (by norm_num)
  have hgapb : gap ≤ b := min_le_left _ _
  have hgapη : gap ≤ ηE := (min_le_right _ _).trans (min_le_left _ _)
  have hgap1 : gap ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hpow := Hd δ hδ hδ1 hδd
  have hδsq : δ ^ (2 : ℕ) ≤ dE := by nlinarith
  have hr : δ ≤ δ ^ (1 - B) / 6 := by
    have hh := hpow 6 1 (1 - B) (by norm_num) (by linarith)
    rw [Real.rpow_one] at hh
    linarith
  have hsqR : δ ^ (2 : ℕ) ≤ (δ ^ (1 - B) / 6) / 8 := by
    have hh := hpow 48 2 (1 - B) (by norm_num) (by linarith)
    rw [Real.rpow_two] at hh
    linarith
  have hηEpow : 128 * (δ ^ (2 : ℕ)) ^ ηE ≤ δ ^ (2 * ν) := by
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.square_rpow hδ]
    exact hpow 128 (2 * ηE) (2 * ν) le_rfl (by linarith)
  have hbudget : 7 * (2 * ν) + 2 * e + η ≤ b * ω / 2 := by
    dsimp [η, e] at *
    linarith
  have hcard : (n : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) := by
    have hAn : WangZahlLot.Obl.wz_multiscale_finite_tower.FrameAdmissible δ δ η n x v Y := hA
    have hn := hAn.card_bound hδ
    have hcount : (n : ℝ) ≤ 16 * δ ^ (-η - 2) := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp
      calc
        _ ≤ 16 * δ ^ (-η) := hn
        _ = (16 * δ ^ (-η - 2)) * δ ^ (2 : ℕ) := by
          rw [← Real.rpow_two, mul_assoc, ← Real.rpow_add hδ]
          congr 2
          ring
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.square_rpow hδ]
    apply hcount.trans
    exact hpow 16 (-η - 2) (2 * (-100)) (by norm_num) (by dsimp [η]; linarith)
  have hmass : O (δ ^ (2 * ν) * n * δ ^ 2) ≤ ∑ i, volume (W i) := by
    have hpower : δ ^ (2 * ν) ≤ δ ^ ν * δ ^ η := by
      rw [← Real.rpow_add hδ]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    calc
      _ ≤ O (δ ^ ν * (δ ^ η * n * δ ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg δ)]
      _ = O (δ ^ ν) * O (δ ^ η * n * δ ^ 2) := ENNReal.ofReal_mul (by positivity)
      _ ≤ O (δ ^ ν) * ∑ i, volume (Y i) := mul_le_mul' le_rfl hA.2.2.2.1
      _ ≤ _ := hretain
  have hbudgetB : 7 * (2 * ν) + 2 * e + η ≤ B * ω / 2 :=
    hbudget.trans (by nlinarith)
  have hg := H δ η B (2 * ν) hδ hδ1 hη.le (hb.le.trans hbB) hB1 hδsq hr hsqR
    hηEpow hbudgetB n x v Y W hcard hA hW hmass
    (by simpa only [show 6 * (2 * ν) = 12 * ν by ring] using hdense)
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hg
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ (n : ℝ) * δ ^ 2)
  apply mul_le_mul_of_nonneg_left _ hκ.le
  exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
