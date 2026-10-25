-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.NeighborhoodPowers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodGain
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenBridge
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PowerBudgets

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory Metric
open scoped ENNReal

lemma neighborhood_power_identity {δ C σ ω ν e h b : ℝ}
    (hδ : 0 < δ) (hC : 0 < C) :
    C * δ ^ (6 * ν) * δ ^ ν * (δ ^ (2 : ℕ)) ^ e *
      (δ ^ (-h)) ^ (-1 + σ) * (8 * δ ^ (-h)) ^ (-σ) *
      ((δ ^ (1 - b) / 6) / δ) ^ (ω + σ) =
    (C * (8 : ℝ) ^ (-σ) * (6 : ℝ) ^ (-(ω + σ))) *
      δ ^ (7 * ν + 2 * e + h - b * (ω + σ)) := by
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_div, Real.log_pow]
  ring

/-- At radius δ^(1-b)/2 a density δ^(6ν) gives a fixed power gain,
provided the density losses are sufficiently smaller than bω. -/
theorem neighborhood_power_gain {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω) :
    ∀ e : ℝ, 0 < e → ∃ κ η d₀ : ℝ, 0 < κ ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
    ∀ δ h b ν : ℝ, 0 < δ → δ ≤ 1 → 0 ≤ h → 0 ≤ b → b ≤ 1 →
    δ ^ (2 : ℕ) ≤ d₀ → δ ≤ δ ^ (1 - b) / 6 →
    δ ^ (2 : ℕ) ≤ (δ ^ (1 - b) / 6) / 8 →
    128 * (δ ^ (2 : ℕ)) ^ η ≤ δ ^ ν →
    7 * ν + 2 * e + h ≤ b * ω / 2 →
    ∀ (n : ℕ) (x v : Fin n → V) (Y W : Fin n → Set V),
    (n : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) →
    A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
    (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i) →
    O (δ ^ ν * n * δ ^ 2) ≤ ∑ i, volume (W i) →
    (∀ i p, p ∈ W i → O (δ ^ (6 * ν) * (δ ^ (1 - b) / 2) ^ 3) ≤
      volume ((⋃ i, Y i) ∩ ball p (δ ^ (1 - b) / 2))) →
    O (κ * δ ^ (ω - b * ω / 2) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  intro e he
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ :=
    regular_density_neighborhood_gain hσ hσhalf hω (tubeEstimate_of_E hE) e he
  let κ := C * (8 : ℝ) ^ (-σ) * (6 : ℝ) ^ (-(ω + σ))
  refine ⟨κ, η, d₀, by dsimp [κ]; positivity, hη, hd₀, hd₀small, ?_⟩
  intro δ h b ν hδ hδ1 hh hb hb1 hδd hdr hDr hηq hbudget n x v Y W hnmax hA hW hmass hdensity
  have hm : 1 ≤ δ ^ (-h) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hr1 : δ ^ (1 - b) / 6 ≤ 1 := by
    have hh := Real.rpow_le_one hδ.le hδ1 (show 0 ≤ 1 - b by linarith)
    linarith
  have hball := fun i => (hA.2.1 i).2.1
  have hslab := tube_body_slab x v (Real.rpow_nonneg hδ.le (-h)) hball hA.2.2.2.2.2
  have hgain := H (δ ^ (2 : ℕ)) δ (δ ^ (1 - b) / 6) (by positivity) hδd hδ hdr hr1 hDr
    n x v W (δ ^ (-h)) (8 * δ ^ (-h)) (δ ^ ν) (δ ^ (6 * ν)) (⋃ i, Y i) hA.1 hnmax hm
    (by linarith) (Real.rpow_pos_of_pos hδ _) (Real.rpow_nonneg hδ.le _) hηq
    (fun i => (hA.2.1 i).1) hball (fun i => (hW i).1)
    (fun i => (hW i).2.trans (hA.2.1 i).2.2.2) hmass hA.2.2.2.2.1 hslab
    (MeasurableSet.iUnion fun i => (hA.2.1 i).2.2.1)
    (by simpa only [show 3 * (δ ^ (1 - b) / 6) = δ ^ (1 - b) / 2 by ring] using hdensity)
  have hscalar : C * δ ^ (6 * ν) * δ ^ ν * (δ ^ (2 : ℕ)) ^ e *
      (δ ^ (-h)) ^ (-1 + σ) * (8 * δ ^ (-h)) ^ (-σ) *
      (δ ^ ω * (n * δ ^ 2) * (n * δ) ^ (-σ) * ((δ ^ (1 - b) / 6) / δ) ^ (ω + σ)) =
      κ * δ ^ (ω + (7 * ν + 2 * e + h - b * (ω + σ))) * (n * δ ^ 2) * (n * δ) ^ (-σ) := by
    rw [Real.rpow_add hδ]
    have heq := neighborhood_power_identity (C := C) (σ := σ) (ω := ω) (ν := ν) (e := e)
      (h := h) (b := b) hδ hC
    calc
      _ = (C * δ ^ (6 * ν) * δ ^ ν * (δ ^ (2 : ℕ)) ^ e *
        (δ ^ (-h)) ^ (-1 + σ) * (8 * δ ^ (-h)) ^ (-σ) *
        ((δ ^ (1 - b) / 6) / δ) ^ (ω + σ)) * δ ^ ω *
        (n * δ ^ 2) * (n * δ) ^ (-σ) := by ring
      _ = _ := by rw [heq]; dsimp [κ]; ring
  rw [hscalar] at hgain
  apply le_trans _ hgain
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ (n : ℝ) * δ ^ 2)
  apply mul_le_mul_of_nonneg_left _ (by dsimp [κ]; positivity)
  apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
  nlinarith [mul_nonneg hb hσ]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
