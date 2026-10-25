-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ScaleDensityGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ScaleDensityGain.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.LowDensity

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (regular_density_neighborhood_gain tubeEstimate_of_E tube_body_slab)

noncomputable section

/-- The neighborhood gain cancels the chosen ball scale against a density
threshold of exponent sigma plus omega. -/
theorem scale_density_power_identity {C δ R σ ω ν e h t : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hR : 0 < R) :
    C * (δ ^ (-t) * (δ / R) ^ (ω + σ)) * δ ^ ν * (δ ^ (2 : ℕ)) ^ e *
      (δ ^ (-h)) ^ (-1 + σ) * (8 * δ ^ (-h)) ^ (-σ) *
      δ ^ ω * ((R / 3) / δ) ^ (ω + σ) =
      (C * (8 : ℝ) ^ (-σ) * (3 : ℝ) ^ (-(ω + σ))) * δ ^ (ω - t + ν + 2 * e + h) := by
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow]
  norm_num
  ring

/-- A retained shading with an excessive density at any one radius gives
a power gain for the original family. -/
theorem single_scale_density_gain {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω) :
    ∀ e : ℝ, 0 < e → ∃ κ η d₀ : ℝ, 0 < κ ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ h ν t R : ℝ, 0 < δ → δ ≤ 1 → 0 ≤ h → 0 < R → R ≤ 1 →
      δ ^ (2 : ℕ) ≤ d₀ → δ ≤ R / 3 → δ ^ (2 : ℕ) ≤ (R / 3) / 8 →
      128 * (δ ^ (2 : ℕ)) ^ η ≤ δ ^ ν → ν + 2 * e + h ≤ t / 2 →
      ∀ (n : ℕ) (x v : Fin n → V) (Y W : Fin n → Set V),
      (n : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) →
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i) →
      O (δ ^ ν * n * δ ^ 2) ≤ ∑ i, μ (W i) →
      (∀ i p, p ∈ W i → O (δ ^ (-t) * (δ / R) ^ (ω + σ) * R ^ 3) ≤
        μ ((⋃ i, Y i) ∩ ball p R)) → Gain σ ω κ (t / 2) δ n Y := by
  intro e he
  obtain ⟨C, η, d₀, hC, hη, hd₀, hsmall, H⟩ :=
    regular_density_neighborhood_gain hσ hσhalf hω (tubeEstimate_of_E hE) e he
  let κ := C * (8 : ℝ) ^ (-σ) * (3 : ℝ) ^ (-(ω + σ))
  refine ⟨κ, η, d₀, by dsimp [κ]; positivity, hη, hd₀, hsmall, ?_⟩
  intro δ h ν t R hδ hδ1 hh hR hR1 hδd hδR hDR hq hbudget n x v Y W hnmax hA hW hmass hdensity
  have hm : 1 ≤ δ ^ (-h) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hball := fun i => (hA.2.1 i).2.1
  have hslab := tube_body_slab x v (Real.rpow_nonneg hδ.le (-h)) hball hA.2.2.2.2.2
  have hgain := H (δ ^ (2 : ℕ)) δ (R / 3) (sq_pos_of_pos hδ) hδd hδ hδR (by linarith) hDR
    n x v W (δ ^ (-h)) (8 * δ ^ (-h)) (δ ^ ν) (δ ^ (-t) * (δ / R) ^ (ω + σ)) (⋃ i, Y i)
    hA.1 hnmax hm (by linarith) (by positivity) (by positivity) hq
    (fun i => (hA.2.1 i).1) hball (fun i => (hW i).1)
    (fun i => (hW i).2.trans (hA.2.1 i).2.2.2) hmass hA.2.2.2.2.1 hslab
    (MeasurableSet.iUnion fun i => (hA.2.1 i).2.2.1)
    (by simpa only [show 3 * (R / 3) = R by ring] using hdensity)
  have hscalar : C * (δ ^ (-t) * (δ / R) ^ (ω + σ)) * δ ^ ν * (δ ^ (2 : ℕ)) ^ e *
      (δ ^ (-h)) ^ (-1 + σ) * (8 * δ ^ (-h)) ^ (-σ) *
      (δ ^ ω * (n * δ ^ 2) * (n * δ) ^ (-σ) * ((R / 3) / δ) ^ (ω + σ)) =
      κ * δ ^ (ω - t + ν + 2 * e + h) * (n * δ ^ 2) * (n * δ) ^ (-σ) := by
    have hi := scale_density_power_identity (σ := σ) (ω := ω) (ν := ν) (e := e) (h := h) (t := t)
      hC hδ hR
    calc
      _ = (C * (δ ^ (-t) * (δ / R) ^ (ω + σ)) * δ ^ ν * (δ ^ (2 : ℕ)) ^ e *
        (δ ^ (-h)) ^ (-1 + σ) * (8 * δ ^ (-h)) ^ (-σ) *
        δ ^ ω * ((R / 3) / δ) ^ (ω + σ)) * (n * δ ^ 2) * (n * δ) ^ (-σ) := by ring
      _ = _ := by rw [hi]
  rw [hscalar] at hgain
  apply le_trans _ hgain
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ (n : ℝ) * δ ^ 2)
  apply mul_le_mul_of_nonneg_left _ (by dsimp [κ]; positivity)
  exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
