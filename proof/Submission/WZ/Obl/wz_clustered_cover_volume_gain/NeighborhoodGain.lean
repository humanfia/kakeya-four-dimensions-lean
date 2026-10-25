-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.NeighborhoodGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodAverage
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodTransfer

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

/-- The neighbourhood estimate, expressed as an actual gain over the fine
scale baseline after imposing a common lower ball-density class. -/
theorem regular_density_neighborhood_gain {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
    ∀ D d r : ℝ, 0 < D → D ≤ d₀ → 0 < d → d ≤ r → r ≤ 1 → D ≤ r / 8 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (m l q lam : ℝ) (U : Set Space),
    0 < n → (n : ℝ) ≤ D ^ (-100 : ℝ) → 1 ≤ m → 1 ≤ l → 0 < q → 0 ≤ lam →
    128 * D ^ η ≤ q → (∀ i, ‖v i‖ = 1) → (∀ i, Tube d (x i) (v i) ⊆ ball 0 1) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube d (x i) (v i)) →
    ENNReal.ofReal (q * n * d ^ 2) ≤ ∑ i, volume (Y i) →
    BodyConvexCount (fun i => Tube d (x i) (v i)) (d ^ 2) m →
    BodySlabCount (fun i => Tube d (x i) (v i)) l → MeasurableSet U →
    (∀ i p, p ∈ Y i → ENNReal.ofReal (lam * (3 * r) ^ 3) ≤ volume (U ∩ ball p (3 * r))) →
    ENNReal.ofReal (C * lam * q * D ^ ε * m ^ (-1 + σ) * l ^ (-σ) *
      (d ^ ω * (n * d ^ 2) * (n * d) ^ (-σ) * (r / d) ^ (ω + σ))) ≤ volume U := by
  intro ε hε
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ := tube_neighborhood_average hσ hσhalf hω hE ε hε
  refine ⟨C / 512, η, d₀, by positivity, hη, hd₀, hd₀small, ?_⟩
  intro D d r hD hDd hd hdr hr1 hDr n x v Y m l q lam U hn hnmax hm hl hq hlam hqD
    hv hball hYm hYT hmass hK hF hUm hdensity
  have hr : 0 < r := hd.trans_le hdr
  have hN := H D d r hD hDd hd hdr hr1 hDr n x v Y m l q hn hnmax hm hl hq hqD
    hv hball hYm hYT hmass hK hF
  have hbound : Bornology.IsBounded (⋃ i, Y i) := isBounded_ball.subset (by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hball i (hYT i hi))
  have hh := lower_union_of_neighborhood (by positivity : 0 < 3 * r) hbound hUm hN (by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hdensity i p hi)
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ lam / 512)] at hh
  convert hh using 1
  congr 1
  rw [← neighborhood_factor_baseline hd hr (Nat.cast_pos.mpr hn)]
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
