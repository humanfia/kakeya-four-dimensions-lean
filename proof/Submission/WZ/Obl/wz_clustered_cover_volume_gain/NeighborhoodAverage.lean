-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.NeighborhoodAverage.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodEstimate
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DenseMass

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

/-- An average shading density is sufficient for the neighbourhood estimate;
its only additional cost is one factor of that density. -/
theorem tube_neighborhood_average {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ (D d r : ℝ), 0 < D → D ≤ d₀ → 0 < d → d ≤ r → r ≤ 1 → D ≤ r / 8 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (m l q : ℝ),
      0 < n → (n : ℝ) ≤ D ^ (-100 : ℝ) → 1 ≤ m → 1 ≤ l → 0 < q → 128 * D ^ η ≤ q →
      (∀ i, ‖v i‖ = 1) → (∀ i, Tube d (x i) (v i) ⊆ ball 0 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube d (x i) (v i)) →
      ENNReal.ofReal (q * n * d ^ 2) ≤ ∑ i, volume (Y i) →
      BodyConvexCount (fun i => Tube d (x i) (v i)) (d ^ 2) m →
      BodySlabCount (fun i => Tube d (x i) (v i)) l →
      ENNReal.ofReal (A * q * D ^ ε *
        (r ^ ω * m ^ (-1 + σ) * l ^ (-σ) * n ^ (1 - σ) * d ^ (2 - σ) * (r / d) ^ σ)) ≤
        volume (thickening (3 * r) (⋃ i, Y i)) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ := tube_neighborhood_estimate hσ hσhalf hω hE ε hε
  refine ⟨A / 768, η, d₀, by positivity, hη, hd₀, hd₀small, ?_⟩
  intro D d r hD hDd hd hdr hr1 hDr n x v Y m l q hn hnmax hm hl hq hqD hv hball hYm hYT hmass hK hF
  have hr : 0 < r := hd.trans_le hdr
  obtain ⟨k, f, hf, hk, hkcount, hfden⟩ := select_large_masses Y hn (sq_pos_of_pos hd) hq
    (show 0 ≤ 64 * D ^ η by positivity) (by linarith : 2 * (64 * D ^ η) ≤ q)
    (fun i => (measure_mono (hYT i)).trans
      (WangZahlLot.Obl.wz_affine_packet_counting_transfer.tube_volume_upper hd (hdr.trans hr1) (x i) (v i) (hv i))) hmass
  have hkn : k ≤ n := by simpa using Fintype.card_le_of_injective f hf
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnratio : 1 ≤ l * n / k := by
    rw [le_div_iff₀ hkR]
    have hknR : (k : ℝ) ≤ n := Nat.cast_le.mpr hkn
    nlinarith [mul_le_mul_of_nonneg_right hl hnR.le]
  have H' := H D d r hD hDd hd hdr hr1 hDr k (x ∘ f) (v ∘ f) (Y ∘ f) m (l * n / k)
    hk ((Nat.cast_le.mpr hkn).trans hnmax) hm hnratio (fun i => hv (f i))
    (fun i => hball (f i)) (fun i => hYm (f i)) (fun i => hYT (f i)) hfden
    (body_convex_count_restrict (sq_nonneg d) hK f hf) (body_slab_count_restrict hk hF f hf)
  have hsub : thickening (3 * r) (⋃ i, Y (f i)) ⊆ thickening (3 * r) (⋃ i, Y i) := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_thickening_iff.mpr ⟨z, mem_iUnion.mpr ⟨f i, hi⟩, hpz⟩
  apply le_trans _ (H'.trans (measure_mono hsub))
  apply ENNReal.ofReal_le_ofReal
  have hfactor := subfamily_slab_factor (σ := σ) (zero_lt_one.trans_le hl) hnR hkR
  have hnp : (n : ℝ) ^ (-σ) * n = (n : ℝ) ^ (1 - σ) := by
    rw [show 1 - σ = -σ + 1 by ring, Real.rpow_add hnR, Real.rpow_one]
  have hfac : 0 ≤ A * D ^ ε * r ^ ω * m ^ (-1 + σ) * l ^ (-σ) *
      n ^ (-σ) * d ^ (2 - σ) * (r / d) ^ σ := by positivity
  have hh := mul_le_mul_of_nonneg_left hkcount hfac
  convert hh using 1
  · rw [← hnp]
    ring
  · calc
      _ = A * D ^ ε * r ^ ω * m ^ (-1 + σ) *
          ((l * n / k) ^ (-σ) * (k : ℝ) ^ (1 - σ)) * d ^ (2 - σ) * (r / d) ^ σ := by ring
      _ = _ := by rw [hfactor]; ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
