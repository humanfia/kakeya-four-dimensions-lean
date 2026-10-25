-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.LongRescale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.LongGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.RescaleEstimate

/-!
# Local volume estimates inside carriers of bounded length

The extraction constant is uniform over carrier lengths from one through eight. Fine tubes
retain unit length; the normalized slab hypothesis uses the centered two-fold dilation.
-/

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_affine_robust_cluster_estimate

/-- Bounded-length carriers satisfy the same rescaled-family bounds as unit carriers. -/
theorem rescaled_subfamily_carrier :
    ∃ D : ℕ, 0 < D ∧ ∀ {δ ρ η m l L : ℝ} {n : ℕ} {x v : Fin n → Space}
      {Y : Fin n → Set Space} {y w : Space},
      0 < δ → δ ≤ ρ → ρ ≤ 1 → 1 ≤ L → L ≤ 8 → 0 < n → ‖w‖ = 1 →
      (∀ i, ‖v i‖ = 1 ∧ Tube δ (x i) (v i) ⊆ Carrier L ρ y w ∧
        MeasurableSet (Y i) ∧ Y i ⊆ Tube δ (x i) (v i)) →
      (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
      Dense δ η Y → Katz δ m x v →
      ReferenceSlabCount (Carrier (2 * L) (2 * ρ) y w) l (fun i => Tube δ (x i) (v i)) →
      RescaledFamily D δ ρ η m l Y := by
  obtain ⟨D, hD, hrescale⟩ := rescaled_subfamily_of_bounds 10 (by norm_num)
  refine ⟨D, hD, ?_⟩
  intro δ ρ η m l L n x v Y y w hδ hδρ hρ1 hL1 hL8 hn hw hfib hdist hdense hK hB
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hL : 0 ≤ L := by linarith
  obtain ⟨e, hew⟩ := exists_rotation hw
  have hκ : (0 : ℝ) < 1 / 100 := by norm_num
  apply hrescale (y := y) (w := w) e hδ hδρ hρ1 hn hew
    (fun i => ⟨(hfib i).1, (hfib i).2.2⟩)
    (fun i => pd_lt_of_tube_subset_carrier hδ (hfib i).1 hw (hfib i).2.1)
    (fun i j => ((midpoint_dist_lt_carrier hδ hρ1 hL hw (hfib i).2.1
      (hfib j).2.1).le).trans (by linarith))
    _ (fun i => ((hfib i).2.1).trans (carrier_subset_dilate hρ.le y w)) _ _
    hdist hdense hK hB
  · intro i
    have hmid : x i + (1 / 2 : ℝ) • v i ∈ Carrier L ρ y w := by
      apply (hfib i).2.1
      apply self_subset_thickening hδ
      rw [segment_eq_image']
      exact ⟨1 / 2, by norm_num, by simp⟩
    have h := rescaleMap_carrier_norm_lt e hew hκ hρ hρ1 hL hmid
    linarith
  · rintro _ ⟨p, hp, rfl⟩
    rw [mem_ball_zero_iff]
    have hpoint : p ∈ Carrier (2 * L) (2 * ρ) y w := hp
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hpoint
    rw [segment_eq_image'] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    simp only [add_sub_cancel_left] at hpq
    have heq : y + ((1 - 2 * L) / 2) • w + s • ((2 * L) • w) =
        y + ((1 - 2 * L) / 2 + s * (2 * L)) • w := by module
    have hqnorm : ‖rescaleMap e y w hκ hρ
        (y + ((1 - 2 * L) / 2) • w + s • ((2 * L) • w))‖ ≤ (1 / 100) * L := by
      rw [heq, rescaleMap_segment_norm e hew hκ hρ]
      apply mul_le_mul_of_nonneg_left _ hκ.le
      apply abs_le.mpr
      constructor <;> nlinarith [hs.1, hs.2]
    have hd := rescaleMap_dist_le e y w hκ hρ hρ1 p
      (y + ((1 - 2 * L) / 2) • w + s • ((2 * L) • w))
    have hdist : (1 / 100) * ρ⁻¹ * dist p
        (y + ((1 - 2 * L) / 2) • w + s • ((2 * L) • w)) < 2 / 100 := by
      calc
        _ < (1 / 100) * ρ⁻¹ * (2 * ρ) := by gcongr
        _ = 2 / 100 := by field_simp
    have hn := norm_le_norm_add_norm_sub
      (rescaleMap e y w hκ hρ (y + ((1 - 2 * L) / 2) • w + s • ((2 * L) • w)))
      (rescaleMap e y w hκ hρ p)
    rw [norm_sub_rev, ← dist_eq_norm] at hn
    linarith
  · exact (wz_direction_density_transfer.tube_volume_lower hρ y w hw).trans
      (measure_mono ((tube_subset_carrier hL1 y w).trans (carrier_subset_dilate hρ.le y w)))

namespace Interfaces

/-- `E(σ,ω)` in carriers of any length in `[1,8]`, uniformly in that length. -/
theorem local_rescaling_carrier_of_estimate {σ ω : ℝ} (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1 / 2)
    (hω : 0 ≤ ω) (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 →
    ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ L : ℝ, 1 ≤ L → L ≤ 8 →
    ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (y w : V),
    0 < n → ‖w‖ = 1 →
    (∀ i, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ Carrier L ρ y w ∧
      MeasurableSet (Y i) ∧ Y i ⊆ T δ (x i) (v i)) →
    X δ n x v → o (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i) → K δ m n x v →
    ReferenceSlabCount (Carrier (2 * L) (2 * ρ) y w) l (fun i => T δ (x i) (v i)) →
    o (κ * δ ^ ε * (δ / ρ) ^ ω * m⁻¹ * (n * δ ^ 2) *
      (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ (-σ)) ≤ μ (⋃ i, Y i) := by
  obtain ⟨D, hD, hsubfam⟩ := rescaled_subfamily_carrier
  intro ε hε
  obtain ⟨κ, hκ, η, hη, hbound⟩ := local_bound_of_rescaled_family hσ hσ2 hω hE D hD ε hε
  refine ⟨κ, hκ, η, hη, ?_⟩
  intro δ ρ hδ hδ100 hδρ hρ1 m l hm hl L hL1 hL8 n x v Y y w hn hw hfib hX hdense hK hB
  exact hbound δ ρ hδ hδ100 hδρ hρ1 m l hm hl n Y hn hdense
    (hsubfam hδ hδρ hρ1 hL1 hL8 hn hw hfib hX hdense hK hB)

end Interfaces

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
