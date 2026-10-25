-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.PacketGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketClusters
import Submission.WZ.Obl.wz_broad_grains_initialization.ClusterGain.Gain
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Multiplicity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Definitions

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (A)
open wz_clustered_cover_volume_gain.Parent (density_of_retained_mass)

lemma packet_gain_coefficient {δ θ κ ε η τ β ω : ℝ} (hδ : 0 < δ) (hθ : 0 < θ) :
    κ * δ ^ (ε + η) * (δ ^ (η + τ) / (2 * θ ^ (-β))) * (δ / (8 * θ)) ^ ω =
      (κ * (8 : ℝ) ^ (-ω) / 2) * δ ^ (ω + ε + 2 * η + τ) * θ ^ (β - ω) := by
  have hr : (δ / (8 * θ)) ^ ω = δ ^ ω * (8 : ℝ) ^ (-ω) * θ ^ (-ω) := by
    rw [Real.div_rpow hδ.le (by positivity), Real.mul_rpow (by norm_num) hθ.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), Real.rpow_neg hθ.le]
    ring
  have hi : (θ ^ (-β))⁻¹ = θ ^ β := by rw [Real.rpow_neg hθ.le, inv_inv]
  calc
    _ = (κ * (8 : ℝ) ^ (-ω) / 2) *
        (δ ^ (ε + η) * δ ^ (η + τ) * δ ^ ω) * (θ ^ β * θ ^ (-ω)) := by
      rw [hr]
      simp only [div_eq_mul_inv, mul_inv_rev, hi]
      ring
    _ = _ := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hθ]
      congr 2 <;> ring

/-- A common-scale angular packet refinement gives the narrow-case gain,
while preserving the full packet mass in the carrier decomposition. -/
theorem packet_gain {σ ω : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω)
    (hE : wz_clustered_cover_volume_gain.Parent.Interfaces.E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ δ θ β η τ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ θ → 8 * θ ≤ 1 → 0 ≤ β → 0 ≤ η →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y Z : Fin n → Set Space)
        (P : Space → Finset (Finset (Fin n))) (a : Space → Finset (Fin n) → Fin n),
      A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      PacketRefinement β δ θ v Y Z P a →
      ENNReal.ofReal (δ ^ τ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) →
      2 * (2 * 6 ^ 3 * 22 ^ 3 : ℝ) * δ ^ η₀ ≤ δ ^ (η + τ) →
      ENNReal.ofReal (κ * δ ^ (ω + ε + 2 * η + τ) * θ ^ (β - ω) *
        (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨κ, hκ, η₀, hη₀, hgain⟩ := ClusterGain.cluster_gain hσ hσ2 hω hE ε hε
  refine ⟨κ * (8 : ℝ) ^ (-ω) / 2, by positivity, η₀, hη₀, ?_⟩
  intro δ θ β η τ hδ hδsmall hδθ hθsmall hβ hη n x v Y Z P a hA hR hmass hdense
  classical
  have hθ : 0 < θ := hδ.trans_le hδθ
  have hv (i : Fin n) : ‖v i‖ = 1 := (hA.2.1 i).1
  have hYT (i : Fin n) : Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i)) :=
    (hA.2.1 i).2.2.2
  have hZT (i : Fin n) : Z i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i)) :=
    (hR.1 i).2.trans (hYT i)
  obtain ⟨y, w, hw, hcar, hoverlap, hdup, hsum⟩ := hR.finite_clusters hθ hδθ hv hZT
    (fun i => (hZT i).trans (hA.2.1 i).2.1)
  have hP : 1 ≤ 2 * θ ^ (-β) := by
    have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hθ (by linarith : θ ≤ 1)
      (neg_nonpos.mpr hβ)
    linarith
  have hM : ENNReal.ofReal (δ ^ (η + τ) * n * δ ^ 2) ≤
      ∑ ℓ : {ℓ // ℓ ∈ packetLabelUniverse θ x v}, ∑ i,
        volume (packetPiece θ v Z P a ℓ.val i) := by
    rw [hsum]
    exact density_of_retained_mass hδ hA.2.2.2.1 hmass
  have hg := hgain δ (8 * θ) η hδ hδsmall (by linarith) hθsmall hη n x v Y hv
    (fun i => (hA.2.1 i).2.1) hA.2.2.1 hA.2.2.2.2.1 hA.2.2.2.2.2
    {ℓ // ℓ ∈ packetLabelUniverse θ x v} (fun ℓ i => packetPiece θ v Z P a ℓ.val i)
    y w (2 * θ ^ (-β)) (2 * 6 ^ 3 * 22 ^ 3) (δ ^ (η + τ))
    (fun ℓ i => ⟨hR.measurable_piece ℓ.val i, fun _ hp => (hR.1 i).2 hp.1⟩)
    hYT hw hcar hP hoverlap (by positivity) hdup hM hdense
  rw [packet_gain_coefficient hδ hθ] at hg
  exact hg

end WangZahlLot.Obl.wz_broad_grains_initialization
