-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PacketRescaledLocality.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaledPrismLocality
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalPacketData

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_affine_robust_cluster_estimate

/-- Every full prism of a packet is local in the normalized coordinates,
provided its original shading was local there. -/
theorem LocalPrismPacket.rescaled_locality {δ r ρ c ε κ : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} {p₀ y w : V}
    (R : LocalPrismPacket δ r ρ c ε x v Y p₀ y w)
    (hκ : 0 < κ) (hρ : 0 < ρ) (hρ256 : ρ ≤ 1 / 256) (hc : 0 ≤ c)
    (hsize : 16 * δ ≤ 128 * ρ * c) (hcr : 512 * c ≤ r) (hw : ‖w‖ = 1)
    (E : V ≃ₗᵢ[ℝ] V) (hew : E w = axis)
    (hY : ∀ i, Y i ⊆ (rescaleMap E y w hκ hρ) ⁻¹'
      ball (rescaleMap E y w hκ hρ p₀) (κ * r)) :
    ∀ z ∈ R.centers, P (16 * δ) (128 * ρ * c) c z R.frame ⊆
      (rescaleMap E y w hκ hρ) ⁻¹'
        ball (rescaleMap E y w hκ hρ p₀) (3 * (κ * r)) := by
  intro z hz
  have hbc : 128 * ρ * c ≤ c := by
    have hh := mul_le_mul_of_nonneg_right hρ256 hc
    nlinarith
  have hmeet : (P (16 * δ) (128 * ρ * c) c z R.frame ∩
      (rescaleMap E y w hκ hρ) ⁻¹' ball (rescaleMap E y w hκ hρ p₀) (κ * r)).Nonempty := by
    obtain ⟨p, hp⟩ := (R.piece_data z hz).2.2.1
    have hpZ : p ∈ ⋃ i, R.shading i := R.union_eq ▸ mem_iUnion₂.mpr ⟨z, hz, hp⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hpZ
    exact ⟨p, (R.piece_data z hz).2.1 hp, hY i ((R.refines i).2 hi)⟩
  have hh := rescale_prism_subset_triple_ball hκ hρ (by linarith) hc hsize hbc le_rfl hcr
    hw R.frame E hew R.aligned hmeet
  intro p hp
  exact hh (mem_image_of_mem _ hp)

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
