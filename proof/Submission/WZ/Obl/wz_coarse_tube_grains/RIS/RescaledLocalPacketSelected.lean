-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaledLocalPacketSelected.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaledLocalPacket
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalPacketLift

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_extremal_lipschitz_grains wz_affine_robust_cluster_estimate
open scoped Classical

/-- Normalize local density by the occupied tubes and restore the original
fine indices after the relative-broad packet construction. -/
theorem rescaled_local_prism_packet_selected {ζ β D : ℝ}
    (hζ : 0 < ζ) (hβ : 0 < β) (hD : 0 < D) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η ≤ ζ / 3 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ r ρ c : ℝ, 0 < δ → ∀ hρ : 0 < ρ, ρ ≤ 1 / 256 →
      0 < c → c ≤ 1 / 256 → 512 * c ≤ r → r ≤ 1 → 16 * δ ≤ 128 * ρ * c →
      let ξ := δ / (100 * ρ)
      ξ ≤ 1 / 100 → ξ ≤ d → 2560 * c ≤ ξ ^ (η + ζ / 3) * r →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (p₀ y w : V)
        (E : V ≃ₗᵢ[ℝ] V), E w = axis →
      let F := rescaleMap E y w (by norm_num : (0 : ℝ) < 1 / 100) hρ
      ∀ Q : Finset (Fin n), Q.Nonempty → (Q.card : ℝ) ≤ ξ ^ (-D) → ‖w‖ = 1 →
      (∀ i ∈ Q, ‖v i‖ = 1) → (∀ i, MeasurableSet (Y i)) →
      (∀ i, i ∉ Q → Y i = ∅) →
      (∀ i, Y i ⊆ T δ (x i) (v i) ∩ F ⁻¹' ball (F p₀) (r / 100)) →
      (∀ i ∈ Q, T δ (x i) (v i) ⊆ T ρ y w) →
      o (ξ ^ η * Q.card * δ ^ 2 * r) ≤ ∑ i, μ (Y i) →
      μ (⋃ i, Y i) ≤ o (ξ ^ (-η) * δ * ρ * r ^ 2) →
      (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
        ({i | p ∈ Y i ∧ pd (v i) u ≤ s}.ncard : ℝ) ≤
          (ξ ^ (-η) * (s / ρ) ^ β) * incidence Y p) →
      Nonempty (LocalPrismPacket δ r ρ c ζ x v Y p₀ y w) := by
  obtain ⟨η, hη, hη1, hηζ, d, hd, hlocal⟩ := rescaled_local_prism_packet hζ hβ hD
  refine ⟨η, hη, hη1, hηζ, d, hd, ?_⟩
  intro δ r ρ c hδ hρ hρ256 hc hc256 hcr hr1 hsize ξ hξ100 hξd hbudget
    n x v Y p₀ y w E hew F Q hQ hQD hw hv hY hzero hYT hcover hdense hvol hbroad
  let j := SelectedShading.enum Q
  have hjQ (i : Fin Q.card) : j i ∈ Q := SelectedShading.enum_mem Q i
  have hmemQ {i : Fin n} {p : V} (hp : p ∈ Y i) : i ∈ Q := by
    by_contra hi
    rw [hzero i hi] at hp
    exact hp.elim
  have hsum : (∑ i, μ (Y (j i))) = ∑ i, μ (Y i) := SelectedShading.sum_enum μ Q Y hzero
  have hunionY : (⋃ i, Y (j i)) = ⋃ i, Y i := SelectedShading.union_enum Q Y hzero
  have hincY (p : V) : incidence (Y ∘ j) p = incidence Y p := by
    rw [incidence_eq_ncard, incidence_eq_ncard]
    exact congrArg Nat.cast (SelectedShading.count_enum Q (fun i => p ∈ Y i) (fun _ => hmemQ))
  have hbroad' : ∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
      ({i | p ∈ (Y ∘ j) i ∧ pd ((v ∘ j) i) u ≤ s}.ncard : ℝ) ≤
        (ξ ^ (-η) * (s / ρ) ^ β) * incidence (Y ∘ j) p := by
    intro p u s hu hs hsρ
    rw [hincY]
    simp only [Function.comp_apply]
    rw [SelectedShading.count_enum Q
      (fun i => p ∈ Y i ∧ pd (v i) u ≤ s) (fun _ h => hmemQ h.1)]
    exact hbroad p u s hu hs hsρ
  obtain ⟨R⟩ := hlocal δ r ρ c hδ hρ hρ256 hc hc256 hcr hr1 hsize hξ100 hξd hbudget
    Q.card (x ∘ j) (v ∘ j) (Y ∘ j) p₀ y w E hew (Finset.card_pos.mpr hQ) hQD hw
    (fun i => hv (j i) (hjQ i)) (fun i => hY (j i)) (fun i => hYT (j i))
    (fun i => hcover (j i) (hjQ i))
    (by simpa only [Function.comp_apply, hsum] using hdense)
    (by simpa only [Function.comp_apply, hunionY] using hvol) hbroad'
  exact ⟨R.lift Q hzero⟩

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
