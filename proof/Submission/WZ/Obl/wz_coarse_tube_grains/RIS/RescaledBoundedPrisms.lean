-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaledBoundedPrisms.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaledPartitionPrisms
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.MappedLocalCells

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_extremal_lipschitz_grains wz_affine_robust_cluster_estimate
open scoped Classical

/-- Localize larger normalized partition pieces and construct the complete
physical prism family from their local volume and crossing budgets. -/
theorem rescaled_prism_family_of_bounded_partition {ζ β D : ℝ}
    (hζ : 0 < ζ) (hβ : 0 < β) (hD : 0 < D) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η ≤ ζ / 48 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ r R ρ c L : ℝ, 0 < δ → ∀ hρ : 0 < ρ, ρ ≤ 1 / 256 →
      0 < c → c ≤ 1 / 256 → 512 * c ≤ r → r ≤ 1 → r / 100 ≤ R → 0 ≤ L →
      16 * δ ≤ 128 * ρ * c →
      let ξ := δ / (100 * ρ)
      ξ ≤ 1 / 100 → ξ ≤ d → 2560 * c ≤ ξ ^ (ζ / 6) * r →
      ∀ (n G : ℕ) (x v : Fin n → V) (Y : Fin n → Set V)
        (B : Fin G → Set V) (p₀ : Fin G → V) (y w : V) (E : V ≃ₗᵢ[ℝ] V), E w = axis →
      let F := rescaleMap E y w (by norm_num : (0 : ℝ) < 1 / 100) hρ
      (n : ℝ) ≤ ξ ^ (-D) → ‖w‖ = 1 → (∀ i, ‖v i‖ = 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, μ (Y i) ≠ ⊤) →
      (∀ i, Y i ⊆ T δ (x i) (v i)) →
      (∀ i, (Y i).Nonempty → T δ (x i) (v i) ⊆ T ρ y w) →
      (∀ j, MeasurableSet (B j)) →
      (∀ j, B j ⊆ F ⁻¹' closedBall (F (p₀ j)) R) →
      (Pairwise fun j k => Disjoint (B j) (B k)) →
      (⋃ i, Y i) ⊆ ⋃ j, B j →
      (∀ i, ({j | (Y i ∩ B j).Nonempty}.ncard : ℝ) ≤ L) →
      2 * (ξ ^ η * δ ^ 2 * r) * n * ((12 * R / (r / 100)) ^ 3 * L) ≤ shadingMass Y →
      (∀ j p, μ (B j ∩ F ⁻¹' ball (F p) (r / 100)) ≤ o (ξ ^ (-η) * δ * ρ * r ^ 2)) →
      (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
        ({i | p ∈ Y i ∧ pd (v i) u ≤ s}.ncard : ℝ) ≤
          (ξ ^ (-η) * (s / ρ) ^ β) * incidence Y p) →
      ∃ (N : ℕ) (C : Fin N → Set V) (q : Fin N → V) (parent : Fin N → Fin G),
        (∀ j, MeasurableSet (C j) ∧ C j ⊆ B (parent j) ∧
          C j ⊆ F ⁻¹' ball (F (q j)) (r / 100)) ∧
        (Pairwise fun j k => Disjoint (C j) (C k)) ∧
        (⋃ j, C j) = ⋃ j, B j ∧
        (N : ℝ) ≤ G * (12 * R / (r / 100)) ^ 3 ∧
        (∀ i, ({j | (Y i ∩ C j).Nonempty}.ncard : ℝ) ≤ (12 * R / (r / 100)) ^ 3 * L) ∧
        Nonempty (CellPrismFamily δ r ρ c ζ x v Y C q y w) := by
  obtain ⟨η, hη, hη1, hηζ, d, hd, hprism⟩ := rescaled_prism_family_of_thin_partition hζ hβ hD
  refine ⟨η, hη, hη1, hηζ, d, hd, ?_⟩
  intro δ r R ρ c L hδ hρ hρ256 hc hc256 hcr hr1 hrR hL hsize ξ hξ100 hξd hbudget
    n G x v Y B p₀ y w E hew F hnD hw hv hY hfin hYT hcarrier hB hbound hdisj hcover
    hcross hcost hvol hbroad
  have hr : 0 < r := by linarith
  have hR : 0 < R := (by positivity : 0 < r / 100).trans_le hrR
  obtain ⟨N, C, q, parent, hC, hCdisj, hunion, hN, hcount⟩ :=
    mapped_bounded_partition_localization F.toHomeomorph (by positivity : 0 < r / 100)
      hrR B p₀ hB hbound hdisj
  have hcross' (i : Fin n) :
      ({j | (Y i ∩ C j).Nonempty}.ncard : ℝ) ≤ (12 * R / (r / 100)) ^ 3 * L :=
    (hcount (Y i)).trans (mul_le_mul_of_nonneg_left (hcross i) (by positivity))
  refine ⟨N, C, q, parent, hC, hCdisj, hunion, hN, hcross', ?_⟩
  apply hprism δ r ρ c ((12 * R / (r / 100)) ^ 3 * L) hδ hρ hρ256 hc hc256 hcr hr1
    (by positivity) hsize hξ100 hξd hbudget n N x v Y C q y w E hew
    hnD hw hv hY hfin hYT hcarrier (fun j => (hC j).1) (fun j => (hC j).2.2) hCdisj
    (by rw [hunion]; exact hcover) hcross' hcost
  · intro j
    exact (measure_mono (subset_inter (hC j).2.1 (hC j).2.2)).trans (hvol (parent j) (q j))
  · exact hbroad

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
