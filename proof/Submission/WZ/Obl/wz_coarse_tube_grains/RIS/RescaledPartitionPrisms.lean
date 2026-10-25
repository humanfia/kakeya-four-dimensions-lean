-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaledPartitionPrisms.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaledCellPrisms
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaledSeparation
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CellPrismRefinement

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_extremal_lipschitz_grains wz_affine_robust_cluster_estimate
open scoped Classical

set_option maxHeartbeats 1200000 in
/-- A thin partition in normalized coordinates supplies separation, local
density, relative planarity, and a physical prism family with arbitrary loss. -/
theorem rescaled_prism_family_of_thin_partition {ζ β D : ℝ}
    (hζ : 0 < ζ) (hβ : 0 < β) (hD : 0 < D) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η ≤ ζ / 48 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ r ρ c L : ℝ, 0 < δ → ∀ hρ : 0 < ρ, ρ ≤ 1 / 256 →
      0 < c → c ≤ 1 / 256 → 512 * c ≤ r → r ≤ 1 → 0 ≤ L →
      16 * δ ≤ 128 * ρ * c →
      let ξ := δ / (100 * ρ)
      ξ ≤ 1 / 100 → ξ ≤ d → 2560 * c ≤ ξ ^ (ζ / 6) * r →
      ∀ (n N : ℕ) (x v : Fin n → V) (Y : Fin n → Set V)
        (C : Fin N → Set V) (q : Fin N → V) (y w : V) (E : V ≃ₗᵢ[ℝ] V), E w = axis →
      let F := rescaleMap E y w (by norm_num : (0 : ℝ) < 1 / 100) hρ
      (n : ℝ) ≤ ξ ^ (-D) → ‖w‖ = 1 → (∀ i, ‖v i‖ = 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, μ (Y i) ≠ ⊤) →
      (∀ i, Y i ⊆ T δ (x i) (v i)) →
      (∀ i, (Y i).Nonempty → T δ (x i) (v i) ⊆ T ρ y w) →
      (∀ j, MeasurableSet (C j)) → (∀ j, C j ⊆ F ⁻¹' ball (F (q j)) (r / 100)) →
      (Pairwise fun j k => Disjoint (C j) (C k)) →
      (⋃ i, Y i) ⊆ ⋃ j, C j →
      (∀ i, ({j | (Y i ∩ C j).Nonempty}.ncard : ℝ) ≤ L) →
      2 * (ξ ^ η * δ ^ 2 * r) * n * L ≤ shadingMass Y →
      (∀ j, μ (C j) ≤ o (ξ ^ (-η) * δ * ρ * r ^ 2)) →
      (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
        ({i | p ∈ Y i ∧ pd (v i) u ≤ s}.ncard : ℝ) ≤
          (ξ ^ (-η) * (s / ρ) ^ β) * incidence Y p) →
      Nonempty (CellPrismFamily δ r ρ c ζ x v Y C q y w) := by
  obtain ⟨η₀, hη₀, hη₀1, hη₀ζ, d₀, hd₀, hlocal⟩ :=
    rescaled_cell_prism_family (half_pos hζ) hβ hD
  let η := η₀ / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : 4 * η = η₀ := by dsimp [η]; ring
  obtain ⟨d₁, hd₁, hseparate⟩ := BrushPlanarity.rescaled_separated_dense_input_power hη
  refine ⟨η, hη, by dsimp [η]; linarith, by dsimp [η]; linarith,
    min d₀ d₁, lt_min hd₀ hd₁, ?_⟩
  intro δ r ρ c L hδ hρ hρ256 hc hc256 hcr hr1 hL hsize ξ hξ100 hξd hbudget
    n N x v Y C q y w E hew F hnD hw hv hY hfin hYT hcarrier hC hball hdisj hcover
    hcross hcost hvol hbroad
  have hρ1 : ρ ≤ 1 := by linarith
  have hr : 0 < r := by linarith
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξ1 : ξ ≤ 1 := hξ100.trans (by norm_num)
  have hδξ : δ ≤ ξ := by
    apply (le_div_iff₀ (by positivity : 0 < 100 * ρ)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hρ256 hδ.le]
  have hδ1 : δ ≤ 1 := hδξ.trans hξ1
  have hδρr : δ ≤ ρ * r := by
    have hh := mul_le_mul_of_nonneg_left hcr hρ.le
    nlinarith
  obtain ⟨W, hW, hkeep, hsep, _, _, hdense, hrelative⟩ :=
    hseparate δ ρ r L hδ hρ hρ1 hδρr hL hξ1 (hξd.trans (min_le_right _ _))
      n N x v Y C q y w E hew hw hv hY hfin hYT hcarrier hC hball hdisj hcover hcross hcost
  have hbudget' : 2560 * c ≤ ξ ^ (η₀ + (ζ / 2) / 6) * r :=
    hbudget.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hξ hξ1 (by linarith)) hr.le)
  have hvol' (j : Fin N) : μ (C j) ≤ o (ξ ^ (-η₀) * δ * ρ * r ^ 2) := by
    apply (hvol j).trans (ENNReal.ofReal_le_ofReal ?_)
    have hp : ξ ^ (-η) ≤ ξ ^ (-η₀) :=
      Real.rpow_le_rpow_of_exponent_ge hξ hξ1 (by dsimp [η]; linarith)
    gcongr
  have hcap : ∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
      ({i | p ∈ W i ∧ pd (v i) u ≤ s}.ncard : ℝ) ≤
        (ξ ^ (-η₀) * (s / ρ) ^ β) * incidence W p := by
    intro p u s hu hs hsρ
    have hs0 : 0 ≤ s := hδ.le.trans hs
    have hh := BrushPlanarity.angular_cap_bound_of_relative_incidence v
      (Real.rpow_pos_of_pos hξ (3 * η))
      (show 0 ≤ ξ ^ (-η) * (s / ρ) ^ β by positivity) (fun i => (hW i).2)
      hrelative (fun p u hu => hbroad p u s hu hs hsρ) p u hu
    have he : (ξ ^ (-η) * (s / ρ) ^ β) / ξ ^ (3 * η) = ξ ^ (-η₀) * (s / ρ) ^ β := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hξ.le]
      calc
        _ = (ξ ^ (-η) * ξ ^ (-(3 * η))) * (s / ρ) ^ β := by ring
        _ = _ := by rw [← Real.rpow_add hξ]; congr 2; dsimp [η]; ring
    simpa only [he, pd] using hh
  obtain ⟨R⟩ := hlocal δ r ρ c hδ hρ hρ256 hc hc256 hcr hr1 hsize hξ100
    (hξd.trans (min_le_left _ _)) hbudget' n N x v W C q y w E hew hnD hw hv
    (fun i => (hW i).1) (fun i => (hW i).2.trans (hYT i))
    (fun i hi => hcarrier i (hi.mono (hW i).2)) hC hball hdisj
    ((iUnion_mono fun i => (hW i).2).trans hcover) hsep
    (by simpa only [hηeq, o, μ] using hdense) hvol' hcap
  have hkeepδ : o (δ ^ (3 * η)) * (∑ i, μ (Y i)) ≤ ∑ i, μ (W i) :=
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow hδ.le hδξ (by positivity : 0 ≤ 3 * η))) _).trans hkeep
  exact ⟨(R.rebase hδ hδ1 hρ.le hc.le (by positivity : 0 ≤ 3 * η)
    (fun i => (hW i).2) hkeepδ).weaken hδ hδ1 hρ.le hc.le (by dsimp [η]; linarith)⟩

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
