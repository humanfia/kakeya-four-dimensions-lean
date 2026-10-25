-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaledCellPrisms.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.MappedPrismAssembly
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaledLocalPacketSelected

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_extremal_lipschitz_grains wz_affine_robust_cluster_estimate
open scoped Classical

set_option maxHeartbeats 1200000 in
/-- Assemble relative-broad local cells in normalized coordinates, retaining
physical tubes, prisms, and shading indices throughout. -/
theorem rescaled_cell_prism_family {ζ β D : ℝ} (hζ : 0 < ζ) (hβ : 0 < β) (hD : 0 < D) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η ≤ ζ / 6 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ δ r ρ c : ℝ, 0 < δ → ∀ hρ : 0 < ρ, ρ ≤ 1 / 256 →
      0 < c → c ≤ 1 / 256 → 512 * c ≤ r → r ≤ 1 → 16 * δ ≤ 128 * ρ * c →
      let ξ := δ / (100 * ρ)
      ξ ≤ 1 / 100 → ξ ≤ d → 2560 * c ≤ ξ ^ (η + ζ / 6) * r →
      ∀ (n N : ℕ) (x v : Fin n → V) (Y : Fin n → Set V)
        (C : Fin N → Set V) (q : Fin N → V) (y w : V) (E : V ≃ₗᵢ[ℝ] V), E w = axis →
      let F := rescaleMap E y w (by norm_num : (0 : ℝ) < 1 / 100) hρ
      (n : ℝ) ≤ ξ ^ (-D) → ‖w‖ = 1 → (∀ i, ‖v i‖ = 1) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) →
      (∀ i, (Y i).Nonempty → T δ (x i) (v i) ⊆ T ρ y w) →
      (∀ j, MeasurableSet (C j)) → (∀ j, C j ⊆ F ⁻¹' ball (F (q j)) (r / 100)) →
      (Pairwise fun j k => Disjoint (C j) (C k)) →
      (⋃ i, Y i) ⊆ ⋃ j, C j →
      (∀ i j k, j ≠ k → (Y i ∩ C j).Nonempty → (Y i ∩ C k).Nonempty →
        10 * (r / 100) < dist (F (q j)) (F (q k))) →
      (∀ j, o (ξ ^ η * ({i | (Y i ∩ C j).Nonempty}.ncard : ℝ) * δ ^ 2 * r) ≤
        ∑ i, μ (Y i ∩ C j)) →
      (∀ j, μ (C j) ≤ o (ξ ^ (-η) * δ * ρ * r ^ 2)) →
      (∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
        ({i | p ∈ Y i ∧ pd (v i) u ≤ s}.ncard : ℝ) ≤
          (ξ ^ (-η) * (s / ρ) ^ β) * incidence Y p) →
      Nonempty (CellPrismFamily δ r ρ c ζ x v Y C q y w) := by
  obtain ⟨η, hη, hη1, hηζ, d₀, hd₀, hlocal⟩ :=
    rescaled_local_prism_packet_selected (half_pos hζ) hβ hD
  obtain ⟨d₁, hd₁, hlog⟩ := logarithmic_count_power hD (half_pos hζ)
  refine ⟨η, hη, hη1, by linarith, min d₀ d₁, lt_min hd₀ hd₁, ?_⟩
  intro δ r ρ c hδ hρ hρ256 hc hc256 hcr hr1 hsize ξ hξ100 hξd hbudget
    n N x v Y C q y w E hew F hnD hw hv hY hYT hcarrier hC hball hdisj hcover hsep hdense hvol hbroad
  have hr : 0 < r := by linarith
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hδξ : δ ≤ ξ := by
    apply (le_div_iff₀ (by positivity : 0 < 100 * ρ)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hρ256 hδ.le]
  have hδ1 : δ ≤ 1 := hδξ.trans (hξ100.trans (by norm_num))
  have hbudget' : 2560 * c ≤ ξ ^ (η + (ζ / 2) / 3) * r := by
    convert hbudget using 1 <;> congr 2 <;> ring
  have hex (j : Fin N) :
      Nonempty (LocalPrismPacket δ r ρ c (ζ / 2) x v (fun i => Y i ∩ C j) (q j) y w) := by
    let Q : Finset (Fin n) := {i | (Y i ∩ C j).Nonempty}.toFinset
    by_cases hQ : Q.Nonempty
    · have hQcard : Q.card = {i | (Y i ∩ C j).Nonempty}.ncard := by
        simp only [Q, ncard_eq_toFinset_card']
      have hQn : (Q.card : ℝ) ≤ n := by
        exact_mod_cast (show Q.card ≤ n by simpa using Finset.card_le_univ Q)
      have hzero (i : Fin n) (hi : i ∉ Q) : Y i ∩ C j = ∅ :=
        not_nonempty_iff_eq_empty.mp (by simpa only [Q, mem_toFinset, mem_setOf_eq] using hi)
      have hcap : ∀ p u s, ‖u‖ = 1 → δ ≤ s → s ≤ ρ →
          ({i | p ∈ Y i ∩ C j ∧ pd (v i) u ≤ s}.ncard : ℝ) ≤
            (ξ ^ (-η) * (s / ρ) ^ β) * incidence (fun i => Y i ∩ C j) p := by
        intro p u s hu hs hsρ
        by_cases hp : p ∈ C j
        · simpa only [incidence_eq_ncard, mem_inter_iff, hp, and_true] using hbroad p u s hu hs hsρ
        · simp [incidence_eq_ncard, hp]
      exact hlocal δ r ρ c hδ hρ hρ256 hc hc256 hcr hr1 hsize hξ100
        (hξd.trans (min_le_left _ _)) hbudget' n x v (fun i => Y i ∩ C j) (q j) y w E hew Q
        hQ (hQn.trans hnD) hw (fun i _ => hv i) (fun i => (hY i).inter (hC j)) hzero
        (fun i p hp => ⟨hYT i hp.1, hball j hp.2⟩)
        (fun i hi => hcarrier i ((show (Y i ∩ C j).Nonempty from
          by simpa only [Q, mem_toFinset, mem_setOf_eq] using hi).mono inter_subset_left))
        (by simpa only [hQcard] using hdense j)
        ((measure_mono (iUnion_subset fun i => inter_subset_right)).trans (hvol j)) hcap
    · apply empty_local_prism_packet x v (fun i => Y i ∩ C j) (q j) y w hw
      intro i
      apply not_nonempty_iff_eq_empty.mp
      intro hi
      exact hQ ⟨i, by simpa only [Q, mem_toFinset, mem_setOf_eq] using hi⟩
  let R (j : Fin N) := Classical.choice (hex j)
  have hlocality (j : Fin N) (z : V) (hz : z ∈ (R j).centers) :
      P (16 * δ) (128 * ρ * c) c z (R j).frame ⊆ F ⁻¹' ball (F (q j)) (3 * (r / 100)) := by
    have hh := (R j).rescaled_locality (by norm_num : (0 : ℝ) < 1 / 100) hρ hρ256 hc.le
      hsize hcr hw E hew (fun i =>
        show Y i ∩ C j ⊆ F ⁻¹' ball (F (q j)) ((1 / 100 : ℝ) * r) from by
          simpa only [div_eq_mul_inv, one_mul, mul_comm] using (inter_subset_right.trans (hball j))) z hz
    change P (16 * δ) (128 * ρ * c) c z (R j).frame ⊆
      F ⁻¹' ball (F (q j)) (3 * ((1 / 100 : ℝ) * r)) at hh
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hh
  have hlogδ : (Nat.log 2 n + 1 : ℝ) ≤ δ ^ (-(ζ / 2)) := by
    apply le_trans (by exact_mod_cast hlog ξ hξ (hξd.trans (min_le_right _ _)) n hnD)
    exact Real.rpow_le_rpow_of_nonpos hδ hδξ (by linarith)
  have hh := assemble_local_prism_packets_mapped hδ hδ1 (by positivity : 0 < r / 100)
    hρ.le hc.le (half_pos hζ).le x v Y C q y w F hY hC hball hdisj hcover hsep hlogδ R hlocality
  convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
