-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NetEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NetEstimate.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641 commit 7652d3d, NetEstimate.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.RoundEstimate
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NetDensity

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (closedTube)

/-- The balanced intermediate net retains its whole-body fibres, and its small
fibre alternative forces density in the ambient shading. -/
theorem balanced_net_density_estimate_with_separation {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n d : ℕ) (I : Finset (Fin n))
        (U Y : Fin n → Set V) (Γ : Set V) (c : Fin n → V) (u : Fin n → Fin 3 → V)
        (a b Λ w M D τ : ℝ),
      I.Nonempty → (n : ℝ) ≤ δ ^ (-100 : ℝ) → 0 < d → 1 < Λ → (n : ℝ) < Λ ^ d →
      0 ≤ a → a ≤ b → 4 * δ ≤ b → b ≤ 1 / 1000000 →
      0 < w → 0 < M → 0 < τ → 6144 * δ ^ η ≤ D → MeasurableSet Γ →
      (∀ i ∈ I, Orthonormal ℝ (u i)) → (∀ i ∈ I, ‖c i‖ < 1 / 100) →
      (∀ i ∈ I, U i ⊆ prism a b (c i) (u i)) →
      (∀ i ∈ I, Y i ⊆ Γ ∩ prism a b (c i) (u i)) →
      (∀ i ∈ I, O (D * b ^ 2) ≤ μ (Y i)) →
      BodyConvexCount U w M → τ * M ≤ (I.card : ℝ) * w →
      ∃ (N q : ℕ) (k : Fin N → Fin n) (F : Fin N → Finset (Fin n)),
        0 < N ∧ 0 < q ∧ (∀ j, k j ∈ I) ∧ (∀ j, F j ⊆ I) ∧
        (∀ j, (F j).card = q) ∧ (∀ j j', j ≠ j' → Disjoint (F j) (F j')) ∧
        netConst * (I.card : ℝ) ≤ (d : ℝ) * Λ * N * q ∧
        (∀ j, ∀ i ∈ F j, U i ⊆ cTube b (c (k j)) (u (k j))) ∧
        (∀ j j', j ≠ j' → μ (cTube b (c (k j)) (u (k j)) ∩
          cTube b (c (k j')) (u (k j'))) ≤
          (1 / 2 : ℝ≥0∞) * μ (cTube b (c (k j)) (u (k j)))) ∧
        ((q : ℝ) * w ≤ M * (4 * b) ^ 2 →
          O (A * (netConst * τ / ((d : ℝ) * Λ)) * δ ^ ε * (4 * b) ^ (ω + σ) *
            (M * (4 * b) ^ 2 / ((q : ℝ) * w)) ^ (σ / 2)) ≤ μ Γ) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, HE⟩ :=
    saturated_round_estimate hσ hσhalf hω hE ε hε
  refine ⟨A, η, d₀, hA, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n d I U Y Γ c u a b Λ w M D τ hI hn hd hΛ hnΛ ha hab hδb hbsmall
    hw hM hτ hD hΓ hu hc hU hY hden hK hsat
  have hnet : 0 < netConst := netConst_pos
  have hD0 : 0 ≤ D := (by positivity : 0 ≤ 6144 * δ ^ η).trans hD
  have hb : 0 < b := (by positivity : 0 < 4 * δ).trans_le hδb
  obtain ⟨N, q, k, F, hN, hq, hk, hFI, hcard, hdisj, hret, hcover, hX⟩ :=
    balanced_prism_net I hI ha hab hb hbsmall hd hΛ hnΛ c u hu hc
  have hwhole : ∀ j, ∀ i ∈ F j, U i ⊆ cTube b (c (k j)) (u (k j)) :=
    fun j i hi => (hU i (hFI j hi)).trans (hcover j i hi)
  refine ⟨N, q, k, F, hN, hq, hk, hFI, hcard, hdisj, hret, hwhole, hX, ?_⟩
  intro hqmax
  let v : Fin N → V := fun j => axisDir (u (k j))
  let x : Fin N → V := fun j => c (k j) - (1 / 2 : ℝ) • v j
  let W : Fin N → Set V := fun j => closedTube (4 * b) (x j) (v j)
  let Z : Fin N → Set V := fun j => W j ∩ Γ
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hΛ0 : 0 < Λ := zero_lt_one.trans hΛ
  have hNn : N ≤ n := by
    have H : N * q ≤ n := by
      simpa using WangZahlLot.Obl.wz_affine_packet_counting_transfer.fiber_count
        F hcard hdisj Set.univ Set.univ (fun _ _ _ _ => Set.mem_univ _)
    exact (Nat.le_mul_of_pos_right N hq).trans H
  have hv (j) : ‖v j‖ = 1 := norm_axisDir (hu _ (hk j))
  have hball (j) : W j ⊆ ball (0 : V) 1 :=
    closed_net_carrier_subset_ball hb hbsmall (hu _ (hk j)) (hc _ (hk j))
  have hZden (j) : O (δ ^ η) * μ (W j) ≤ μ (Z j) := by
    have hcoef : δ ^ η ≤ D / 6144 := (le_div_iff₀ (by norm_num)).mpr (by nlinarith)
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl).trans
      (net_carrier_density ha hab hb hbsmall hD0
        (hu _ (hk j)) (hY _ (hk j)) (hden _ (hk j)))
  have hcount := balanced_carrier_convex_count hw hM.le (by positivity : 0 < 4 * b)
    hq x v F hcard hdisj hwhole hK
  have hMsat : (netConst * τ / ((d : ℝ) * Λ)) *
      (M * (4 * b) ^ 2 / ((q : ℝ) * w)) ≤ (N : ℝ) * (4 * b) ^ 2 := by
    have H : netConst * τ * M ≤ ((d : ℝ) * Λ) * ((N : ℝ) * q * w) := by
      calc
        _ = netConst * (τ * M) := by ring
        _ ≤ netConst * ((I.card : ℝ) * w) :=
          mul_le_mul_of_nonneg_left hsat netConst_pos.le
        _ = (netConst * (I.card : ℝ)) * w := by ring
        _ ≤ ((d : ℝ) * Λ * N * q) * w := mul_le_mul_of_nonneg_right hret hw.le
        _ = _ := by ring
    have H' : netConst * τ * M / ((d : ℝ) * Λ * q * w) ≤ (N : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [H]
    calc
      _ = (netConst * τ * M / ((d : ℝ) * Λ * q * w)) * (4 * b) ^ 2 := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right H' (sq_nonneg _)
  have H := HE δ hδ hδd N x v Z (4 * b) (M * (4 * b) ^ 2 / ((q : ℝ) * w))
    (netConst * τ / ((d : ℝ) * Λ)) hN ((Nat.cast_le.mpr hNn).trans hn)
    (by linarith) (by linarith) ((le_div_iff₀ (by positivity)).mpr (by simpa using hqmax))
    (by positivity) hv hball hX
    (fun j => isClosed_closure.measurableSet.inter hΓ) (fun _ => inter_subset_left) hZden hcount hMsat
  exact H.trans (measure_mono (iUnion_subset fun _ => inter_subset_right))

/-- The balanced intermediate net retains its whole-body fibres, and its small
fibre alternative forces density in the ambient shading. -/
theorem balanced_net_density_estimate {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n d : ℕ) (I : Finset (Fin n))
        (U Y : Fin n → Set V) (Γ : Set V) (c : Fin n → V) (u : Fin n → Fin 3 → V)
        (a b Λ w M D τ : ℝ),
      I.Nonempty → (n : ℝ) ≤ δ ^ (-100 : ℝ) → 0 < d → 1 < Λ → (n : ℝ) < Λ ^ d →
      0 ≤ a → a ≤ b → 4 * δ ≤ b → b ≤ 1 / 1000000 →
      0 < w → 0 < M → 0 < τ → 6144 * δ ^ η ≤ D → MeasurableSet Γ →
      (∀ i ∈ I, Orthonormal ℝ (u i)) → (∀ i ∈ I, ‖c i‖ < 1 / 100) →
      (∀ i ∈ I, U i ⊆ prism a b (c i) (u i)) →
      (∀ i ∈ I, Y i ⊆ Γ ∩ prism a b (c i) (u i)) →
      (∀ i ∈ I, O (D * b ^ 2) ≤ μ (Y i)) →
      BodyConvexCount U w M → τ * M ≤ (I.card : ℝ) * w →
      ∃ (N q : ℕ) (k : Fin N → Fin n) (F : Fin N → Finset (Fin n)),
        0 < N ∧ 0 < q ∧ (∀ j, k j ∈ I) ∧ (∀ j, F j ⊆ I) ∧
        (∀ j, (F j).card = q) ∧ (∀ j j', j ≠ j' → Disjoint (F j) (F j')) ∧
        netConst * (I.card : ℝ) ≤ (d : ℝ) * Λ * N * q ∧
        (∀ j, ∀ i ∈ F j, U i ⊆ cTube b (c (k j)) (u (k j))) ∧
        ((q : ℝ) * w ≤ M * (4 * b) ^ 2 →
          O (A * (netConst * τ / ((d : ℝ) * Λ)) * δ ^ ε * (4 * b) ^ (ω + σ) *
            (M * (4 * b) ^ 2 / ((q : ℝ) * w)) ^ (σ / 2)) ≤ μ Γ) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ :=
    balanced_net_density_estimate_with_separation hσ hσhalf hω hE ε hε
  refine ⟨A, η, d₀, hA, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n d I U Y Γ c u a b Λ w M D τ hI hn hd hΛ hnΛ ha hab hδb hbsmall
    hw hM hτ hD hΓ hu hc hU hY hden hK hsat
  obtain ⟨N, q, k, F, hN, hq, hk, hFI, hcard, hdisj, hret, hwhole, _, hlow⟩ :=
    H δ hδ hδd n d I U Y Γ c u a b Λ w M D τ hI hn hd hΛ hnΛ ha hab hδb hbsmall
      hw hM hτ hD hΓ hu hc hU hY hden hK hsat
  exact ⟨N, q, k, F, hN, hq, hk, hFI, hcard, hdisj, hret, hwhole, hlow⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
