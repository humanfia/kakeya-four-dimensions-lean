/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarUniformRangeHierarchy.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarUniformRangeHierarchy.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridHierarchy
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUniformRangeBlockFit

/-! The common original affine hierarchy at arbitrary designated power-range meshes. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts

theorem uniform_original_scalar_grid_hierarchy_between_powers_all_labels
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) :
    ∀ n : ℕ, ∃ B : ℕ → ℝ, (∀ k, 1 ≤ B k) ∧ (∀ k, K k ≤ B k) ∧ SubpowerBound N B ∧
      ∀ᶠ k in atTop, ∀ (Λ : Type*) [MeasurableSpace Λ], ∀ (D : ScalarMotion Λ) (ν : Measure Λ) [IsProbabilityMeasure ν]
        (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (S : ℝ → Set ℝ) (ζ : ℝ)
        (J : Fin n → ℕ) (hJ : ∀ i, 0 < J i),
        ScalarNormalHyp D ν E F S (K k) ζ d → 0 < ζ → (K k)⁻¹ ≤ (ν.prod volume).real E →
        (∀ i, N k ^ (-b) ≤ 1 / (J i : ℝ)) →
        (∀ i, 1 / (J i : ℝ) ≤ N k ^ (-a)) →
        (∀ i, ζ ≤ (1 / (J i : ℝ)) ^ 2) →
        Nonempty (ScalarGridHierarchy ν E F J hJ
          (fun i => (1 / (J i : ℝ)) ^ (1 / 4 : ℝ)) (B k)) := by
  intro n
  induction n with
  | zero =>
      let B : ℕ → ℝ := fun k => 8 * K k
      have hB : ∀ k, 1 ≤ B k := fun k => by dsimp [B]; linarith [hK k]
      have hKB : ∀ k, K k ≤ B k := fun k => by dsimp [B]; linarith [hK k]
      have hBsub : SubpowerBound N B :=
        subpower_mul (fun k => zero_lt_one.trans_le (hN k)) (fun _ => by norm_num)
          (fun k => zero_le_one.trans (hK k)) (subpower_const hNt 8) hsub
      refine ⟨B, hB, hKB, hBsub, ?_⟩
      filter_upwards [] with k
      intro Λ _ D ν _ E F S ζ J hJ h hζ hmass hlow hhigh hζH
      exact exists_initial_scalar_grid_hierarchy ν h.event_measurable h.unit_time
        (hK k) hmass F J hJ (fun i => (1 / (J i : ℝ)) ^ (1 / 4 : ℝ))
  | succ n ih =>
      obtain ⟨B, hB, hKB, hBsub, hprevious⟩ :=
        ih
      have h8B : ∀ k, 1 ≤ 8 * B k := fun k => by linarith [hB k]
      have h8Bsub : SubpowerBound N (fun k => 8 * B k) :=
        subpower_mul (fun k => zero_lt_one.trans_le (hN k)) (fun _ => by norm_num)
          (fun k => zero_le_one.trans (hB k)) (subpower_const hNt 8) hBsub
      obtain ⟨Q, hQ, hQsub, hlocal⟩ := uniform_subpower_original_scalar_block_fit_between_powers_all_labels
        N (fun k => 8 * B k) hN hNt h8B h8Bsub (show 0 < a / 4 by positivity) (show a / 4 ≤ b / 4 by linarith) hd0 hd
      let B' : ℕ → ℝ := fun k => scalarGridStageBound (B k) (Q k)
      have hB' : ∀ k, 1 ≤ B' k := fun k => (scalarGridStageBound_bounds (hB k) (hQ k)).1
      have hBB' : ∀ k, B k ≤ B' k := fun k => (scalarGridStageBound_bounds (hB k) (hQ k)).2.1
      have hB'sub : SubpowerBound N B' := by
        exact subpower_mul (fun k => zero_lt_one.trans_le (hN k))
          (fun k => by positivity) (fun k => zero_le_one.trans (hQ k))
          (subpower_mul (fun k => zero_lt_one.trans_le (hN k)) (fun _ => by norm_num)
            (fun k => sq_nonneg (B k)) (subpower_const hNt 10000)
            (subpower_pow hN (fun k => zero_le_one.trans (hB k)) hBsub 2)) hQsub
      refine ⟨B', hB', fun k => (hKB k).trans (hBB' k), hB'sub, ?_⟩
      filter_upwards [hprevious, hlocal] with k hpreviousk hlocalk
      intro Λ _ D ν _ E F S ζ J hJ h hζ hmass hlow hhigh hζH
      obtain ⟨G⟩ := hpreviousk Λ D ν E F S ζ (fun i => J i.succ) (fun i => hJ i.succ)
        h hζ hmass (fun i => hlow i.succ) (fun i => hhigh i.succ) (fun i => hζH i.succ)
      let H : ℝ := 1 / (J 0 : ℝ)
      have hJpos : (0 : ℝ) < J 0 := Nat.cast_pos.mpr (hJ 0)
      have hH : 0 < H := by dsimp [H]; positivity
      have hH1 : H ≤ 1 := by
        apply (div_le_iff₀ hJpos).mpr
        simpa using (show (1 : ℝ) ≤ J 0 from by exact_mod_cast (Nat.succ_le_iff.mpr (hJ 0) : 1 ≤ J 0))
      have hpLow : N k ^ (-(b / 4)) ≤ H ^ (1 / 4 : ℝ) := by
        calc
          _ = (N k ^ (-b)) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_mul (zero_le_one.trans (hN k))]
            congr 1
            ring
          _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (zero_le_one.trans (hN k)) _) (hlow 0) (by norm_num)
      have hpHigh : H ^ (1 / 4 : ℝ) ≤ N k ^ (-(a / 4)) := by
        calc
          _ ≤ (N k ^ (-a)) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hH.le (hhigh 0) (by norm_num)
          _ = _ := by
            rw [← Real.rpow_mul (zero_le_one.trans (hN k))]
            congr 1
            ring
      exact ScalarGridHierarchy.extend J hJ (fun i => (1 / (J i : ℝ)) ^ (1 / 4 : ℝ)) G h hζ
        (hKB k) (hB k) (hQ k) (fun i => Real.rpow_nonneg (by positivity) _)
        (Real.self_le_rpow_of_le_one hH.le hH1 (by norm_num)) (hζH 0)
        (hlocalk Λ (H ^ (1 / 4 : ℝ)) hpLow hpHigh)

theorem uniform_original_scalar_grid_hierarchy_between_powers {Λ : Type*} [MeasurableSpace Λ]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 ≤ d) (hd : d < 1) :
    ∀ n : ℕ, ∃ B : ℕ → ℝ, (∀ k, 1 ≤ B k) ∧ (∀ k, K k ≤ B k) ∧ SubpowerBound N B ∧
      ∀ᶠ k in atTop, ∀ (D : ScalarMotion Λ) (ν : Measure Λ) [IsProbabilityMeasure ν]
        (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (S : ℝ → Set ℝ) (ζ : ℝ)
        (J : Fin n → ℕ) (hJ : ∀ i, 0 < J i),
        ScalarNormalHyp D ν E F S (K k) ζ d → 0 < ζ → (K k)⁻¹ ≤ (ν.prod volume).real E →
        (∀ i, N k ^ (-b) ≤ 1 / (J i : ℝ)) →
        (∀ i, 1 / (J i : ℝ) ≤ N k ^ (-a)) →
        (∀ i, ζ ≤ (1 / (J i : ℝ)) ^ 2) →
        Nonempty (ScalarGridHierarchy ν E F J hJ
          (fun i => (1 / (J i : ℝ)) ^ (1 / 4 : ℝ)) (B k)) := by
  intro n
  obtain ⟨B, hB, hKB, hBsub, hgood⟩ := uniform_original_scalar_grid_hierarchy_between_powers_all_labels
    N K hN hNt hK hsub ha hab hd0 hd n
  refine ⟨B, hB, hKB, hBsub, ?_⟩
  filter_upwards [hgood] with k hk
  exact hk Λ

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
