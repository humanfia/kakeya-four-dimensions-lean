-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_cluster_slab_filling.CoreSteps.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Volume
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Survival

/-!
The global steps of the proof of `WangZahlLot.wz_flat_cluster_slab_filling`: regularizing the
flat-cluster shadings at one scale, and keeping the tubes whose surviving shading is heavy.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_flat_cluster_slab_filling

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

/-- Step (i): drop the light shadings and replace each remaining one by a half-mass
subshading that is regular at the scale `L` (WZ Lemma 5.9, lib o095). -/
lemma regularize {n : ℕ} {δ lam L A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 ≤ lam)
    (hL : 0 < L) (hA : 0 ≤ A)
    (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1) (G : Finset (Fin n))
    (Z₁ : Fin n → Set Space) (hZ₁m : ∀ i, MeasurableSet (Z₁ i))
    (hZ₁T : ∀ i, Z₁ i ⊆ Tube δ (x i) (v i))
    (hmass : ENNReal.ofReal (A + 384 * lam * δ ^ 2 * n) ≤ ∑ i ∈ G, volume (Z₁ i)) :
    ∃ (G2 : Finset (Fin n)) (Z2 : Fin n → Set Space), G2 ⊆ G ∧
      (∀ i, MeasurableSet (Z2 i)) ∧ (∀ i, Z2 i ⊆ Z₁ i) ∧
      ENNReal.ofReal (A / 2) ≤ ∑ i ∈ G2, volume (Z2 i) ∧
      ∀ i, ∀ p ∈ Z2 i, ENNReal.ofReal (lam / 16000) * volume (Tube δ (x i) (v i) ∩ ball p L) ≤
        volume (Z2 i ∩ ball p L) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (384 * lam * δ ^ 2) with hc
  set G2 := G.filter (fun i => c ≤ volume (Z₁ i)) with hG2
  have hex : ∀ i, ∃ Z : Set Space, MeasurableSet Z ∧ Z ⊆ Z₁ i ∧
      (i ∈ G2 → (1 / 2 : ℝ≥0∞) * volume (Z₁ i) ≤ volume Z) ∧
      ∀ p ∈ Z, ENNReal.ofReal (lam / 16000) * volume (Tube δ (x i) (v i) ∩ ball p L) ≤
        volume (Z ∩ ball p L) := by
    intro i
    by_cases hi : i ∈ G2
    · have hdense : ENNReal.ofReal lam * volume (Tube δ (x i) (v i)) ≤ volume (Z₁ i) := by
        calc ENNReal.ofReal lam * volume (Tube δ (x i) (v i))
            ≤ ENNReal.ofReal lam * ENNReal.ofReal (384 * δ ^ 2) := by
              gcongr
              exact tube_volume_le hδ hδ1 (x i) (v i) (hv i)
          _ = c := by
              rw [hc, ← ENNReal.ofReal_mul hlam]; ring_nf
          _ ≤ volume (Z₁ i) := (Finset.mem_filter.1 hi).2
      obtain ⟨Z, hZm, hZY, hhalf, hreg⟩ :=
        WangZahlLot.Obl.wz_clustered_cover_volume_gain.convex_regular_subshading_finite
          (tube_convex δ (x i) (v i)) (tube_measurable δ (x i) (v i))
          (tube_totallyBounded δ (x i) (v i)) (tube_volume_ne_top δ (x i) (v i)) (hZ₁m i)
          (hZ₁T i) hlam hdense (by norm_num : 0 < (1 : ℕ)) (fun _ => L) (fun _ => hL)
      exact ⟨Z, hZm, hZY, fun _ => hhalf, fun p hp => by simpa using hreg p hp 0⟩
    · exact ⟨∅, MeasurableSet.empty, Set.empty_subset _, fun h => absurd h hi,
        fun p hp => absurd hp (Set.notMem_empty p)⟩
  choose Z2 hZ2m hZ2sub hZ2half hZ2reg using hex
  refine ⟨G2, Z2, Finset.filter_subset _ _, hZ2m, hZ2sub, ?_, hZ2reg⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not G (fun i => c ≤ volume (Z₁ i))
    (fun i => volume (Z₁ i))
  have hlight : ∑ i ∈ G.filter (fun i => ¬ c ≤ volume (Z₁ i)), volume (Z₁ i) ≤
      ENNReal.ofReal (384 * lam * δ ^ 2 * n) := by
    calc _ ≤ (G.filter (fun i => ¬ c ≤ volume (Z₁ i))).card • c :=
          Finset.sum_le_card_nsmul _ _ _
            (fun i hi => le_of_lt (not_le.1 (Finset.mem_filter.1 hi).2))
      _ ≤ n • c := by
          gcongr
          exact card_finset_fin_le _
      _ = ENNReal.ofReal (384 * lam * δ ^ 2 * n) := by
          rw [ENNReal.ofReal_mul' (Nat.cast_nonneg n), ENNReal.ofReal_natCast, nsmul_eq_mul, hc,
            mul_comm]
  have hheavy : ENNReal.ofReal A ≤ ∑ i ∈ G2, volume (Z₁ i) := by
    have h1 : ENNReal.ofReal A + ENNReal.ofReal (384 * lam * δ ^ 2 * n) ≤
        ∑ i ∈ G2, volume (Z₁ i) + ENNReal.ofReal (384 * lam * δ ^ 2 * n) := by
      rw [← ENNReal.ofReal_add hA (by positivity)]
      calc _ ≤ ∑ i ∈ G, volume (Z₁ i) := hmass
        _ = _ := hsplit.symm
        _ ≤ _ := add_le_add le_rfl hlight
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1
  calc ENNReal.ofReal (A / 2) = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal A := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat,
          ENNReal.div_eq_inv_mul, one_div]
    _ ≤ (1 / 2 : ℝ≥0∞) * ∑ i ∈ G2, volume (Z₁ i) := by gcongr
    _ = ∑ i ∈ G2, (1 / 2 : ℝ≥0∞) * volume (Z₁ i) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ G2, volume (Z2 i) := Finset.sum_le_sum (fun i hi => hZ2half i hi)

/-- Steps (ii)-(iii): after deleting the non-surviving points (threshold `s`), many tubes keep
a heavy surviving shading. -/
lemma survive_heavy {n N : ℕ} {s B A t : ℝ} (hs : 0 ≤ s) (hB : 0 < B) (ht : 0 ≤ t)
    (S G2 : Finset (Fin n)) (f : Fin n → Fin N) (Z Z2 : Fin n → Set Space)
    (hZm : ∀ j, MeasurableSet (Z j)) (hZ2m : ∀ j, MeasurableSet (Z2 j))
    (hZB : ∀ j ∈ S, volume (Z j) ≤ ENNReal.ofReal B)
    (hZ2B : ∀ j ∈ G2, volume (Z2 j) ≤ ENNReal.ofReal B)
    (hmass : ENNReal.ofReal A ≤ ∑ i ∈ G2, volume (Z2 i)) :
    A - s * B * n - n * t ≤
      B * ((G2.filter fun i => ENNReal.ofReal t ≤
        volume (Z2 i ∩ survivors S G2 f Z Z2 s i)).card : ℝ) := by
  have hloss := survival_loss S G2 f Z Z2 hZm hZ2m hs
  have hSmass : ∑ j ∈ S, volume (Z j) ≤ ENNReal.ofReal (B * n) := by
    calc ∑ j ∈ S, volume (Z j) ≤ S.card • ENNReal.ofReal B := Finset.sum_le_card_nsmul _ _ _ hZB
      _ ≤ n • ENNReal.ofReal B := by
          gcongr
          exact card_finset_fin_le _
      _ = ENNReal.ofReal (B * n) := by
          rw [nsmul_eq_mul, ENNReal.ofReal_mul hB.le, ENNReal.ofReal_natCast, mul_comm]
  have hloss' : ∑ i ∈ G2, volume (Z2 i \ survivors S G2 f Z Z2 s i) ≤
      ENNReal.ofReal (s * B * n) := by
    calc _ ≤ ENNReal.ofReal s * ∑ j ∈ S, volume (Z j) := hloss
      _ ≤ ENNReal.ofReal s * ENNReal.ofReal (B * n) := by gcongr
      _ = ENNReal.ofReal (s * B * n) := by rw [← ENNReal.ofReal_mul hs, mul_assoc]
  have hsplit : ∑ i ∈ G2, volume (Z2 i) ≤
      ∑ i ∈ G2, volume (Z2 i ∩ survivors S G2 f Z Z2 s i) +
        ∑ i ∈ G2, volume (Z2 i \ survivors S G2 f Z Z2 s i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => measure_le_inter_add_sdiff _ _ _)
  have hA' : ENNReal.ofReal (A - s * B * n) ≤
      ∑ i ∈ G2, volume (Z2 i ∩ survivors S G2 f Z Z2 s i) := by
    by_cases hpos : A - s * B * n ≤ 0
    · rw [ENNReal.ofReal_of_nonpos hpos]; exact zero_le
    · push Not at hpos
      have h1 : ENNReal.ofReal (A - s * B * n) + ENNReal.ofReal (s * B * n) ≤
          ∑ i ∈ G2, volume (Z2 i ∩ survivors S G2 f Z Z2 s i) + ENNReal.ofReal (s * B * n) := by
        rw [← ENNReal.ofReal_add hpos.le (by positivity)]
        calc ENNReal.ofReal (A - s * B * n + s * B * n) = ENNReal.ofReal A := by ring_nf
          _ ≤ _ := hmass
          _ ≤ _ := hsplit
          _ ≤ _ := add_le_add le_rfl hloss'
      exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1
  have hmh := many_heavy G2 (fun i => volume (Z2 i ∩ survivors S G2 f Z Z2 s i)) hB ht
    (fun i hi => (measure_mono Set.inter_subset_left).trans (hZ2B i hi)) hA'
  have hcard : (G2.card : ℝ) ≤ n := by
    exact_mod_cast card_finset_fin_le G2
  have : (G2.card : ℝ) * t ≤ n * t := mul_le_mul_of_nonneg_right hcard ht
  linarith

end WangZahlLot.Obl.wz_flat_cluster_slab_filling

end
