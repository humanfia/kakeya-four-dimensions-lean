-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.InnerTubePacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/InnerTubePacking.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.WeightedSelection
import Submission.WZ.Obl.wz_separated_cover_refinement.Covers
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry
import Submission.WZ.Obl.wz_convex_container_tube_packing.Packing
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyCounts

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyPacking)
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate enumerate_mem enumerate_injective)

noncomputable section

/-- Bodies containing unit tubes inherit square-root packing when their
large-overlap relation has bounded degree. -/
theorem body_packing_of_inner_tubes {r : ℝ} (hr : 0 < r) {n K : ℕ} (hK : 0 < K)
    (U : Fin n → Set V) (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (hTU : ∀ i, T r (x i) (v i) ⊆ U i)
    (hdegree : ∀ i, (Finset.univ.filter fun j => O (r ^ 2 / 2) < μ (U i ∩ U j)).card ≤ K) :
    BodyPacking U (r ^ 2) (1000 * Real.sqrt K) := by
  classical
  let R : Fin n → Fin n → Prop := fun i j => O (r ^ 2 / 2) < μ (U i ∩ U j)
  have hRself (i : Fin n) : R i i := by
    have hh := (WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hr (x i) (v i)
      (hv i)).trans (measure_mono (hTU i))
    change O (r ^ 2 / 2) < μ (U i ∩ U i)
    rw [inter_self]
    apply lt_of_lt_of_le ?_ hh
    exact (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hr)).mpr (by nlinarith [sq_pos_of_pos hr])
  have hRsymm {i j : Fin n} (h : R i j) : R j i := by
    simpa only [R, inter_comm] using h
  intro Q hconv
  by_cases hQ : μ Q = ⊤
  · simp [hQ, Real.sqrt_pos.mpr (Nat.cast_pos.mpr hK)]
  let F := Finset.univ.filter fun i => U i ⊆ Q
  obtain ⟨S, hSF, hsep, hcard⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.weighted_separated_subfamily
      R hRself hRsymm K hdegree (fun _ => (1 : ENNReal)) F
  have hFS : (F.card : ℝ) ≤ (K : ℝ) * S.card := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hcard
    exact_mod_cast hcard
  have hTubeSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      μ (T r (x i) (v i) ∩ T r (x j) (v j)) ≤ (1 / 2 : ENNReal) * μ (T r (x i) (v i)) := by
    intro i hi j hj hij
    calc
      _ ≤ μ (U i ∩ U j) := measure_mono (inter_subset_inter (hTU i) (hTU j))
      _ ≤ O (r ^ 2 / 2) := le_of_not_gt (hsep i hi j hj hij)
      _ = (1 / 2 : ENNReal) * O (r ^ 2) := by
        change ENNReal.ofReal (r ^ 2 / 2) = (1 / 2 : ENNReal) * ENNReal.ofReal (r ^ 2)
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
        rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
      _ ≤ _ := mul_le_mul' le_rfl
        (WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hr (x i) (v i) (hv i))
  have hpack := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hr
    (fun j => x (enumerate S j)) (fun j => v (enumerate S j)) hQ
    (fun j => hv (enumerate S j))
    (fun j => (hTU (enumerate S j)).trans (Finset.mem_filter.mp (hSF (enumerate_mem S j))).2)
    (fun i j hij => hTubeSep _ (enumerate_mem S i) _ (enumerate_mem S j)
      ((enumerate_injective S).ne hij))
  have hraw := ENNReal.toReal_mono (by finiteness) hpack
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (S.card : ℝ) * r ^ 4),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1000000)] at hraw
  have hcardF : F.card = Set.ncard {i | U i ⊆ Q} := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [F]
  have hbound : (F.card : ℝ) * r ^ 4 ≤ (1000000 * K) * (μ Q).toReal ^ 2 := by
    calc
      _ ≤ ((K : ℝ) * S.card) * r ^ 4 := mul_le_mul_of_nonneg_right hFS (by positivity)
      _ = (K : ℝ) * ((S.card : ℝ) * r ^ 4) := by ring
      _ ≤ (K : ℝ) * (1000000 * (μ Q).toReal ^ 2) :=
        mul_le_mul_of_nonneg_left hraw (Nat.cast_nonneg K)
      _ = _ := by ring
  have hroot : Real.sqrt (F.card : ℝ) * r ^ 2 ≤
      (1000 * Real.sqrt K) * (μ Q).toReal := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
    nlinarith only [hbound]
  change O (Real.sqrt (Set.ncard {i | U i ⊆ Q} : ℝ) * r ^ 2) ≤
    O (1000 * Real.sqrt K) * μ Q
  rw [← ENNReal.ofReal_toReal hQ, ← ENNReal.ofReal_mul (by positivity)]
  rw [hcardF] at hroot
  exact ENNReal.ofReal_le_ofReal hroot

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
