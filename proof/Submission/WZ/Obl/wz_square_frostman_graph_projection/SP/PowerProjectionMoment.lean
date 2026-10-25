-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.PowerProjectionMoment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.IndexedDirections
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.ProjectionMoment
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.PowerFrostman

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem sum_indexed_power_projectionEnergy_le {I : Type*} [Fintype I] {f : I → Plane}
    {δ C D s γ : ℝ} {F : Finset Plane}
    (hF : ClosedFinitePowerFrostman δ C s F) (hf : IndexedFrostman δ D f)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C) (hD : 1 ≤ D) (hs : 0 < s)
    (hunit : ∀ i, ‖f i‖ = 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hprod : s * γ ≤ 1) :
    ∑ i, projectionEnergy F (f i) δ ≤
      8 * C * D * energyConstant γ * δ ^ (s * γ) * (Fintype.card I : ℝ) * (F.card : ℝ) ^ 2 := by
  have heq : ∑ i, projectionEnergy F (f i) δ =
      ∑ x : F, ∑ y : F,
        ((Finset.univ.filter (fun i => |inner ℝ (f i) ((x : Plane) - y)| ≤ 2 * δ)).card : ℝ) := by
    unfold projectionEnergy
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
      apply_ite, Nat.cast_one, Nat.cast_zero]
  rw [heq]
  calc ∑ x : F, ∑ y : F,
        ((Finset.univ.filter (fun i => |inner ℝ (f i) ((x : Plane) - y)| ≤ 2 * δ)).card : ℝ) ≤
        ∑ x : F, ∑ y : F,
          8 * D * δ ^ (s * γ) * (truncatedDistance δ x y) ^ (-(s * γ)) * (Fintype.card I : ℝ) := by
            apply Finset.sum_le_sum
            intro x hx
            apply Finset.sum_le_sum
            intro y hy
            exact hf.direction_collision_power hδ hδ1 hD hunit hprod x y
    _ = ∑ x : F, (8 * D * δ ^ (s * γ) * (Fintype.card I : ℝ)) *
        ∑ y : F, (truncatedDistance δ x y) ^ (-(s * γ)) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ ≤ ∑ _x : F, (8 * D * δ ^ (s * γ) * (Fintype.card I : ℝ)) *
        (C * (F.card : ℝ) * energyConstant γ) := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_left (hF.truncated_energy hδ hδ1 hC hs hγ hγ1 x) (by positivity)
    _ = _ := by simp; ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
