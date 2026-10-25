-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.IndexedMoment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.IndexedDirections
import Submission.WZ.Obl.wz_separated_projection_dichotomy.ProjectionMoment

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem sum_indexed_projectionEnergy_le {I : Type*} [Fintype I] {f : I → Plane}
    {δ C γ : ℝ} {F : Finset Plane}
    (hF : ClosedFiniteFrostman δ C F) (hf : IndexedFrostman δ C f)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C)
    (hunit : ∀ i, ‖f i‖ = 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    ∑ i, projectionEnergy F (f i) δ ≤
      8 * C ^ 2 * energyConstant γ * δ ^ γ * (Fintype.card I : ℝ) * (F.card : ℝ) ^ 2 := by
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
          8 * C * δ ^ γ * (truncatedDistance δ x y) ^ (-γ) * (Fintype.card I : ℝ) := by
            apply Finset.sum_le_sum
            intro x hx
            apply Finset.sum_le_sum
            intro y hy
            exact hf.direction_collision_power hδ hδ1 hC hunit hγ1.le x y
    _ = ∑ x : F, (8 * C * δ ^ γ * (Fintype.card I : ℝ)) *
        ∑ y : F, (truncatedDistance δ x y) ^ (-γ) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ ≤ ∑ _x : F, (8 * C * δ ^ γ * (Fintype.card I : ℝ)) *
        (C * (F.card : ℝ) * energyConstant γ) := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_left (hF.truncated_energy hδ hδ1 hC hγ hγ1 x) (by positivity)
    _ = _ := by simp; ring

end WangZahlLot.Obl.wz_separated_projection_dichotomy
