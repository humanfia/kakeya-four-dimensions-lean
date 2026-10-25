-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.ProjectionMoment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.DirectionCounts
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Collision

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable def projectionEnergy (F : Finset Plane) (θ : Plane) (δ : ℝ) : ℝ :=
  ∑ x : F, ∑ y : F, if |inner ℝ θ ((x : Plane) - y)| ≤ 2 * δ then 1 else 0

theorem projectionEnergy_nonneg (F : Finset Plane) (θ : Plane) (δ : ℝ) :
    0 ≤ projectionEnergy F θ δ := by unfold projectionEnergy; positivity

theorem projectionEnergy_eq_closePairs (F : Finset Plane) (θ : Plane) (δ : ℝ) :
    projectionEnergy F θ δ = ((closePairs (fun x : F => inner ℝ θ (x : Plane)) (2 * δ)).card : ℝ) := by
  simp only [projectionEnergy, closePairs, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type, Real.dist_eq, inner_sub_right, Nat.cast_sum,
    apply_ite, Nat.cast_one, Nat.cast_zero]

theorem sum_projectionEnergy_eq (F Λ : Finset Plane) (δ : ℝ) :
    ∑ θ ∈ Λ, projectionEnergy F θ δ =
      ∑ x : F, ∑ y : F, ((Λ.filter (fun θ => |inner ℝ θ ((x : Plane) - y)| ≤ 2 * δ)).card : ℝ) := by
  unfold projectionEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    apply_ite, Nat.cast_one, Nat.cast_zero]

/-- The total collision count over all projection directions, with every
power below one and a constant depending only on that power. -/
theorem sum_projectionEnergy_le {δ C γ : ℝ} {F Λ : Finset Plane}
    (hF : ClosedFiniteFrostman δ C F) (hΛ : ClosedFiniteFrostman δ C Λ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C)
    (hunit : ∀ θ ∈ Λ, ‖θ‖ = 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    ∑ θ ∈ Λ, projectionEnergy F θ δ ≤
      8 * C ^ 2 * energyConstant γ * δ ^ γ * (Λ.card : ℝ) * (F.card : ℝ) ^ 2 := by
  rw [sum_projectionEnergy_eq]
  calc ∑ x : F, ∑ y : F,
        ((Λ.filter (fun θ => |inner ℝ θ ((x : Plane) - y)| ≤ 2 * δ)).card : ℝ) ≤
        ∑ x : F, ∑ y : F,
          8 * C * δ ^ γ * (truncatedDistance δ x y) ^ (-γ) * (Λ.card : ℝ) := by
            apply Finset.sum_le_sum
            intro x hx
            apply Finset.sum_le_sum
            intro y hy
            exact hΛ.direction_collision_power hδ hδ1 hC hunit hγ1.le x y
    _ = ∑ x : F, (8 * C * δ ^ γ * (Λ.card : ℝ)) *
        ∑ y : F, (truncatedDistance δ x y) ^ (-γ) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ ≤ ∑ _x : F, (8 * C * δ ^ γ * (Λ.card : ℝ)) *
        (C * (F.card : ℝ) * energyConstant γ) := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_left (hF.truncated_energy hδ hδ1 hC hγ hγ1 x) (by positivity)
    _ = _ := by simp; ring

end WangZahlLot.Obl.wz_separated_projection_dichotomy
