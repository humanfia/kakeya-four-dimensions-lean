-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_robust_cluster_estimate.Counts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Geometry

namespace WangZahlLot.Obl.wz_affine_robust_cluster_estimate
open Set
noncomputable section

/-- Recenter a nonempty cap at one of its directions and pull it back. -/
theorem cap_count_transfer {n : ℕ} (S : Set (Fin n)) (v v' : Fin n → E)
    (hv : ∀ i, ‖v i‖ = 1) {A b r : ℝ} (hA : 0 ≤ A) (hr : 2 * A * b ≤ r)
    (hd : ∀ i j, pd (v i) (v j) ≤ A * pd (v' i) (v' j))
    (hc : ∀ u : E, ‖u‖ = 1 →
      ({i | i ∈ S ∧ pd (v i) u ≤ r}.ncard : ℝ) ≤ (1 / 2 : ℝ) * (S.ncard : ℝ))
    (u : E) :
    ({i | i ∈ S ∧ pd (v' i) u ≤ b}.ncard : ℝ) ≤ (1 / 2 : ℝ) * (S.ncard : ℝ) := by
  classical
  let Q : Set (Fin n) := {i | i ∈ S ∧ pd (v' i) u ≤ b}
  rcases Q.eq_empty_or_nonempty with hQ | ⟨j, hj⟩
  · change (Q.ncard : ℝ) ≤ _
    rw [hQ, ncard_empty, Nat.cast_zero]
    positivity
  · have hsub : Q ⊆ {i | i ∈ S ∧ pd (v i) (v j) ≤ r} := by
      intro i hi
      refine ⟨hi.1, (hd i j).trans ?_⟩
      have ht := pd_triangle (v' i) u (v' j)
      rw [pd_symm u (v' j)] at ht
      have hle : pd (v' i) (v' j) ≤ 2 * b := by linarith [hi.2, hj.2]
      exact (mul_le_mul_of_nonneg_left hle hA).trans (by nlinarith only [hr])
    exact (Nat.cast_le.mpr (ncard_mono hsub)).trans (hc (v j) (hv j))

/-- A fixed small relative angular radius suffices for the half-cap condition. -/
theorem exists_robust_radius {C β : ℝ} (hC : 1 ≤ C) (hβ : 0 < β) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ C * ρ ^ β ≤ 1 / 2 := by
  have hC0 : 0 < C := by linarith
  let ρ : ℝ := (1 / (2 * C)) ^ (1 / β)
  have hbase : 0 < 1 / (2 * C) := by positivity
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hbase _
  refine ⟨ρ, hρ, ?_, ?_⟩
  · exact Real.rpow_le_one hbase.le (by rw [div_le_one (by positivity)]; linarith) (by positivity)
  · have he : ρ ^ β = 1 / (2 * C) := by
      dsimp [ρ]
      rw [← Real.rpow_mul hbase.le, one_div_mul_cancel hβ.ne', Real.rpow_one]
    rw [he]
    field_simp
    norm_num

end
end WangZahlLot.Obl.wz_affine_robust_cluster_estimate
