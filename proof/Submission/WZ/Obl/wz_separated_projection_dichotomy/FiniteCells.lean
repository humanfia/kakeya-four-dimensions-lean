-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.FiniteCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoarseCover

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- A finite family can be assigned to a separated internal net. -/
theorem exists_finite_cells (S : Finset Plane) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (T : Finset Plane) (f : Plane → Plane), T ⊆ S ∧
      (∀ y ∈ T, ∀ z ∈ T, y ≠ z → δ < dist y z) ∧
      (∀ x ∈ S, f x ∈ T ∧ dist x (f x) ≤ δ) := by
  classical
  obtain ⟨m, c, hcS, hcsep, hcov⟩ := exists_separated_cover S.finite_toSet.totallyBounded hδ
  let T := Finset.univ.image c
  have hcell : ∀ x ∈ S, ∃ i, dist x (c i) ≤ δ := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact ⟨i, hi⟩
  let f (x : Plane) := if hx : x ∈ S then c (Classical.choose (hcell x hx)) else x
  refine ⟨T, f, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact hcS i
  · intro y hy z hz hyz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact hcsep i j (fun hij => hyz (congrArg c hij))
  · intro x hx
    dsimp [f]
    rw [dif_pos hx]
    exact ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, Classical.choose_spec (hcell x hx)⟩

/-- The number of cells depends on the ambient scale and bound, independently
of the number or minimum separation of original points. -/
theorem exists_bounded_finite_cells (S : Finset Plane) {δ R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R) (hS : ∀ x ∈ S, ‖x‖ ≤ R) :
    ∃ (T : Finset Plane) (f : Plane → Plane), T ⊆ S ∧
      (∀ y ∈ T, ∀ z ∈ T, y ≠ z → δ < dist y z) ∧
      (∀ x ∈ S, f x ∈ T ∧ dist x (f x) ≤ δ) ∧
      (T.card : ℝ) ≤ (2 * R + 1) ^ 2 / δ ^ 2 := by
  obtain ⟨T, f, hTS, hsep, hnear⟩ := exists_finite_cells S hδ
  refine ⟨T, f, hTS, hsep, hnear, ?_⟩
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
  have hc := separated_card_mul_radius_sq_le hδ hR T 0
    (fun y hy => by simpa only [dist_zero_right] using hS y (hTS hy))
    (fun y hy z hz hyz => (hsep y hy z hz hyz).le)
  exact hc.trans (by gcongr)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
