-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.GridIteratedSums.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.GridQuantization

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

/-- Rounding commutes with an iterated sum up to one mesh unit per summand. -/
theorem nsmul_grid_approximation {δ : ℝ} (hδ : 0 < δ) (B : Finset ℝ) (k : ℕ) :
    ∀ x ∈ k • B, ∃ z ∈ k • (B.image (realGridIndex δ)),
      dist x (δ * (z : ℝ)) ≤ (k : ℝ) * δ := by
  classical
  induction k with
  | zero =>
      intro x hx
      simp only [zero_nsmul, Finset.mem_zero] at hx
      subst x
      exact ⟨0, by simp, by simp⟩
  | succ k ih =>
      intro x hx
      rw [succ_nsmul] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨z, hz, hza⟩ := ih a ha
      refine ⟨z + realGridIndex δ b, ?_, ?_⟩
      · rw [succ_nsmul]
        exact Finset.add_mem_add hz (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
      · have hbδ : dist b (δ * (realGridIndex δ b : ℝ)) ≤ δ := by
          rw [Real.dist_eq, abs_of_nonneg (realGridIndex_error hδ b).1]
          exact (realGridIndex_error hδ b).2.le
        calc
          dist (a + b) (δ * ((z + realGridIndex δ b : ℤ) : ℝ)) =
              dist (a + b) (δ * (z : ℝ) + δ * (realGridIndex δ b : ℝ)) := by rw [Int.cast_add, mul_add]
          _ ≤ dist a (δ * (z : ℝ)) + dist b (δ * (realGridIndex δ b : ℝ)) := dist_add_add_le _ _ _ _
          _ ≤ (k : ℝ) * δ + δ := add_le_add hza hbδ
          _ = _ := by push_cast; ring

/-- The integer sum-difference set indexes a real cover with an absolute
linear loss in its radius. -/
theorem cover_of_grid_nsmul_sub_nsmul {δ : ℝ} (hδ : 0 < δ) (B : Finset ℝ) (k l : ℕ) :
    ∃ (m : ℕ) (cc : Fin m → ℝ), Covers (((k + l : ℕ) : ℝ) * δ)
      (↑(k • B - l • B) : Set ℝ) cc ∧
      m = (k • (B.image (realGridIndex δ)) - l • (B.image (realGridIndex δ))).card := by
  classical
  let D := k • (B.image (realGridIndex δ)) - l • (B.image (realGridIndex δ))
  let e := Fintype.equivFin D
  let cc (i : Fin (Fintype.card D)) := δ * ((e.symm i).1 : ℝ)
  refine ⟨Fintype.card D, cc, ?_, Fintype.card_coe _⟩
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
  obtain ⟨z, hz, hza⟩ := nsmul_grid_approximation hδ B k a ha
  obtain ⟨w, hw, hwb⟩ := nsmul_grid_approximation hδ B l b hb
  have hzw : z - w ∈ D := Finset.sub_mem_sub hz hw
  refine Set.mem_iUnion.mpr ⟨e ⟨z - w, hzw⟩, ?_⟩
  change dist (a - b) (δ * ((e.symm (e ⟨z - w, hzw⟩)).1 : ℝ)) ≤ _
  rw [Equiv.symm_apply_apply, Int.cast_sub, mul_sub]
  have hh := dist_sub_sub_le a b (δ * (z : ℝ)) (δ * (w : ℝ))
  push_cast
  linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
