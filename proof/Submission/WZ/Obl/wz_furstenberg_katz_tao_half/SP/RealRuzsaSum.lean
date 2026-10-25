-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.RealRuzsaSum.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.MixedPlunnecke
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RealCoverAlgebra

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

/-- Centering a rounded sum halfway across its two-cell error interval
keeps the cover at the original radius. -/
theorem cover_of_grid_sum {δ : ℝ} (hδ : 0 < δ) (A B : Finset ℝ) :
    ∃ (m : ℕ) (cc : Fin m → ℝ), Covers δ (↑(A + B) : Set ℝ) cc ∧
      m = (A.image (realGridIndex δ) + B.image (realGridIndex δ)).card := by
  classical
  let D := A.image (realGridIndex δ) + B.image (realGridIndex δ)
  let e := Fintype.equivFin D
  let cc : Fin (Fintype.card D) → ℝ := fun i => δ * (((e.symm i).val : ℝ) + 1)
  refine ⟨Fintype.card D, cc, ?_, Fintype.card_coe _⟩
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
  have hab : realGridIndex δ a + realGridIndex δ b ∈ D := Finset.add_mem_add
    (Finset.mem_image.mpr ⟨a, ha, rfl⟩) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  refine Set.mem_iUnion.mpr ⟨e ⟨_, hab⟩, ?_⟩
  change dist (a + b) (δ * (((e.symm (e ⟨_, hab⟩)).val : ℝ) + 1)) ≤ δ
  rw [Equiv.symm_apply_apply, Real.dist_eq, Int.cast_add]
  have hA := realGridIndex_error hδ a
  have hB := realGridIndex_error hδ b
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- The additive form of Ruzsa's triangle inequality for real covers.
The middle set is measured by its occupied grid cells. -/
theorem real_ruzsa_sum {δ : ℝ} (hδ : 0 < δ) (A B C : Finset ℝ)
    {m n : ℕ} (ca : Fin m → ℝ) (cc : Fin n → ℝ)
    (hAB : Covers δ (↑(A + B) : Set ℝ) ca)
    (hBC : Covers δ (↑(B + C) : Set ℝ) cc) :
    ∃ (k : ℕ) (centers : Fin k → ℝ), Covers δ (↑(A + C) : Set ℝ) centers ∧
      (k : ℝ) * ((B.image (realGridIndex δ)).card : ℝ) ≤ 36 * (m : ℝ) * (n : ℝ) := by
  classical
  obtain ⟨k, centers, hcov, hk⟩ := cover_of_grid_sum hδ A C
  refine ⟨k, centers, hcov, ?_⟩
  have ht := Finset.ruzsa_triangle_inequality_add_add_add
    (A.image (realGridIndex δ)) (B.image (realGridIndex δ)) (C.image (realGridIndex δ))
  have ht' : (k : ℝ) * ((B.image (realGridIndex δ)).card : ℝ) ≤
      ((A.image (realGridIndex δ) + B.image (realGridIndex δ)).card : ℝ) *
        ((B.image (realGridIndex δ) + C.image (realGridIndex δ)).card : ℝ) := by
    rw [hk]
    exact_mod_cast ht
  have ha := grid_mixed_sum_card_le hδ A B ca hAB
  have hc := grid_mixed_sum_card_le hδ B C cc hBC
  calc
    _ ≤ ((A.image (realGridIndex δ) + B.image (realGridIndex δ)).card : ℝ) *
        ((B.image (realGridIndex δ) + C.image (realGridIndex δ)).card : ℝ) := ht'
    _ ≤ (6 * (m : ℝ)) * (6 * (n : ℝ)) :=
      mul_le_mul ha hc (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
