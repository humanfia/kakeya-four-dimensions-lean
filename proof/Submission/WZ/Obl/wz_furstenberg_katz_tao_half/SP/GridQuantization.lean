-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.GridQuantization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.Basic

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped BigOperators

noncomputable def realGridIndex (δ x : ℝ) : ℤ := ⌊x / δ⌋

theorem realGridIndex_error {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 ≤ x - δ * (realGridIndex δ x : ℝ) ∧ x - δ * (realGridIndex δ x : ℝ) < δ := by
  have hlo := mul_le_mul_of_nonneg_left (Int.floor_le (x / δ)) hδ.le
  have hhi := mul_lt_mul_of_pos_left (Int.lt_floor_add_one (x / δ)) hδ
  rw [mul_div_cancel₀ _ hδ.ne'] at hlo hhi
  dsimp [realGridIndex]
  constructor <;> nlinarith

theorem realGridIndex_injective {δ : ℝ} (hδ : 0 < δ) {A : Finset ℝ}
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b) :
    Set.InjOn (realGridIndex δ) (↑A : Set ℝ) := by
  intro a ha b hb heq
  by_contra hab
  have hdist := hsep a ha b hb hab
  have hea := realGridIndex_error hδ a
  have heb := realGridIndex_error hδ b
  rw [heq] at hea
  rw [Real.dist_eq] at hdist
  have habs : |a - b| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
  exact (not_lt_of_ge hdist) habs

theorem realGridIndex_sum_mem {δ a b c : ℝ} (hδ : 0 < δ)
    (hc : dist (a + b) c ≤ δ) :
    realGridIndex δ a + realGridIndex δ b ∈
      Finset.Icc (realGridIndex δ c - 3) (realGridIndex δ c + 2) := by
  have hea := realGridIndex_error hδ a
  have heb := realGridIndex_error hδ b
  have hec := realGridIndex_error hδ c
  have hc' := abs_le.mp (show |a + b - c| ≤ δ by simpa only [Real.dist_eq] using hc)
  have hlo : (realGridIndex δ c : ℝ) - 3 ≤
      (realGridIndex δ a : ℝ) + (realGridIndex δ b : ℝ) := by
    nlinarith
  have hhi : (realGridIndex δ a : ℝ) + (realGridIndex δ b : ℝ) ≤
      (realGridIndex δ c : ℝ) + 2 := by
    nlinarith
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

theorem realGridIndex_sub_error {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    dist (a - b) (δ * ((realGridIndex δ a - realGridIndex δ b : ℤ) : ℝ)) ≤ δ := by
  have hea := realGridIndex_error hδ a
  have heb := realGridIndex_error hδ b
  rw [Real.dist_eq, Int.cast_sub]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- A cover of a real sumset gives at most six integer sums per cover ball
when both summands are rounded down to the same grid. -/
theorem grid_sums_of_cover {δ : ℝ} (hδ : 0 < δ) (R : Finset (ℝ × ℝ))
    {m : ℕ} (cc : Fin m → ℝ)
    (hcov : Covers δ ((fun p : ℝ × ℝ => p.1 + p.2) '' (↑R : Set (ℝ × ℝ))) cc) :
    ∃ S : Finset ℤ, (S.card : ℝ) ≤ 6 * (m : ℝ) ∧
      ∀ p ∈ R, realGridIndex δ p.1 + realGridIndex δ p.2 ∈ S := by
  classical
  let D (i : Fin m) := Finset.Icc (realGridIndex δ (cc i) - 3) (realGridIndex δ (cc i) + 2)
  let S := Finset.univ.biUnion D
  have hcard (i : Fin m) : (D i).card = 6 := by
    simp only [D, Int.card_Icc]
    omega
  refine ⟨S, ?_, ?_⟩
  · have h := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin m))) (t := D)
    have hh : S.card ≤ 6 * m := by simpa only [hcard, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, Nat.mul_comm] using h
    exact_mod_cast hh
  · intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ⟨p, hp, rfl⟩)
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ _, realGridIndex_sum_mem hδ hi⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
