-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.DenseSlopes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.SlopeDirections

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

theorem perturbed_grid_frostman {δ : ℝ} {N : ℕ} (hδ : 0 < δ) (hN : 0 < N)
    (hδN : 1 ≤ δ * (N : ℝ)) (t : Fin N → ℝ)
    (hclose : ∀ i, dist (t i) ((i : ℕ) / (N : ℝ)) ≤ δ) :
    IndexedRealFrostman δ 5 t := by
  classical
  intro x r hr
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let S := Finset.univ.filter (fun i => dist (t i) x ≤ r)
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have ha : a ∈ S := S.min'_mem hS
    have hb : b ∈ S := S.max'_mem hS
    have hab : a ≤ b := S.min'_le_max' hS
    have hsub : S ⊆ Finset.Icc a b := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨S.min'_le i hi, S.le_max' i hi⟩
    have hcard : (S.card : ℝ) ≤ (b : ℕ) + 1 - (a : ℕ) := by
      have hh := Finset.card_le_card hsub
      rw [Fin.card_Icc] at hh
      have hle : (a : ℕ) ≤ (b : ℕ) + 1 := by exact Nat.le_succ_of_le hab
      exact_mod_cast hh
    have hga : dist ((a : ℕ) / (N : ℝ)) x ≤ δ + r := by
      calc dist ((a : ℕ) / (N : ℝ)) x ≤ dist ((a : ℕ) / (N : ℝ)) (t a) + dist (t a) x :=
          dist_triangle _ _ _
        _ ≤ δ + r := add_le_add (by simpa only [dist_comm] using hclose a) (Finset.mem_filter.mp ha).2
    have hgb : dist ((b : ℕ) / (N : ℝ)) x ≤ δ + r := by
      calc dist ((b : ℕ) / (N : ℝ)) x ≤ dist ((b : ℕ) / (N : ℝ)) (t b) + dist (t b) x :=
          dist_triangle _ _ _
        _ ≤ δ + r := add_le_add (by simpa only [dist_comm] using hclose b) (Finset.mem_filter.mp hb).2
    have hgap : ((b : ℕ) : ℝ) - (a : ℕ) ≤ (2 * (δ + r)) * (N : ℝ) := by
      have ha' := abs_le.mp (show |(a : ℕ) / (N : ℝ) - x| ≤ δ + r by simpa only [Real.dist_eq] using hga)
      have hb' := abs_le.mp (show |(b : ℕ) / (N : ℝ) - x| ≤ δ + r by simpa only [Real.dist_eq] using hgb)
      have hh : (b : ℕ) / (N : ℝ) - (a : ℕ) / (N : ℝ) ≤ 2 * (δ + r) := by linarith
      rw [← sub_div, div_le_iff₀ hNr] at hh
      exact hh
    have hdr := mul_le_mul_of_nonneg_right hr hNr.le
    change (S.card : ℝ) ≤ 5 * r * (Fintype.card (Fin N) : ℝ)
    rw [Fintype.card_fin]
    nlinarith
  · change (S.card : ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty, Nat.cast_zero]
    have hrp : 0 < r := hδ.trans_le hr
    positivity

/-- A dense family of slopes in the unit interval supports a finite
indexed family with a uniform one-dimensional Frostman bound. -/
theorem exists_frostman_slopes_of_dense {δ : ℝ} (hδ : 0 < δ) (T : Set ℝ)
    (hdense : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ T, t ∈ Set.Icc (0 : ℝ) 1 ∧ dist t x ≤ δ) :
    ∃ (N : ℕ) (t : Fin N → ℝ), 0 < N ∧ (∀ i, t i ∈ T ∧ t i ∈ Set.Icc (0 : ℝ) 1) ∧
      IndexedRealFrostman δ 5 t := by
  classical
  let N := ⌈δ⁻¹⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (inv_pos.mpr hδ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδN : 1 ≤ δ * (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil δ⁻¹) hδ.le
    simpa only [mul_inv_cancel₀ hδ.ne'] using hh
  have hgrid (i : Fin N) : (i : ℕ) / (N : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hNr).mpr
      exact_mod_cast i.isLt.le
  choose t htT hti htclose using fun i : Fin N => hdense _ (hgrid i)
  exact ⟨N, t, hN, fun i => ⟨htT i, hti i⟩, perturbed_grid_frostman hδ hN hδN t htclose⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
