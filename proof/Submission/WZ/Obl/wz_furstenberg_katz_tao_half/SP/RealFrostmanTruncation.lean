-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.RealFrostmanTruncation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CartesianFrostman

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- Passing to a positive proportion subset costs the reciprocal proportion
in normalized Frostman control. -/
theorem RealFiniteFrostman.subset {δ C σ d : ℝ} {A B : Finset ℝ}
    (h : RealFiniteFrostman δ C σ A) (hδ : 0 < δ) (hC : 0 ≤ C) (hd : 0 < d)
    (hBA : B ⊆ A) (hsize : d * (A.card : ℝ) ≤ (B.card : ℝ)) :
    RealFiniteFrostman δ (C / d) σ B := by
  classical
  intro x r hr
  have hrp : 0 < r := hδ.trans_le hr
  have hsub : B.filter (fun b => dist b x ≤ r) ⊆ A.filter (fun a => dist a x ≤ r) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨hBA (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2⟩
  have hn : (A.card : ℝ) ≤ (B.card : ℝ) / d := (le_div_iff₀ hd).mpr (by nlinarith)
  calc
    ((B.filter (fun b => dist b x ≤ r)).card : ℝ) ≤
        ((A.filter (fun a => dist a x ≤ r)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ C * r ^ σ * (A.card : ℝ) := h x r hr
    _ ≤ C * r ^ σ * ((B.card : ℝ) / d) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by ring

/-- The small initial interval can be discarded while retaining at least
half the points and normalized Frostman control. -/
theorem RealFiniteFrostman.trim_zero {δ C σ c : ℝ} {A : Finset ℝ}
    (h : RealFiniteFrostman δ C σ A) (hδ : 0 < δ) (hC : 0 ≤ C) (hδc : δ ≤ c)
    (hA : A.Nonempty) (hpos : ∀ a ∈ A, 0 ≤ a) (hsmall : C * c ^ σ ≤ 1 / 2) :
    ∃ B : Finset ℝ, B ⊆ A ∧ B.Nonempty ∧
      (∀ b ∈ B, c ≤ b) ∧ (A.card : ℝ) ≤ 2 * (B.card : ℝ) ∧
      RealFiniteFrostman δ (2 * C) σ B := by
  classical
  let B := A.filter (fun a => c ≤ a)
  let N := A.filter (fun a => dist a 0 ≤ c)
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hsub : A ⊆ B ∪ N := by
    intro a ha
    by_cases hca : c ≤ a
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, hca⟩)
    · apply Finset.mem_union_right _
      refine Finset.mem_filter.mpr ⟨ha, ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hpos a ha)]
      exact (lt_of_not_ge hca).le
  have hcard : (A.card : ℝ) ≤ (B.card : ℝ) + (N.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hN : (N.card : ℝ) ≤ (A.card : ℝ) / 2 := by
    have hh := h 0 c hδc
    have hm := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
    dsimp [N]
    nlinarith
  have hBsize : (A.card : ℝ) ≤ 2 * (B.card : ℝ) := by linarith
  have hBne : B.Nonempty := by
    have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
    apply Finset.card_pos.mp
    have hBp : (0 : ℝ) < B.card := by linarith
    exact_mod_cast hBp
  refine ⟨B, hBA, hBne, fun b hb => (Finset.mem_filter.mp hb).2, hBsize, ?_⟩
  have hh := h.subset hδ hC (by norm_num : (0 : ℝ) < 1 / 2) hBA (by linarith)
  convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
