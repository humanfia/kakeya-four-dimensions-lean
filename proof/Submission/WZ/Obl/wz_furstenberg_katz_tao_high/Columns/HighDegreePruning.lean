-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.HighDegreePruning.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open scoped BigOperators

/-- A second moment for the number of cells controls the incidence mass
in coarse tubes of large degree.  The only weight assumption is an upper
bound per occupied cell; shared arcs between pins are not assumed. -/
theorem high_degree_mass_bound {τ : Type*} (T : Finset τ) (c w : τ → ℝ)
    {W E B : ℝ} (hW : 0 ≤ W) (hB : 0 < B)
    (hc : ∀ t ∈ T, 0 ≤ c t)
    (hw : ∀ t ∈ T, w t ≤ W * c t)
    (hsecond : ∑ t ∈ T, c t ^ 2 ≤ E) :
    ∑ t ∈ T.filter (fun t => B < c t), w t ≤ W * E / B := by
  classical
  have hratio : 0 ≤ W / B := div_nonneg hW hB.le
  calc
    ∑ t ∈ T.filter (fun t => B < c t), w t
        ≤ ∑ t ∈ T.filter (fun t => B < c t), (W / B) * c t ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨htT, htB⟩ := Finset.mem_filter.mp ht
      have hdegree : c t ≤ c t ^ 2 / B := by
        rw [le_div_iff₀ hB]
        nlinarith only [hc t htT, htB]
      calc
        w t ≤ W * c t := hw t htT
        _ ≤ W * (c t ^ 2 / B) := mul_le_mul_of_nonneg_left hdegree hW
        _ = (W / B) * c t ^ 2 := by ring
    _ = (W / B) * ∑ t ∈ T.filter (fun t => B < c t), c t ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (W / B) * ∑ t ∈ T, c t ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hratio
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun t _ _ => sq_nonneg (c t))
    _ ≤ (W / B) * E := mul_le_mul_of_nonneg_left hsecond hratio
    _ = W * E / B := by ring

/-- Remove high-degree coarse tubes with a controlled incidence loss. -/
theorem retained_mass_of_second_moment {τ : Type*} (T : Finset τ) (c w : τ → ℝ)
    {W E B : ℝ} (hW : 0 ≤ W) (hB : 0 < B)
    (hc : ∀ t ∈ T, 0 ≤ c t)
    (hw : ∀ t ∈ T, w t ≤ W * c t)
    (hsecond : ∑ t ∈ T, c t ^ 2 ≤ E) :
    ∑ t ∈ T, w t ≤ (∑ t ∈ T.filter (fun t => c t ≤ B), w t) + W * E / B := by
  classical
  have hsplit : ∑ t ∈ T, w t =
      (∑ t ∈ T.filter (fun t => c t ≤ B), w t) +
        ∑ t ∈ T.filter (fun t => B < c t), w t := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases ht : c t ≤ B
    · simp [ht, not_lt_of_ge ht]
    · simp [ht, lt_of_not_ge ht]
  rw [hsplit]
  exact add_le_add le_rfl (high_degree_mass_bound T c w hW hB hc hw hsecond)

/-- The standard half-incidence choice of cutoff. -/
theorem half_mass_of_second_moment {τ : Type*} (T : Finset τ) (c w : τ → ℝ)
    {W E B : ℝ} (hW : 0 ≤ W) (hB : 0 < B)
    (hc : ∀ t ∈ T, 0 ≤ c t)
    (hw : ∀ t ∈ T, w t ≤ W * c t)
    (hsecond : ∑ t ∈ T, c t ^ 2 ≤ E)
    (hbudget : 2 * W * E ≤ B * ∑ t ∈ T, w t) :
    (∑ t ∈ T, w t) / 2 ≤ ∑ t ∈ T.filter (fun t => c t ≤ B), w t := by
  classical
  have hmass := retained_mass_of_second_moment T c w hW hB hc hw hsecond
  have hcost : W * E / B ≤ (∑ t ∈ T, w t) / 2 := by
    rw [div_le_iff₀ hB]
    nlinarith only [hbudget]
  linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
