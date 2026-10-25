/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/RowCounting.lean.
   Earlier provenance comments in the source are retained. -/
/- Adapted from this LOT tree, obligation o200, session x0864, commit bba668a8aa9f,
   Submission/Obl/k4_finite_projected_horizontal_candidates/RowCounting.lean
   (namespace renamed; uses the accepted o088 geometry). -/
import Mathlib
import Submission.Obl.k4_finite_row_graph_assembly.Geometry

/-! The finite row-list count keeps the original external palette weights. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.RowCounting

noncomputable section

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Weighted double counting of separated witness pairs. The lower floor is
charged once per row; the upper count is integrated against the original
palette product law. -/
theorem weighted_row_count {R V : Type*} (rows : Finset R) (vel : Finset V)
    (weight : V → ℝ) (test : R → V → V → Prop)
    {m B : ℝ} (hw : ∀ v ∈ vel, 0 ≤ weight v)
    (hfloor : ∀ r ∈ rows, m ≤ ∑ v ∈ vel, ∑ w ∈ vel,
      weight v * weight w * if test r v w then 1 else 0)
    (hcount : ∀ v ∈ vel, ∀ w ∈ vel,
      ((rows.filter (fun r => test r v w)).card : ℝ) ≤ B) :
    (rows.card : ℝ) * m ≤ B * (∑ v ∈ vel, weight v) ^ 2 := by
  classical
  have hcard (v w : V) : (∑ r ∈ rows, if test r v w then (1 : ℝ) else 0) =
      ((rows.filter (fun r => test r v w)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  calc
    _ = ∑ _r ∈ rows, m := by simp
    _ ≤ ∑ r ∈ rows, ∑ v ∈ vel, ∑ w ∈ vel,
        weight v * weight w * if test r v w then 1 else 0 := Finset.sum_le_sum hfloor
    _ = ∑ v ∈ vel, ∑ w ∈ vel, weight v * weight w *
        ((rows.filter (fun r => test r v w)).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      rw [← Finset.mul_sum, hcard]
    _ ≤ ∑ v ∈ vel, ∑ w ∈ vel, weight v * weight w * B := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro w hw'
      exact mul_le_mul_of_nonneg_left (hcount v hv w hw')
        (mul_nonneg (hw v hv) (hw w hw'))
    _ = B * (∑ v ∈ vel, weight v) ^ 2 := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

/-- Probability palettes turn the weighted pair count into a literal row-list
cardinality bound. -/
theorem weighted_row_count_probability {R V : Type*} (rows : Finset R) (vel : Finset V)
    (weight : V → ℝ) (test : R → V → V → Prop)
    {m B : ℝ} (hm : 0 < m) (hB : 0 ≤ B) (hw : ∀ v ∈ vel, 0 ≤ weight v)
    (hsum : ∑ v ∈ vel, weight v ≤ 1)
    (hfloor : ∀ r ∈ rows, m ≤ ∑ v ∈ vel, ∑ w ∈ vel,
      weight v * weight w * if test r v w then 1 else 0)
    (hcount : ∀ v ∈ vel, ∀ w ∈ vel,
      ((rows.filter (fun r => test r v w)).card : ℝ) ≤ B) :
    (rows.card : ℝ) ≤ B / m := by
  classical
  have hS : 0 ≤ ∑ v ∈ vel, weight v := Finset.sum_nonneg hw
  have hS2 : (∑ v ∈ vel, weight v) ^ 2 ≤ 1 := by nlinarith
  have hh := weighted_row_count rows vel weight test hw hfloor hcount
  have hb := mul_le_mul_of_nonneg_left hS2 hB
  apply (le_div_iff₀ hm).mpr
  nlinarith

/-- Two evaluation intervals of radius D contain only polynomially many
integer row bins when the velocities are separated. -/
theorem row_bins_per_pair (rows : Finset (Fin 2 → ℤ))
    {v1 v2 K D a b : ℝ} (hK : 1 ≤ K) (hD : 0 ≤ D)
    (hv1 : |v1| ≤ K) (hv2 : |v2| ≤ K) (hsep : 1 / K ≤ |v2 - v1|)
    (h1 : ∀ r ∈ rows, |(r 0 : ℝ) + v1 * (r 1 : ℝ) - a| ≤ D)
    (h2 : ∀ r ∈ rows, |(r 0 : ℝ) + v2 * (r 1 : ℝ) - b| ≤ D) :
    (rows.card : ℝ) ≤ (12 * K ^ 2 * D + 2) ^ 2 := by
  have hd (r) (hr : r ∈ rows) (s) (hs : s ∈ rows) (v c : ℝ)
      (hv : ∀ u ∈ rows, |(u 0 : ℝ) + v * (u 1 : ℝ) - c| ≤ D) :
      |((r 0 : ℝ) - s 0) + v * ((r 1 : ℝ) - s 1)| ≤ 2 * D := by
    calc
      _ = |((r 0 : ℝ) + v * r 1 - c) - ((s 0 : ℝ) + v * s 1 - c)| := by congr 1; ring
      _ ≤ |(r 0 : ℝ) + v * r 1 - c| + |(s 0 : ℝ) + v * s 1 - c| := abs_sub _ _
      _ ≤ 2 * D := by linarith [hv r hr, hv s hs]
  have hdiam : ∀ r ∈ rows, ∀ s ∈ rows, ∀ e : Fin 2,
      |(r e : ℝ) - s e| ≤ 6 * K ^ 2 * D := by
    intro r hr s hs e
    have hh := Submission.Obl.k4_finite_row_graph_assembly.row_error_of_two_evaluations
      hK hv1 hv2 hsep (hd r hr s hs v1 a h1) (hd r hr s hs v2 b h2)
    fin_cases e
    · change |(r 0 : ℝ) - s 0| ≤ 6 * K ^ 2 * D
      convert hh.1 using 1 <;> ring
    · change |(r 1 : ℝ) - s 1| ≤ 6 * K ^ 2 * D
      have hKK : 2 * K ≤ 3 * K ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hKK (by positivity : 0 ≤ 2 * D)
      nlinarith [hh.2]
  have hh := Submission.Obl.k4_finite_row_graph_assembly.card_pi_grid_of_diameter rows
    (by positivity : 0 ≤ 6 * K ^ 2 * D) hdiam
  simpa only [Fintype.card_fin, show 2 * (6 * K ^ 2 * D) + 2 = 12 * K ^ 2 * D + 2 by ring] using hh


/-- A pair of short evaluation lists bounds all compatible row bins. -/
theorem row_bins_from_two_lists (rows : Finset (Fin 2 → ℤ)) (L1 L2 : Finset ℝ)
    (good : (Fin 2 → ℤ) → Prop) {v1 v2 K D : ℝ}
    (hK : 1 ≤ K) (hD : 0 ≤ D) (hv1 : |v1| ≤ K) (hv2 : |v2| ≤ K)
    (hsep : 1 / K ≤ |v2 - v1|)
    (hlist1 : ∀ r ∈ rows, good r → ∃ a ∈ L1, |(r 0 : ℝ) + v1 * r 1 - a| ≤ D)
    (hlist2 : ∀ r ∈ rows, good r → ∃ b ∈ L2, |(r 0 : ℝ) + v2 * r 1 - b| ≤ D) :
    ((rows.filter good).card : ℝ) ≤
      (L1.card : ℝ) * L2.card * (12 * K ^ 2 * D + 2) ^ 2 := by
  classical
  let F : ℝ → ℝ → Finset (Fin 2 → ℤ) := fun a b => rows.filter (fun r =>
    |(r 0 : ℝ) + v1 * r 1 - a| ≤ D ∧ |(r 0 : ℝ) + v2 * r 1 - b| ≤ D)
  have hsub : rows.filter good ⊆ L1.biUnion (fun a => L2.biUnion (F a)) := by
    intro r hr
    obtain ⟨hr, hrg⟩ := Finset.mem_filter.mp hr
    obtain ⟨a, ha, hra⟩ := hlist1 r hr hrg
    obtain ⟨b, hb, hrb⟩ := hlist2 r hr hrg
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_biUnion.mpr
      ⟨b, hb, Finset.mem_filter.mpr ⟨hr, hra, hrb⟩⟩⟩
  have hF (a b : ℝ) : ((F a b).card : ℝ) ≤ (12 * K ^ 2 * D + 2) ^ 2 := by
    apply row_bins_per_pair (F a b) hK hD hv1 hv2 hsep
    · intro r hr
      exact (Finset.mem_filter.mp hr).2.1
    · intro r hr
      exact (Finset.mem_filter.mp hr).2.2
  calc
    _ ≤ ((L1.biUnion (fun a => L2.biUnion (F a))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ a ∈ L1, ((L2.biUnion (F a)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ a ∈ L1, ∑ b ∈ L2, ((F a b).card : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ L1, ∑ _b ∈ L2, (12 * K ^ 2 * D + 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum (fun b hb => hF a b)
    _ = _ := by simp [mul_assoc]

/-- The row count needed before applying Row: a short list for each velocity,
and a positive original-palette pair weight per row option, give a short row
list at the horizontal location. -/
theorem row_list_card_from_palette_pairs (rows : Finset (Fin 2 → ℤ)) (vel : Finset ℝ)
    (weight : ℝ → ℝ) (good : (Fin 2 → ℤ) → ℝ → Prop) (L : ℝ → Finset ℝ)
    {K D m : ℝ} (hK : 1 ≤ K) (hD : 0 ≤ D) (hm : 0 < m)
    (hw : ∀ v ∈ vel, 0 ≤ weight v) (hsum : ∑ v ∈ vel, weight v ≤ 1)
    (hv : ∀ v ∈ vel, |v| ≤ K) (hL : ∀ v ∈ vel, (L v).card ≤ K)
    (hlist : ∀ r ∈ rows, ∀ v ∈ vel, good r v →
      ∃ a ∈ L v, |(r 0 : ℝ) + v * r 1 - a| ≤ D)
    (hpair : ∀ r ∈ rows, m ≤ ∑ v ∈ vel, ∑ w ∈ vel, weight v * weight w *
      if 1 / K ≤ |w - v| ∧ good r v ∧ good r w then 1 else 0) :
    (rows.card : ℝ) ≤ K ^ 2 * (12 * K ^ 2 * D + 2) ^ 2 / m := by
  classical
  apply weighted_row_count_probability rows vel weight
    (fun r v w => 1 / K ≤ |w - v| ∧ good r v ∧ good r w) hm (by positivity) hw hsum
  · intro r hr
    apply (hpair r hr).trans_eq
    apply Finset.sum_congr rfl
    intro v hvv
    apply Finset.sum_congr rfl
    intro w hww
    by_cases h : 1 / K ≤ |w - v| ∧ good r v ∧ good r w <;> simp only [h, ite_true, ite_false]
  intro v hvv w hww
  by_cases hs : 1 / K ≤ |w - v|
  · have hh := row_bins_from_two_lists rows (L v) (L w) (fun r => good r v ∧ good r w)
      hK hD (hv v hvv) (hv w hww) hs
      (fun r hr hg => hlist r hr v hvv hg.1) (fun r hr hg => hlist r hr w hww hg.2)
    have hprod : (L v).card * (L w).card ≤ K ^ 2 := by
      have hh := mul_le_mul (hL v hvv) (hL w hww) (Nat.cast_nonneg _) (by linarith : 0 ≤ K)
      simpa only [sq] using hh
    have hb := hh.trans (mul_le_mul_of_nonneg_right hprod (sq_nonneg (12 * K ^ 2 * D + 2)))
    apply le_of_eq_of_le ?_ hb
    apply congrArg (fun S : Finset (Fin 2 → ℤ) => (S.card : ℝ))
    ext r
    simp only [Finset.mem_filter, hs, true_and]
  · simp only [hs, false_and, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
    positivity

end
end Submission.Obl.k4_narrow_projected_row_parents.RowCounting
