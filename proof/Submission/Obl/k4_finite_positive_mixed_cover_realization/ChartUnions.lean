/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/ChartUnions.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Lib.K4XInterface.Charts
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Grouping

/-!
Merging the priority pieces with one strip label. The geometry, quadratic
test and time block are common to those pieces. Their polynomial sign tests
are concatenated using the accepted finite-union format lemma.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set
open Submission.Lib.K4XInterface

/-- A polynomially sized union of charts with common geometry is a chart,
with a fixed enlarged format exponent. -/
theorem gchart_iUnion_fin {n M Mc D T : ℕ} {Nk κ j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ}
    (A : Fin n → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hn : 0 < n) (hNk : 1 ≤ Nk) (hcount : (n : ℝ) ≤ Nk ^ Mc)
    (hchart : ∀ i, gchart Nk M D κ T j r Bv Ev c u Q R (A i) (F i) True)
    {ex : Prop} (hex : ex) :
    gchart Nk (M + Mc) D κ T j r Bv Ev c u Q R (⋃ i, A i) (⋃ i, F i) ex := by
  have hpow : Nk ^ M ≤ Nk ^ (M + Mc) := pow_le_pow_right₀ hNk (by omega)
  have hformat : (n : ℝ) * Nk ^ M ≤ Nk ^ (M + Mc) := by
    calc
      _ ≤ Nk ^ Mc * Nk ^ M := mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hAm (i : Fin n) : MeasurableSet (A i) := (hchart i).2.2.2.2.2.2.1
  have hFm (i : Fin n) : MeasurableSet (F i) := (hchart i).2.2.2.2.2.2.2.1
  have hAf (tag : ℕ) (i : Fin n) : gfmt 6 (Nk ^ M) D {x | (tag, x) ∈ A i} :=
    ((hchart i).2.2.2.2.2.2.2.2.1 tag).1
  have hFf (tag : ℕ) (i : Fin n) :
      gfmt 7 (Nk ^ M) D {x : Fin 7 → ℝ | ((tag, fun j : Fin 6 => x j.castSucc), x 6) ∈ F i} :=
    ((hchart i).2.2.2.2.2.2.2.2.1 tag).2
  obtain ⟨hdet, hcu, hframe, hsize, hdeg, hcoef, -, -, -, -, -, -⟩ := hchart ⟨0, hn⟩
  refine ⟨hdet, hcu.trans hpow, hframe.trans hpow, hsize, hdeg,
    fun e => (hcoef e).trans hpow, MeasurableSet.iUnion hAm, MeasurableSet.iUnion hFm,
    ?_, ?_, ?_, hex⟩
  · intro tag
    constructor
    · apply gfmt_mono hformat le_rfl
      have hf := k4_fixed_budget_quadratic_recovery.fmt_iUnion_fin n _ (hAf tag)
      have heq : {x | (tag, x) ∈ ⋃ i, A i} = ⋃ i, {x | (tag, x) ∈ A i} := by
        ext x
        simp
      rw [heq]
      exact hf
    · apply gfmt_mono hformat le_rfl
      have hf := k4_fixed_budget_quadratic_recovery.fmt_iUnion_fin n _ (hFf tag)
      have heq : {x : Fin 7 → ℝ | ((tag, fun j : Fin 6 => x j.castSucc), x 6) ∈ ⋃ i, F i} =
          ⋃ i, {x : Fin 7 → ℝ | ((tag, fun j : Fin 6 => x j.castSucc), x 6) ∈ F i} := by
        ext x
        simp
      rw [heq]
      exact hf
  · intro l hl
    obtain ⟨i, hi⟩ := mem_iUnion.mp hl
    obtain ⟨htag, hcoords, hwhole⟩ := (hchart i).2.2.2.2.2.2.2.2.2.1 l hi
    exact ⟨htag.trans hpow, fun e => (hcoords e).trans hpow, hwhole⟩
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    obtain ⟨hE, hA, htime, hderiv⟩ := (hchart i).2.2.2.2.2.2.2.2.2.2.1 p hi
    exact ⟨hE, mem_iUnion.mpr ⟨i, hA⟩, htime, hderiv⟩

end Submission.Obl.k4_finite_positive_mixed_cover_realization
