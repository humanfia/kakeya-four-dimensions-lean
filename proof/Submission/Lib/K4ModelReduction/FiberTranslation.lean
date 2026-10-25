import Mathlib

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-!
The elementary one-dimensional translation estimate behind joint base
flattening (paper Lemma `a01:flattening`). A bounded function whose only
changes occur at finitely many boundaries has a uniform L1 translation bound.
-/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

/-- A one-dimensional fiber with finitely many possible change points has
translation error bounded by boundary count times displacement. The local
constancy hypothesis only concerns intervals avoiding every change point. -/
theorem fiber_translation_bound
    (f : ℝ → ℝ) (F : Finset ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x, |f x| ≤ M)
    (hconst : ∀ x y, (∀ a ∈ F, dist x y < dist x a) → f x = f y)
    (h : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal |f (x + h) - f x| ≤
      ENNReal.ofReal (4 * M * (F.card : ℝ) * |h|) := by
  classical
  let S : Set ℝ := ⋃ a : F, closedBall (a : ℝ) |h|
  have hSm : MeasurableSet S := MeasurableSet.iUnion fun _ => measurableSet_closedBall
  have hdist (x : ℝ) : dist x (x + h) = |h| := by
    rw [Real.dist_eq]
    calc
      |x - (x + h)| = |-h| := by congr 1; ring
      _ = |h| := abs_neg _
  have heq (x : ℝ) (hx : x ∉ S) : f x = f (x + h) := by
    apply hconst
    intro a ha
    rw [hdist]
    apply lt_of_not_ge
    intro hle
    exact hx (mem_iUnion.mpr ⟨⟨a, ha⟩, hle⟩)
  have hpoint (x : ℝ) : ENNReal.ofReal |f (x + h) - f x| ≤
      S.indicator (fun _ => ENNReal.ofReal (2 * M)) x := by
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      apply ENNReal.ofReal_le_ofReal
      calc
        |f (x + h) - f x| ≤ |f (x + h)| + |f x| := abs_sub _ _
        _ ≤ M + M := add_le_add (hbound _) (hbound _)
        _ = 2 * M := by ring
    · rw [indicator_of_notMem hx, ← heq x hx, sub_self, abs_zero, ENNReal.ofReal_zero]
  have hvolume : volume S ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal (2 * |h|) := by
    calc
      volume S ≤ ∑ a : F, volume (closedBall (a : ℝ) |h|) :=
        measure_iUnion_fintype_le _ _
      _ = _ := by
        simp only [Real.volume_closedBall, Finset.sum_const, Finset.card_univ,
          Fintype.card_coe, nsmul_eq_mul]
  calc
    ∫⁻ x : ℝ, ENNReal.ofReal |f (x + h) - f x| ≤
        ∫⁻ x : ℝ, S.indicator (fun _ => ENNReal.ofReal (2 * M)) x := lintegral_mono hpoint
    _ = ENNReal.ofReal (2 * M) * volume S := lintegral_indicator_const hSm _
    _ ≤ ENNReal.ofReal (2 * M) *
        ((F.card : ℝ≥0∞) * ENNReal.ofReal (2 * |h|)) := mul_le_mul_right hvolume _
    _ = _ := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end Submission.Lib.K4ModelReduction
