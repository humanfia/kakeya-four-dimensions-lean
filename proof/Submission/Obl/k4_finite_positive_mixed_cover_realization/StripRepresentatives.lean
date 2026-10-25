/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/StripRepresentatives.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.UnitStripCodes

/-!
An actual candidate represents each used parent/parameter code. Choosing an
actual representative keeps its normal exactly unit, and changing to it costs
only path-sized slack. No division by a rounded normal is introduced.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

noncomputable section

def representativeStrip {A P : Type*} (parent : A → P) (normal : A → Plane)
    (bias : A → ℝ) (h : ℝ) (p : P) (row : Fin 3 → ℤ) : Plane × ℝ := by
  classical
  exact if hs : ∃ a, parent a = p ∧ stripParameterCode h (normal a) (bias a) = row then
      (normal (Classical.choose hs), bias (Classical.choose hs))
    else (WithLp.toLp 2 ![1, 0], 0)

theorem representativeStrip_unit {A P : Type*} (parent : A → P) (normal : A → Plane)
    (bias : A → ℝ) (h : ℝ) (hunit : ∀ a, ‖normal a‖ = 1) (p : P) (row : Fin 3 → ℤ) :
    ‖(representativeStrip parent normal bias h p row).1‖ = 1 := by
  classical
  unfold representativeStrip
  split_ifs with hs
  · exact hunit _
  · change ‖(WithLp.toLp 2 ![1, 0] : Plane)‖ = 1
    have hsq : ‖(WithLp.toLp 2 ![1, 0] : Plane)‖ ^ 2 = 1 := by
      rw [norm_sq_fin2]
      norm_num
    nlinarith [norm_nonneg (WithLp.toLp 2 ![1, 0] : Plane)]

theorem representativeStrip_bias_le {A P : Type*} (parent : A → P) (normal : A → Plane)
    (bias : A → ℝ) (h : ℝ) {B : ℝ} (hB : 0 ≤ B) (hbias : ∀ a, |bias a| ≤ B)
    (p : P) (row : Fin 3 → ℤ) :
    |(representativeStrip parent normal bias h p row).2| ≤ B := by
  classical
  unfold representativeStrip
  split_ifs with hs
  · exact hbias _
  · simpa using hB

theorem representativeStrip_code {A P : Type*} (parent : A → P) (normal : A → Plane)
    (bias : A → ℝ) (h : ℝ) (a : A) :
    stripParameterCode h
      (representativeStrip parent normal bias h (parent a) (stripParameterCode h (normal a) (bias a))).1
      (representativeStrip parent normal bias h (parent a) (stripParameterCode h (normal a) (bias a))).2 =
        stripParameterCode h (normal a) (bias a) := by
  classical
  have hs : ∃ a', parent a' = parent a ∧
      stripParameterCode h (normal a') (bias a') = stripParameterCode h (normal a) (bias a) :=
    ⟨a, rfl, rfl⟩
  simp only [representativeStrip, dite_eq_left hs]
  exact (Classical.choose_spec hs).2

theorem representativeStrip_fit {A P : Type*} (parent : A → P) (normal : A → Plane)
    (bias : A → ℝ) {h ε V : ℝ} (hh : 0 < h) (hV : 0 ≤ V)
    (a : A) (v : Plane) (hv : ‖v‖ ≤ V) (hε : ε ≤ h)
    (hfit : |inner ℝ v (normal a) - bias a| ≤ ε) :
    |inner ℝ v
      (representativeStrip parent normal bias h (parent a) (stripParameterCode h (normal a) (bias a))).1 -
      (representativeStrip parent normal bias h (parent a) (stripParameterCode h (normal a) (bias a))).2| ≤
        (4 + 3 * V) * h :=
  strip_fit_of_same_code hh hV hv hε (representativeStrip_code parent normal bias h a).symm hfit

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
