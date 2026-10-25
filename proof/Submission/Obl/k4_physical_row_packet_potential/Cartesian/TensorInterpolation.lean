-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/TensorInterpolation.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/TensorInterpolation.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/TensorInterpolation.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Mathlib

/-!
Stability of tensor interpolation on a complete Cartesian set of vertices.
The coefficients may have either sign, as Lagrange interpolation requires.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open scoped BigOperators

noncomputable section

variable {A B C E : Type*} [Fintype A] [Fintype B] [Fintype C]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype B] [Fintype C] in
theorem norm_weighted_sum_le (w : A → ℝ) (f : A → E) (ε : ℝ)
    (hf : ∀ a, ‖f a‖ ≤ ε) :
    ‖∑ a, w a • f a‖ ≤ (∑ a, |w a|) * ε := by
  calc
    ‖∑ a, w a • f a‖ ≤ ∑ a, ‖w a • f a‖ := norm_sum_le _ _
    _ ≤ ∑ a, |w a| * ε := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf a) (abs_nonneg _)
    _ = (∑ a, |w a|) * ε := (Finset.sum_mul ..).symm

def tensorInterpolation3 (wa : A → ℝ) (wb : B → ℝ) (wc : C → ℝ)
    (f : A → B → C → E) : E :=
  ∑ a, wa a • ∑ b, wb b • ∑ c, wc c • f a b c

/-- Fiber approximation errors accumulate through the sums of the absolute
Lagrange weights. All the intermediate vertices are explicitly present. -/
theorem norm_tensorInterpolation3_error_le
    (wa : A → ℝ) (wb : B → ℝ) (wc : C → ℝ)
    (f : Option A → Option B → Option C → E) (ε₀ ε₁ ε₂ : ℝ)
    (h₀ : ‖f none none none - ∑ a, wa a • f (some a) none none‖ ≤ ε₀)
    (h₁ : ∀ a, ‖f (some a) none none - ∑ b, wb b • f (some a) (some b) none‖ ≤ ε₁)
    (h₂ : ∀ a b, ‖f (some a) (some b) none -
      ∑ c, wc c • f (some a) (some b) (some c)‖ ≤ ε₂) :
    ‖f none none none - tensorInterpolation3 wa wb wc
      (fun a b c => f (some a) (some b) (some c))‖ ≤
      ε₀ + (∑ a, |wa a|) * ε₁ + (∑ a, |wa a|) * (∑ b, |wb b|) * ε₂ := by
  let L₁ := ∑ a, wa a • f (some a) none none
  let L₂ := ∑ a, wa a • ∑ b, wb b • f (some a) (some b) none
  let P := tensorInterpolation3 wa wb wc (fun a b c => f (some a) (some b) (some c))
  have hstep₁ : ‖L₁ - L₂‖ ≤ (∑ a, |wa a|) * ε₁ := by
    dsimp only [L₁, L₂]
    rw [← Finset.sum_sub_distrib]
    simp only [← smul_sub]
    exact norm_weighted_sum_le wa _ ε₁ h₁
  have hstep₂ : ‖L₂ - P‖ ≤ (∑ a, |wa a|) * ((∑ b, |wb b|) * ε₂) := by
    dsimp only [L₂, P, tensorInterpolation3]
    rw [← Finset.sum_sub_distrib]
    simp only [← smul_sub]
    apply norm_weighted_sum_le
    intro a
    rw [← Finset.sum_sub_distrib]
    simp only [← smul_sub]
    exact norm_weighted_sum_le wb _ ε₂ (h₂ a)
  have htriangle := dist_triangle4 (f none none none) L₁ L₂ P
  simp only [dist_eq_norm] at htriangle
  exact htriangle.trans ((add_le_add (add_le_add h₀ hstep₁) hstep₂).trans_eq (by ring))

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
