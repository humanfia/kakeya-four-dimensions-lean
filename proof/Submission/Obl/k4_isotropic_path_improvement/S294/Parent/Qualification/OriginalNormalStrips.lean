-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalNormalStrips, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalNormalStrips.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalNormalStrips.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalNormalStrips.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.StripCounts
import Submission.Lib.K4VelocityStrips.StripBins


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Polynomial
open scoped BigOperators

noncomputable section

/-- Subtract the fixed physical row from the actual signal polynomial.
All three base coordinates remain those of the original affine line. -/
def originalNormalPolynomial (signal : Polynomial ℝ) (a v G : Fin 3 → ℝ) : Polynomial ℝ :=
  signal - ∑ j, C (G j) * (C (a j) + C (v j) * X)

theorem originalNormalPolynomial_eval (signal : Polynomial ℝ) (a v G : Fin 3 → ℝ) (t : ℝ) :
    (originalNormalPolynomial signal a v G).eval t =
      signal.eval t - ∑ j, G j * (a j + v j * t) := by
  simp [originalNormalPolynomial, Polynomial.eval_finsetSum]

theorem originalNormalPolynomial_derivative (signal : Polynomial ℝ)
    (a v G : Fin 3 → ℝ) (t : ℝ) :
    (originalNormalPolynomial signal a v G).derivative.eval t =
      signal.derivative.eval t - ∑ j, G j * v j := by
  simp [originalNormalPolynomial, Polynomial.eval_finsetSum]

theorem originalNormalPolynomial_degree (signal : Polynomial ℝ) (a v G : Fin 3 → ℝ)
    (hs : signal.natDegree ≤ 2) : (originalNormalPolynomial signal a v G).natDegree ≤ 2 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le hs
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_add_le _ _).trans
  exact max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))

/-- Actual fine physical bins determine this normal strip coordinate. -/
def originalNormalStateCenter (signal : Polynomial ℝ) (a v G : Fin 3 → ℝ)
    (b t : ℝ) : ℝ :=
  (⌊signal.eval t / b⌋ : ℝ) * b -
    ∑ j, G j * ((⌊(a j + v j * t) / b⌋ : ℝ) * b)

theorem originalNormalStateCenter_error (signal : Polynomial ℝ) (a v G : Fin 3 → ℝ)
    (b B t : ℝ) (hb : 0 < b) (hB : 0 ≤ B) (hG : ∀ j, |G j| ≤ B) :
    |originalNormalStateCenter signal a v G b t -
      (originalNormalPolynomial signal a v G).eval t| ≤ (1 + 3 * B) * b := by
  have hsignal := Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hb (signal.eval t)
  have hterm (j : Fin 3) :
      |G j * (((⌊(a j + v j * t) / b⌋ : ℝ) * b) - (a j + v j * t))| ≤ B * b := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul (hG j)
      (Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hb _) (abs_nonneg _) hB
  have hsum : |∑ j : Fin 3, G j *
      (((⌊(a j + v j * t) / b⌋ : ℝ) * b) - (a j + v j * t))| ≤ 3 * B * b := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun j _ => hterm j)).trans_eq
      (by simp; ring))
  rw [originalNormalStateCenter, originalNormalPolynomial_eval]
  have heq : (⌊signal.eval t / b⌋ : ℝ) * b -
      ∑ j, G j * ((⌊(a j + v j * t) / b⌋ : ℝ) * b) -
      (signal.eval t - ∑ j, G j * (a j + v j * t)) =
      ((⌊signal.eval t / b⌋ : ℝ) * b - signal.eval t) -
        ∑ j, G j * (((⌊(a j + v j * t) / b⌋ : ℝ) * b) - (a j + v j * t)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [heq]
  have htri := abs_sub ((⌊signal.eval t / b⌋ : ℝ) * b - signal.eval t)
    (∑ j, G j * (((⌊(a j + v j * t) / b⌋ : ℝ) * b) - (a j + v j * t)))
  rw [abs_sub_comm ((⌊signal.eval t / b⌋ : ℝ) * b)] at htri
  nlinarith

/-- Original graph comparison and a nearby coarse row control the true
normal derivative at active occurrences. -/
theorem original_normal_derivative_bound (signal : Polynomial ℝ) (a v G H : Fin 3 → ℝ)
    (t E η K : ℝ) (hη : 0 ≤ η)
    (hgraph : |signal.derivative.eval t - ∑ j, H j * v j| ≤ E)
    (hrow : ∀ j, |H j - G j| ≤ η) (hvel : ∀ j, |v j| ≤ K) :
    |(originalNormalPolynomial signal a v G).derivative.eval t| ≤ E + 3 * η * K := by
  have hterm (j : Fin 3) : |(H j - G j) * v j| ≤ η * K := by
    rw [abs_mul]
    exact mul_le_mul (hrow j) (hvel j) (abs_nonneg _) hη
  have hsum : |∑ j, (H j - G j) * v j| ≤ 3 * η * K := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun j _ => hterm j)).trans_eq
      (by simp; ring))
  rw [originalNormalPolynomial_derivative]
  rw [show signal.derivative.eval t - ∑ j, G j * v j =
      (signal.derivative.eval t - ∑ j, H j * v j) + ∑ j, (H j - G j) * v j by
    simp only [sub_mul, Finset.sum_sub_distrib]; ring]
  exact (abs_add_le _ _).trans (add_le_add hgraph hsum)

/-- Actual normal strips met by ONE original trajectory in one coarse
time cell. The fine-state center error and normal derivative bound are
constructed here; the quadratic strip-count theorem is imported. -/
theorem original_normal_strip_visit_count (strips : Finset ℤ)
    (signal : Polynomial ℝ) (hsignal : signal.natDegree ≤ 2)
    (a v G : Fin 3 → ℝ) (field : ℤ → Fin 3 → ℝ) (t : ℤ → ℝ)
    (left ρ b B E η K p : ℝ)
    (hρ : 0 ≤ ρ) (hb : 0 < b) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hp : 0 < p)
    (hG : ∀ j, |G j| ≤ B) (hvel : ∀ j, |v j| ≤ K)
    (ht : ∀ i ∈ strips, t i ∈ Set.Icc left (left + ρ))
    (hgraph : ∀ i ∈ strips, |signal.derivative.eval (t i) - ∑ j, field i j * v j| ≤ E)
    (hrow : ∀ i ∈ strips, ∀ j, |field i j - G j| ≤ η)
    (hbin : ∀ i ∈ strips, ⌊originalNormalStateCenter signal a v G b (t i) / p⌋ = i) :
    (strips.card : ℝ) ≤
      2 * (2 * ((1 + 3 * B) * b) + (E + 3 * η * K) * ρ) / p + 4 := by
  apply quadratic_strip_visit_count strips (originalNormalPolynomial signal a v G)
    (originalNormalPolynomial_degree signal a v G hsignal) t
    (fun i => originalNormalStateCenter signal a v G b (t i))
    left ρ (E + 3 * η * K) ((1 + 3 * B) * b) p hρ (by positivity) (by positivity) hp ht
  · intro i hi
    exact original_normal_derivative_bound signal a v G (field i) (t i) E η K hη
      (hgraph i hi) (hrow i hi) hvel
  · intro i _
    exact originalNormalStateCenter_error signal a v G b B (t i) hb hB hG
  · exact hbin

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
