-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.StripCounts, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/StripCounts.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/StripCounts.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/StripCounts.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Lib.K4QuadraticSublevel
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.RowPalette
import Submission.Obl.k4_scalar_coefficient_clustering.Grid

/-!
Normal strips in a physical cube. Endpoint derivative control is sufficient
because the derivative of a quadratic is affine. Strip filling is used only
to certify a support list, which then survives all further restrictions.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_scalar_coefficient_clustering

noncomputable section

/-- A quadratic with small derivative at the active occurrences can meet
only boundedly many normal strips inside a single physical time cell. -/
theorem quadratic_strip_visit_count (S : Finset ℤ) (q : Polynomial ℝ)
    (hq : q.natDegree ≤ 2) (t z : ℤ → ℝ) (o ρ η ε p : ℝ)
    (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hε : 0 ≤ ε) (hp : 0 < p)
    (ht : ∀ i ∈ S, t i ∈ Set.Icc o (o + ρ))
    (hderiv : ∀ i ∈ S, |q.derivative.eval (t i)| ≤ η)
    (hfit : ∀ i ∈ S, |z i - q.eval (t i)| ≤ ε)
    (hbin : ∀ i ∈ S, ⌊z i / p⌋ = i) :
    (S.card : ℝ) ≤ 2 * (2 * ε + η * ρ) / p + 4 := by
  have hdiam : ∀ i ∈ S, ∀ j ∈ S,
      |(i : ℝ) - (j : ℝ)| ≤ (2 * ε + η * ρ) / p + 1 := by
    intro i hi j hj
    have hdt : |t i - t j| ≤ ρ := by
      apply abs_le.mpr
      constructor <;> linarith [(ht i hi).1, (ht i hi).2, (ht j hj).1, (ht j hj).2]
    have hsum : |q.derivative.eval (t j) + q.derivative.eval (t i)| ≤ 2 * η := by
      exact (abs_add_le _ _).trans (by linarith [hderiv i hi, hderiv j hj])
    have heq := congrArg abs (Submission.Lib.K4QuadraticSublevel.quadratic_eval_sub q hq (t j) (t i))
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at heq
    have hprod := mul_le_mul hdt hsum (abs_nonneg _) hρ
    rw [← heq] at hprod
    have hqd : |q.eval (t i) - q.eval (t j)| ≤ η * ρ := by nlinarith
    have hzd : |z i - z j| ≤ 2 * ε + η * ρ := by
      calc
        _ ≤ |z i - q.eval (t i)| + |q.eval (t i) - z j| := abs_sub_le _ _ _
        _ ≤ |z i - q.eval (t i)| +
            (|q.eval (t i) - q.eval (t j)| + |q.eval (t j) - z j|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
        _ ≤ 2 * ε + η * ρ := by
          rw [abs_sub_comm (q.eval (t j))]
          linarith [hfit i hi, hfit j hj]
    have hscaled : |z i / p - z j / p| ≤ (2 * ε + η * ρ) / p := by
      rw [← sub_div, abs_div, abs_of_pos hp]
      exact div_le_div_of_nonneg_right hzd hp.le
    have h := Submission.Obl.k4_matching_homogeneous_records.floor_sub_bound (z i / p) (z j / p)
    rw [hbin i hi, hbin j hj, Int.cast_sub] at h
    linarith
  have h := card_int_grid_of_diameter S
    (show 0 ≤ (2 * ε + η * ρ) / p + 1 by positivity) hdiam
  exact h.trans_eq (by ring)

/-- Filling every retained strip and bounding the number of strips met by
one physical cell converts hereditary physical support into scalar support.
Only the original support witnesses enter this count. -/
theorem normal_strip_count_from_filling {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (C : Finset κ) (W : ι → Finset κ) (K H r p d : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hr : 0 < r) (hp : 0 < p)
    (hsub : ∀ s ∈ S, W s ⊆ C)
    (hfill : ∀ s ∈ S, (H / p) ^ 3 / K ≤ ((W s).card : ℝ))
    (hmult : ∀ c ∈ C, ((S.filter fun s => c ∈ W s).card : ℝ) ≤ K)
    (hphysical : (C.card : ℝ) ≤ K * (H / r) ^ 3 * (r / p) ^ (3 + d)) :
    (S.card : ℝ) ≤ K ^ 3 * (r / p) ^ d := by
  have h := weighted_witness_count S C W (fun _ => (1 : ℝ)) ((H / p) ^ 3 / K) K
    (fun _ _ => zero_le_one) hsub
    (fun s hs => by simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hfill s hs) hmult
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hbound : (S.card : ℝ) * ((H / p) ^ 3 / K) ≤
      K * (K * (H / r) ^ 3 * (r / p) ^ (3 + d)) :=
    h.trans (mul_le_mul_of_nonneg_left hphysical hK.le)
  have hidentity : K * (K * (H / r) ^ 3 * (r / p) ^ (3 + d)) =
      (K ^ 3 * (r / p) ^ d) * ((H / p) ^ 3 / K) := by
    rw [Real.rpow_add (div_pos hr hp),
      show (r / p) ^ (3 : ℝ) = (r / p) ^ (3 : ℕ) by norm_num]
    field_simp
  rw [hidentity] at hbound
  exact (mul_le_mul_iff_left₀ (div_pos (pow_pos (div_pos hH hp) 3) hK)).mp hbound

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
