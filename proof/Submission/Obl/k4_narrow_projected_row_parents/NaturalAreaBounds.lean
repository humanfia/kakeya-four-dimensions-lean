import Submission.Obl.k4_narrow_projected_row_parents.NaturalMajorBounds

namespace Submission.Obl.k4_narrow_projected_row_parents

open Filter
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- The natural common area has a fixed power lower bound after division by
a subpower stability budget. This also bounds the common time from below. -/
theorem eventually_natural_area_lower (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) (s B : ℝ) (β M : ℕ → ℝ)
    (hβ : ∀ᶠ k in atTop, p.N k ^ (-B - 1) ≤ β k)
    (hM : ∀ k, 1 ≤ M k) (hMsub : Model.Subpow p.N M) :
    ∀ᶠ k in atTop, ∀ R : ℝ, a.AtlasAt p R k s →
      p.N k ^ (-(max ((p.kappa + p.ell) * s + 1) (B + 1) + 1)) ≤
        min (a.q k s * narrow p k s) (β k) / M k := by
  have hqg := a.eventually_q_narrow_lower p hp s (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hqg, hβ, hMsub 1 one_pos] with k hq hβk hMk
  intro R hatlas
  have hN1 : 1 ≤ p.N k := by linarith [hp.1 k]
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  have hMp : 0 < M k := zero_lt_one.trans_le (hM k)
  rw [Real.rpow_one] at hMk
  let D : ℝ := max ((p.kappa + p.ell) * s + 1) (B + 1)
  have hlow : p.N k ^ (-D) ≤ min (a.q k s * narrow p k s) (β k) := by
    apply le_min
    · refine (Real.rpow_le_rpow_of_exponent_le hN1
        (neg_le_neg (le_max_left _ _))).trans ?_
      convert hq R s hatlas le_rfl using 1 <;> congr 1 <;> ring
    · refine (Real.rpow_le_rpow_of_exponent_le hN1
        (neg_le_neg (le_max_right _ _))).trans ?_
      convert hβk using 1 <;> congr 1 <;> ring
  calc p.N k ^ (-(max ((p.kappa + p.ell) * s + 1) (B + 1) + 1))
      = p.N k ^ (-D) / p.N k := by
          change p.N k ^ (-(D + 1)) = _
          rw [show -(D + 1) = -D - 1 by ring, Real.rpow_sub hN0, Real.rpow_one]
    _ ≤ p.N k ^ (-D) / M k :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) hMp hMk
    _ ≤ _ := div_le_div_of_nonneg_right hlow hMp.le

end Submission.Obl.k4_narrow_projected_row_parents
