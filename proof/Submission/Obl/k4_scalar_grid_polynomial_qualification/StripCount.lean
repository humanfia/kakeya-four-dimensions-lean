import Mathlib

/- In a coefficient-world application, a world time-slice may select strip
   indices, while the filling sets and physical cells stay in the full global
   family. Restricting the filling law to a coefficient bin can destroy the
   original velocity breadth. The hfill hypothesis must therefore be supplied
   by the global filling sets of the selected strips, not by their time-slice
   or coefficient-world restrictions.
   Geometric caution: x0797, o229, DMs 2026-10-21 14:50:57Z and 14:59:33Z. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

/-- Strip filling and bounded overlap turn a physical support list into a
one-dimensional scalar support list. This is the finite counting step of
the paper's strip-count estimate. -/
theorem scalar_strip_count {S Q : Type*} [DecidableEq S] [DecidableEq Q]
    (strips : Finset S) (cells : Finset Q) (meets : S → Q → Prop)
    [DecidableRel meets] {K p r ρ d : ℝ} (hK : 0 < K)
    (hp : 0 < p) (hr : 0 < r) (hρ : 0 < ρ)
    (hfill : ∀ a ∈ strips, (ρ / p) ^ 2 / K ≤
      ((Finset.bipartiteAbove meets cells a).card : ℝ))
    (hoverlap : ∀ q ∈ cells,
      ((Finset.bipartiteBelow meets strips q).card : ℝ) ≤ K)
    (hsupport : (cells.card : ℝ) ≤ K * (ρ / r) ^ 2 * (r / p) ^ ((2 : ℝ) + d)) :
    (strips.card : ℝ) ≤ K ^ 3 * (r / p) ^ d := by
  have hcount := Finset.card_nsmul_le_card_nsmul (R := ℝ) meets hfill hoverlap
  simp only [nsmul_eq_mul] at hcount
  have hid : (K * (ρ / r) ^ 2 * (r / p) ^ ((2 : ℝ) + d)) * K =
      (K ^ 3 * (r / p) ^ d) * ((ρ / p) ^ 2 / K) := by
    rw [Real.rpow_add (by positivity : 0 < r / p), Real.rpow_two]
    field_simp [hp.ne', hr.ne', hρ.ne', hK.ne']
  have hbound : (strips.card : ℝ) * ((ρ / p) ^ 2 / K) ≤
      (K ^ 3 * (r / p) ^ d) * ((ρ / p) ^ 2 / K) :=
    hcount.trans ((mul_le_mul_of_nonneg_right hsupport hK.le).trans_eq hid)
  exact (mul_le_mul_iff_left₀ (by positivity : 0 < (ρ / p) ^ 2 / K)).mp hbound

end Submission.Obl.k4_scalar_grid_polynomial_qualification
