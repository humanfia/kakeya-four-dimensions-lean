-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.LineCounting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.CapIntersection

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

attribute [local instance] Classical.propDecidable

def IndexedLineFrostman {J : Type*} [Fintype J] (δ C ζ : ℝ) (g : J → Plane) : Prop :=
  ∀ (u : Plane) (a r : ℝ), ‖u‖ = 1 → δ ≤ r →
    ((Finset.univ.filter (fun j => |inner ℝ (g j) u - a| < r)).card : ℝ) ≤
      (C * r) ^ ζ * (Fintype.card J : ℝ)

theorem IndexedLineFrostman.joining_line_count {J : Type*} [Fintype J]
    {g : J → Plane} {δ C ζ s : ℝ} (hG : IndexedLineFrostman δ C ζ g)
    (b b' : Plane) (hbb' : b ≠ b') (hδs : δ ≤ s) :
    ((Finset.univ.filter (fun j => |area (g j - b) (b' - b)| < s * ‖b' - b‖)).card : ℝ) ≤
      (C * s) ^ ζ * (Fintype.card J : ℝ) := by
  classical
  let v := b' - b
  let u := ‖v‖⁻¹ • perp v
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hbb'.symm)
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, perp_norm, Real.norm_of_nonneg (inv_nonneg.mpr hv.le), hv.ne']
  have hid (j : J) : |inner ℝ (g j) u - inner ℝ b u| = |area (g j - b) v| / ‖v‖ := by
    rw [← inner_sub_left]
    simp only [u, real_inner_smul_right, abs_mul, abs_inv, abs_of_pos hv, area]
    ring
  have hsub : Finset.univ.filter (fun j => |area (g j - b) (b' - b)| < s * ‖b' - b‖) ⊆
      Finset.univ.filter (fun j => |inner ℝ (g j) u - inner ℝ b u| < s) := by
    intro j hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hid]
    exact (div_lt_iff₀ hv).mpr (Finset.mem_filter.mp hj).2
  have hc : ((Finset.univ.filter (fun j => |area (g j - b) (b' - b)| < s * ‖b' - b‖)).card : ℝ) ≤
      ((Finset.univ.filter (fun j => |inner ℝ (g j) u - inner ℝ b u| < s)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (hG u (inner ℝ b u) s hu hδs)

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
