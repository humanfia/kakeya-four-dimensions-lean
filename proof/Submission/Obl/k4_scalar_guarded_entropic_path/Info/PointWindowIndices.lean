import Submission.Obl.k4_scalar_guarded_entropic_path.Info.PointRangeNumerics

/-! A long entropy window leaves a dense tangent grid intact: coarse
and fine rows can be separated by many small grid steps. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

noncomputable section

/-- Half a lookahead window, chosen before the original tangent scale. -/
def pointHalfWindow (κ η : ℝ) (m : ℕ) : ℕ :=
  ⌈4 * ((m : ℝ) + 2) / (κ * η)⌉₊ + 1

theorem pointHalfWindow_pos (κ η : ℝ) (m : ℕ) : 0 < pointHalfWindow κ η m := by
  unfold pointHalfWindow
  omega

theorem pointHalfWindow_gap {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) (m : ℕ) :
    4 * ((m : ℝ) + 2) ≤ κ * ((pointHalfWindow κ η m : ℝ) * η) := by
  have hκη : 0 < κ * η := mul_pos hκ hη
  have hceil : 4 * ((m : ℝ) + 2) / (κ * η) ≤ (pointHalfWindow κ η m : ℝ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (show ⌈4 * ((m : ℝ) + 2) / (κ * η)⌉₊ ≤ pointHalfWindow κ η m by
      unfold pointHalfWindow; omega)
  have h := (div_le_iff₀ hκη).mp hceil
  nlinarith

def pointCoarseIndex {count : ℕ} (q : ℕ) (hq : 0 < q) (hcount : 2 * q ≤ count) : Fin count :=
  ⟨q - 1, by omega⟩

def pointFineIndex {count : ℕ} (q : ℕ) (hq : 0 < q) (hcount : 2 * q ≤ count) : Fin count :=
  ⟨2 * q - 1, by omega⟩

theorem point_indices_ordered {count q : ℕ} (hq : 0 < q) (hcount : 2 * q ≤ count) :
    pointCoarseIndex q hq hcount ≤ pointFineIndex q hq hcount := by
  change q - 1 ≤ 2 * q - 1
  omega

theorem point_fine_future {count q : ℕ} (hq : 0 < q) (hcount : 2 * q ≤ count) :
    (pointFineIndex q hq hcount).val + 1 = 2 * q := by
  change 2 * q - 1 + 1 = 2 * q
  omega

theorem point_coarse_step {count q : ℕ} (hq : 0 < q) (hcount : 2 * q ≤ count) :
    (pointCoarseIndex q hq hcount).val + 1 = q := by
  change q - 1 + 1 = q
  omega

/-- Two actual depths close to the chosen grid positions have both the
coarse fit margin and the duration gap required by the point-range theorem. -/
theorem point_window_depth_gaps {κ A scale error v rc rf : ℝ} {m : ℕ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hA : 0 ≤ A) (hscale : 0 ≤ scale)
    (herror : 0 ≤ error) (herrorScale : error ≤ scale) (hv : v ≤ scale)
    (hgap : 4 * ((m : ℝ) + 2) ≤ κ * A)
    (hcoarse : |rc - scale * A| ≤ error)
    (hfine : |rf - 2 * scale * A| ≤ error) :
    scale * ((m : ℝ) + 1) ≤ rc ∧
      scale * ((m : ℝ) + 1) ≤ κ * (rf - rc) - 2 * v := by
  have hAκ : κ * A ≤ A := by nlinarith
  have hAmin : 4 * ((m : ℝ) + 2) ≤ A := hgap.trans hAκ
  have hmass := mul_le_mul_of_nonneg_left hgap hscale
  have hcoarseMass := mul_le_mul_of_nonneg_left hAmin hscale
  have hκerror : κ * error ≤ error := by nlinarith
  have hc := abs_le.mp hcoarse
  have hf := abs_le.mp hfine
  have hdifference : scale * A - 2 * error ≤ rf - rc := by linarith
  have htime := mul_le_mul_of_nonneg_left hdifference hκ.le
  constructor <;> nlinarith

/-- The spare one-depth margin in StageLayout absorbs both grid errors
and the allowance in the two calibrated block counts. -/
theorem point_depth_gaps_of_margins {κ scale error v idealC idealF rc rf : ℝ} {m : ℕ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (herror : 0 ≤ error) (herrorScale : error ≤ scale)
    (hbudget : 2 * error + 2 * v ≤ scale)
    (hcoarseIdeal : scale * ((m : ℝ) + 2) ≤ idealC)
    (hgapIdeal : scale * ((m : ℝ) + 2) ≤ κ * (idealF - idealC))
    (hcoarse : |rc - idealC| ≤ error) (hfine : |rf - idealF| ≤ error) :
    scale * ((m : ℝ) + 1) ≤ rc ∧
      scale * ((m : ℝ) + 1) ≤ κ * (rf - rc) - 2 * v := by
  have hc := abs_le.mp hcoarse
  have hf := abs_le.mp hfine
  have hdiff : idealF - idealC - 2 * error ≤ rf - rc := by linarith
  have htime := mul_le_mul_of_nonneg_left hdiff hκ.le
  have hκerror : κ * error ≤ error := by nlinarith
  constructor <;> nlinarith

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
