/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/CommonHorizontalBox.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o218, session x0760, commit ce93c8df6e603b8044f968da8a9087dc728f3bb6,
   `Submission/Obl/k4_horizontal_endpoint_wide_return/CommonHorizontalBox.lean`. -/
import Mathlib

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

/-- A native horizontal box with time width h, first spatial width K*h and
transverse width K*h squared. -/
def horizontalNativeBox (K h tc z₀ z₁ y₀ y₁ θ : ℝ) : Set (Fin 3 → ℝ) :=
  {p | |p 0 - tc| ≤ h ∧ |p 1 - (z₀ + p 0 * z₁)| ≤ K * h ∧
    |p 2 - (y₀ + p 0 * y₁ + θ * p 1)| ≤ K * h ^ 2}

/-- One contact with a horizontal reference motion puts the whole native box
inside one common enlargement. Thus witness masses can be counted on whole boxes,
including when their contact points come from different parameter assignments. -/
theorem horizontal_box_common_from_contact {K h tc z₀ z₁ y₀ y₁ θ pc r vc : ℝ}
    (hK : 1 ≤ K) (hh : 0 < h) (hz₁ : |z₁| ≤ K) (hvc : |vc| ≤ K)
    (hplane : |θ - tc| ≤ K * h) (hhorizontal : |y₁ + z₀ + tc * z₁| ≤ K * h)
    {w p : Fin 3 → ℝ} (hw : w ∈ horizontalNativeBox K h tc z₀ z₁ y₀ y₁ θ)
    (hp : p ∈ horizontalNativeBox K h tc z₀ z₁ y₀ y₁ θ)
    (hwZ : |w 1 - (pc + w 0 * vc)| ≤ h)
    (hwY : |w 2 - (r - w 0 * pc) - tc * (w 1 - (pc + w 0 * vc))| ≤ h ^ 2) :
    |p 1 - (pc + p 0 * vc)| ≤ 7 * K * h ∧
    |p 2 - (r - p 0 * pc) - tc * (p 1 - (pc + p 0 * vc))| ≤ 20 * K ^ 2 * h ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have hKh : 0 ≤ K * h := mul_nonneg hK0 hh.le
  have hhK : h ≤ K * h := by nlinarith
  obtain ⟨hwt, hwz, hwy⟩ := hw
  obtain ⟨hpt, hpz, hpy⟩ := hp
  let c := fun t : ℝ => z₀ + t * z₁ - (pc + t * vc)
  have hdt : |p 0 - w 0| ≤ 2 * h := by
    calc
      _ = |(p 0 - tc) - (w 0 - tc)| := by congr 1; ring
      _ ≤ |p 0 - tc| + |w 0 - tc| := abs_sub _ _
      _ ≤ h + h := add_le_add hpt hwt
      _ = _ := by ring
  have hvel : |z₁ - vc| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
  have hcW : |c (w 0)| ≤ (K + 1) * h := by
    calc
      _ ≤ |z₀ + w 0 * z₁ - w 1| + |w 1 - (pc + w 0 * vc)| := abs_sub_le _ _ _
      _ ≤ K * h + h := add_le_add (by simpa only [abs_sub_comm] using hwz) hwZ
      _ = _ := by ring
  have hc (t : ℝ) : |c t| ≤ (K + 1) * h + |t - w 0| * (2 * K) := by
    have hid : c t = c (w 0) + (t - w 0) * (z₁ - vc) := by dsimp [c]; ring
    rw [hid]
    calc
      _ ≤ |c (w 0)| + |(t - w 0) * (z₁ - vc)| := abs_add_le _ _
      _ = |c (w 0)| + |t - w 0| * |z₁ - vc| := by rw [abs_mul]
      _ ≤ _ := add_le_add hcW (mul_le_mul_of_nonneg_left hvel (abs_nonneg _))
  have hcP : |c (p 0)| ≤ (5 * K + 1) * h := by
    calc
      _ ≤ (K + 1) * h + |p 0 - w 0| * (2 * K) := hc _
      _ ≤ (K + 1) * h + (2 * h) * (2 * K) := by gcongr
      _ = _ := by ring
  have hcT : |c tc| ≤ 4 * K * h := by
    have htc : |tc - w 0| ≤ h := by simpa only [abs_sub_comm] using hwt
    calc
      _ ≤ (K + 1) * h + |tc - w 0| * (2 * K) := hc _
      _ ≤ (K + 1) * h + h * (2 * K) := by gcongr
      _ = 3 * K * h + h := by ring
      _ ≤ _ := by linarith
  have hZ : |p 1 - (pc + p 0 * vc)| ≤ 7 * K * h := by
    calc
      _ ≤ |p 1 - (z₀ + p 0 * z₁)| + |c (p 0)| := abs_sub_le _ _ _
      _ ≤ K * h + (5 * K + 1) * h := add_le_add hpz hcP
      _ = 6 * K * h + h := by ring
      _ ≤ _ := by linarith
  have hA : |y₁ + pc + tc * vc| ≤ 5 * K * h := by
    have hid : y₁ + pc + tc * vc = (y₁ + z₀ + tc * z₁) - c tc := by dsimp [c]; ring
    rw [hid]
    exact (abs_sub _ _).trans ((add_le_add hhorizontal hcT).trans_eq (by ring))
  have hZw : |p 1 - w 1| ≤ 4 * K * h := by
    have hcenters : |(z₀ + p 0 * z₁) - (z₀ + w 0 * z₁)| ≤ (2 * h) * K := by
      have hid : (z₀ + p 0 * z₁) - (z₀ + w 0 * z₁) = (p 0 - w 0) * z₁ := by ring
      rw [hid, abs_mul]
      exact mul_le_mul hdt hz₁ (abs_nonneg _) (by positivity)
    calc
      _ ≤ |p 1 - (z₀ + p 0 * z₁)| + |(z₀ + p 0 * z₁) - w 1| := abs_sub_le _ _ _
      _ ≤ K * h + (|(z₀ + p 0 * z₁) - (z₀ + w 0 * z₁)| + |(z₀ + w 0 * z₁) - w 1|) :=
        add_le_add hpz (abs_sub_le _ _ _)
      _ ≤ K * h + ((2 * h) * K + K * h) :=
        add_le_add le_rfl (add_le_add hcenters (by simpa only [abs_sub_comm] using hwz))
      _ = _ := by ring
  let g := fun t Z : ℝ => (y₀ + t * y₁ + θ * Z) -
    ((r - t * pc) + tc * (Z - (pc + t * vc)))
  have hgW : |g (w 0) (w 1)| ≤ (K + 1) * h ^ 2 := by
    calc
      _ ≤ |(y₀ + w 0 * y₁ + θ * w 1) - w 2| +
          |w 2 - ((r - w 0 * pc) + tc * (w 1 - (pc + w 0 * vc)))| := abs_sub_le _ _ _
      _ ≤ K * h ^ 2 + h ^ 2 := add_le_add
        (by simpa only [abs_sub_comm] using hwy) (by simpa only [sub_add_eq_sub_sub] using hwY)
      _ = _ := by ring
  have hgdelta : |g (p 0) (p 1) - g (w 0) (w 1)| ≤
      (2 * h) * (5 * K * h) + (K * h) * (4 * K * h) := by
    have hid : g (p 0) (p 1) - g (w 0) (w 1) =
        (p 0 - w 0) * (y₁ + pc + tc * vc) + (θ - tc) * (p 1 - w 1) := by dsimp [g]; ring
    rw [hid]
    calc
      _ ≤ |(p 0 - w 0) * (y₁ + pc + tc * vc)| + |(θ - tc) * (p 1 - w 1)| := abs_add_le _ _
      _ = |p 0 - w 0| * |y₁ + pc + tc * vc| + |θ - tc| * |p 1 - w 1| := by rw [abs_mul, abs_mul]
      _ ≤ _ := add_le_add
        (mul_le_mul hdt hA (abs_nonneg _) (by positivity))
        (mul_le_mul hplane hZw (abs_nonneg _) hKh)
  refine ⟨hZ, ?_⟩
  have hid : p 2 - (r - p 0 * pc) - tc * (p 1 - (pc + p 0 * vc)) =
      (p 2 - (y₀ + p 0 * y₁ + θ * p 1)) +
        g (w 0) (w 1) + (g (p 0) (p 1) - g (w 0) (w 1)) := by dsimp [g]; ring
  rw [hid]
  have hcoef : 4 * K ^ 2 + 12 * K + 1 ≤ 20 * K ^ 2 := by
    have hKsq : K ≤ K ^ 2 := by nlinarith
    have hKsq1 : 1 ≤ K ^ 2 := by nlinarith
    nlinarith
  calc
    _ ≤ (|p 2 - (y₀ + p 0 * y₁ + θ * p 1)| + |g (w 0) (w 1)|) +
        |g (p 0) (p 1) - g (w 0) (w 1)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (K * h ^ 2 + (K + 1) * h ^ 2) +
        ((2 * h) * (5 * K * h) + (K * h) * (4 * K * h)) :=
      add_le_add (add_le_add hpy hgW) hgdelta
    _ = (4 * K ^ 2 + 12 * K + 1) * h ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

end Submission.Obl.k4_subcritical_corrected_scalar_charts
