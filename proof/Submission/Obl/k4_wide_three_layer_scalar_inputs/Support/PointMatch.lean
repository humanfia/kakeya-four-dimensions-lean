import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.PolyLip

set_option linter.unusedVariables false

/-!
# Two incidences of one fine state match

Two incidences in the same fine cell (normalized base, transverse and residual coordinates)
whose residuals follow their predictors plus offsets to precision `H N^-u` give, at a reference
base point near the first, two predictor polynomials in the transverse variable that agree at
the first transverse value up to an offset of the second, within an explicit width.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

noncomputable section

theorem abs_sub_lt_of_floor_eq {a b r : ℝ} (hr : 0 < r) (h : ⌊a / r⌋ = ⌊b / r⌋) : |a - b| < r := by
  have h1 := Int.floor_le (a / r)
  have h2 := Int.lt_floor_add_one (a / r)
  have h3 := Int.floor_le (b / r)
  have h4 := Int.lt_floor_add_one (b / r)
  rw [h] at h1 h2
  have : |a / r - b / r| < 1 := by rw [abs_lt]; constructor <;> linarith
  rwa [← sub_div, abs_div, abs_of_pos hr, div_lt_one hr] at this

theorem abs_sub_floor_mul_le {x r : ℝ} (hr : 0 < r) : |x - (⌊x / r⌋ : ℝ) * r| ≤ r := by
  have h1 := Int.floor_le (x / r)
  have h2 := Int.lt_floor_add_one (x / r)
  rw [le_div_iff₀ hr] at h1
  rw [div_lt_iff₀ hr] at h2
  rw [abs_le]; constructor <;> nlinarith

/-- **Pointwise matching.** -/
theorem point_match {pc pc' : Fin 6 → ℝ} {tc tc' : Fin 4 → ℝ} {H X Y Ub : ℝ}
    (hp : ∀ e, |pc e| ≤ H) (hτ : ∀ e, |tc e| ≤ H) (hp' : ∀ e, |pc' e| ≤ H)
    (hτ' : ∀ e, |tc' e| ≤ H)
    {x y U X3 D x' y' U' X3' D' xr yr ρ1 ρ2 δz δU δX η : ℝ} (hη : 0 < η)
    (hfit : |X3 - quadZ pc x y - D - transv tc x y U| ≤ H * η)
    (hfit' : |X3' - quadZ pc' x' y' - D' - transv tc' x' y' U'| ≤ H * η)
    (hx : |x - x'| ≤ δz) (hy : |y - y'| ≤ δz) (hU : |U - U'| ≤ δU) (hX : |X3 - X3'| ≤ δX)
    (hxr : |x - xr| ≤ ρ1) (hyr : |y - yr| ≤ ρ2)
    (hbx : |x| ≤ X) (hbx' : |x'| ≤ X) (hbxr : |xr| ≤ X) (hby : |y| ≤ Y) (hby' : |y'| ≤ Y)
    (hbyr : |yr| ≤ Y) (hbU : |U| ≤ Ub) (hbU' : |U'| ≤ Ub) :
    |(quadZ pc xr yr + (⌊D / η⌋ : ℝ) * η - quadZ pc' xr yr) +
        (lin1 tc xr yr - lin1 tc' xr yr) * U + (tc 3 - tc' 3) * U ^ 2 -
        (⌊D' / η⌋ : ℝ) * η| ≤
      (2 * H + 2) * η + δX + H * ((1 + 2 * X + Y + Ub) * (2 * ρ1 + δz) +
        (1 + X + 2 * Y + Ub) * (2 * ρ2 + δz) + (1 + X + Y + 2 * Ub) * δU) := by
  have hid : (quadZ pc xr yr + (⌊D / η⌋ : ℝ) * η - quadZ pc' xr yr) +
        (lin1 tc xr yr - lin1 tc' xr yr) * U + (tc 3 - tc' 3) * U ^ 2 - (⌊D' / η⌋ : ℝ) * η =
      (predQ pc tc xr yr U - predQ pc tc x y U) +
      (X3 - X3') - (X3 - quadZ pc x y - D - transv tc x y U) +
      (X3' - quadZ pc' x' y' - D' - transv tc' x' y' U') +
      ((⌊D / η⌋ : ℝ) * η - D) - ((⌊D' / η⌋ : ℝ) * η - D') -
      (predQ pc' tc' xr yr U - predQ pc' tc' x' y' U') := by
    simp only [predQ, transv, lin1]; ring
  rw [hid]
  have hA := predQ_diff hp hτ hbxr hbx hbyr hby hbU hbU (x := xr) (y := yr) (U := U)
    (x' := x) (y' := y) (U' := U)
  have hB := predQ_diff hp' hτ' hbxr hbx' hbyr hby' hbU hbU' (x := xr) (y := yr) (U := U)
    (x' := x') (y' := y') (U' := U')
  have hd1 : |(⌊D / η⌋ : ℝ) * η - D| ≤ η := by rw [abs_sub_comm]; exact abs_sub_floor_mul_le hη
  have hd2 : |(⌊D' / η⌋ : ℝ) * η - D'| ≤ η := by rw [abs_sub_comm]; exact abs_sub_floor_mul_le hη
  have hH : 0 ≤ H := (abs_nonneg _).trans (hp 0)
  have hX0 : 0 ≤ X := (abs_nonneg _).trans hbx
  have hY0 : 0 ≤ Y := (abs_nonneg _).trans hby
  have hU0 : 0 ≤ Ub := (abs_nonneg _).trans hbU
  have e1 : |xr - x| ≤ ρ1 := by rw [abs_sub_comm]; exact hxr
  have e2 : |yr - y| ≤ ρ2 := by rw [abs_sub_comm]; exact hyr
  have e3 : |xr - x'| ≤ ρ1 + δz := by
    calc |xr - x'| = |(xr - x) + (x - x')| := by ring_nf
      _ ≤ |xr - x| + |x - x'| := abs_add_le _ _
      _ ≤ ρ1 + δz := add_le_add e1 hx
  have e4 : |yr - y'| ≤ ρ2 + δz := by
    calc |yr - y'| = |(yr - y) + (y - y')| := by ring_nf
      _ ≤ |yr - y| + |y - y'| := abs_add_le _ _
      _ ≤ ρ2 + δz := add_le_add e2 hy
  have hA' : |predQ pc tc xr yr U - predQ pc tc x y U| ≤
      H * ((1 + 2 * X + Y + Ub) * ρ1 + (1 + X + 2 * Y + Ub) * ρ2) := by
    refine hA.trans ?_
    simp only [sub_self, abs_zero, mul_zero, add_zero]
    gcongr
  have hB' : |predQ pc' tc' xr yr U - predQ pc' tc' x' y' U'| ≤
      H * ((1 + 2 * X + Y + Ub) * (ρ1 + δz) + (1 + X + 2 * Y + Ub) * (ρ2 + δz) +
        (1 + X + Y + 2 * Ub) * δU) := by
    refine hB.trans ?_
    gcongr
  have htri : ∀ a b c d e f g : ℝ, |a + b - c + d + e - f - g| ≤
      |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
    intro a b c d e f g
    have := abs_add_le (a + b - c + d + e - f) (-g)
    have := abs_add_le (a + b - c + d + e) (-f)
    have := abs_add_le (a + b - c + d) e
    have := abs_add_le (a + b - c) d
    have := abs_add_le (a + b) (-c)
    have := abs_add_le a b
    simp only [abs_neg, ← sub_eq_add_neg] at *
    linarith
  refine (htri _ _ _ _ _ _ _).trans ?_
  have := hA'; have := hB'
  nlinarith [hfit, hfit', hX, hd1, hd2]

/-- The nonconstant coefficient gap moves little along the base. -/
theorem gap_move {tc tc' : Fin 4 → ℝ} {H : ℝ} (hτ : ∀ e, |tc e| ≤ H) (hτ' : ∀ e, |tc' e| ≤ H)
    (x y x' y' : ℝ) :
    |lin1 tc x y - lin1 tc' x y| + |tc 3 - tc' 3| ≤
      |lin1 tc x' y' - lin1 tc' x' y'| + |tc 3 - tc' 3| + 2 * H * (|x - x'| + |y - y'|) := by
  have h := lin1_diff hτ hτ' x y x' y'
  have : |lin1 tc x y - lin1 tc' x y| ≤ |lin1 tc x' y' - lin1 tc' x' y'| +
      |(lin1 tc x y - lin1 tc' x y) - (lin1 tc x' y' - lin1 tc' x' y')| := by
    have := abs_sub_abs_le_abs_sub (lin1 tc x y - lin1 tc' x y) (lin1 tc x' y' - lin1 tc' x' y')
    linarith
  linarith

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
