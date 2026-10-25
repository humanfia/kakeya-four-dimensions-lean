-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.Normalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.ZoomFrostman

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem InUnitSquare.dist_le_two {F : Set Plane} (hF : InUnitSquare F)
    {x y : Plane} (hx : x ∈ F) (hy : y ∈ F) : dist x y ≤ 2 := by
  have hx0 := hF x hx 0
  have hx1 := hF x hx 1
  have hy0 := hF y hy 0
  have hy1 := hF y hy 1
  have h0 : |(x - y) 0| ≤ 1 := by change |x 0 - y 0| ≤ 1; rw [abs_le]; constructor <;> linarith
  have h1 : |(x - y) 1| ≤ 1 := by change |x 1 - y 1| ≤ 1; rw [abs_le]; constructor <;> linarith
  have hn := EuclideanSpace.real_norm_sq_eq (x - y)
  simp only [Fin.sum_univ_two] at hn
  rw [dist_eq_norm]
  nlinarith [(sq_le_one_iff_abs_le_one _).mpr h0, (sq_le_one_iff_abs_le_one _).mpr h1,
    norm_nonneg (x - y)]

/-- Normalize the three coarse balls by expanding similarities. The first
center has norm two; the two other centers become zero and a point of norm two. -/
theorem exists_normalizing_zooms {r q : ℝ} {a b c : Plane}
    (hr : 0 < r) (hq : 0 ≤ q) (hqsmall : 1000 * q ≤ r)
    (ha : r / 2 ≤ ‖a‖) (hbc : r / 2 ≤ dist b c)
    (ha2 : ‖a‖ ≤ 2) (hbc2 : dist b c ≤ 2) :
    ∃ α β : ℝ, 1 ≤ α ∧ 1 ≤ β ∧ α ≤ 4 / r ∧ β ≤ 4 / r ∧
      ‖zoom 0 α a‖ = 2 ∧ zoom b β b = 0 ∧ ‖zoom b β c‖ = 2 ∧
      α * q ≤ 1 / 100 ∧ β * q ≤ 1 / 100 := by
  have hapos : 0 < ‖a‖ := (half_pos hr).trans_le ha
  have hbcpos : 0 < dist b c := (half_pos hr).trans_le hbc
  let α := 2 / ‖a‖
  let β := 2 / dist b c
  have hα : 1 ≤ α := (le_div_iff₀ hapos).mpr (by simpa using ha2)
  have hβ : 1 ≤ β := (le_div_iff₀ hbcpos).mpr (by simpa using hbc2)
  have hαpos : 0 < α := zero_lt_one.trans_le hα
  have hβpos : 0 < β := zero_lt_one.trans_le hβ
  have hαup : α ≤ 4 / r := (div_le_div_iff₀ hapos hr).mpr (by nlinarith)
  have hβup : β ≤ 4 / r := (div_le_div_iff₀ hbcpos hr).mpr (by nlinarith)
  have hqratio : q / r ≤ 1 / 1000 := (div_le_iff₀ hr).mpr (by linarith)
  have hsmall (s : ℝ) (hs : s ≤ 4 / r) : s * q ≤ 1 / 100 := by
    calc s * q ≤ (4 / r) * q := mul_le_mul_of_nonneg_right hs hq
      _ = 4 * (q / r) := by ring
      _ ≤ 4 * (1 / 1000) := mul_le_mul_of_nonneg_left hqratio (by norm_num)
      _ ≤ 1 / 100 := by norm_num
  refine ⟨α, β, hα, hβ, hαup, hβup, ?_, ?_, ?_, hsmall α hαup, hsmall β hβup⟩
  · simp only [zoom, sub_zero, norm_smul, Real.norm_of_nonneg hαpos.le]
    exact div_mul_cancel₀ _ hapos.ne'
  · simp [zoom]
  · rw [zoom, norm_smul, Real.norm_of_nonneg hβpos.le, ← dist_eq_norm, dist_comm c b]
    exact div_mul_cancel₀ _ hbcpos.ne'

theorem norm_zoom_le_four_of_near {k q : ℝ} {b c x : Plane} (hk : 0 ≤ k)
    (hc : ‖zoom b k c‖ ≤ 2) (hx : dist x c ≤ q) (hsmall : k * q ≤ 1 / 100) :
    ‖zoom b k x‖ ≤ 4 := by
  have hd : dist (zoom b k x) (zoom b k c) ≤ 1 / 100 := by
    rw [zoom_dist b hk]
    exact (mul_le_mul_of_nonneg_left hx hk).trans hsmall
  have ht := dist_triangle (zoom b k x) (zoom b k c) 0
  simp only [dist_zero_right] at ht
  linarith

end WangZahlLot.Obl.wz_separated_projection_dichotomy
