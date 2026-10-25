import Submission.Obl.k4_horizontal_wide_interval_return.Match.CompareSheets

/-!
# Elementary geometry of normalized sheets

`quad2` Lipschitz and difference bounds, and the strip coordinate `etaFun` of a base point,
in which a piece's normalized sheet reproduces its polynomial exactly.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.Core

open Submission.Obl.k4_horizontal_wide_interval_return.MatchGML2D
open Submission.Obl.k4_horizontal_wide_interval_return.CompareSheets

noncomputable section

theorem quad2_smul (c : ℝ) (F : Fin 6 → ℝ) (t η : ℝ) :
    quad2 (c • F) t η = c * quad2 F t η := by
  simp only [quad2, Pi.smul_apply, smul_eq_mul]; ring

theorem quad2_sub (F F' : Fin 6 → ℝ) (t η : ℝ) :
    quad2 F t η - quad2 F' t η = quad2 (F - F') t η := by
  simp only [quad2, Pi.sub_apply]; ring

/-- Values on the unit square are controlled by the coefficient sup. -/
theorem abs_quad2_le {F : Fin 6 → ℝ} {X : ℝ} (hF : ∀ k, |F k| ≤ X) {t η : ℝ}
    (ht : |t| ≤ 1) (hη : |η| ≤ 1) : |quad2 F t η| ≤ 6 * X := by
  have hX : 0 ≤ X := (abs_nonneg _).trans (hF 0)
  have hm : ∀ (k : Fin 6) (m : ℝ), |m| ≤ 1 → |F k * m| ≤ X := fun k m hm => by
    rw [abs_mul]; nlinarith [abs_nonneg (F k), abs_nonneg m, hF k]
  have h1 := hm 1 t ht
  have h2 := hm 2 η hη
  have h3 := hm 3 (t ^ 2) (by rw [abs_pow]; nlinarith [abs_nonneg t])
  have h4 := hm 4 (t * η) (by rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg η])
  have h5 := hm 5 (η ^ 2) (by rw [abs_pow]; nlinarith [abs_nonneg η])
  have h0 := hF 0
  unfold quad2
  calc |F 0 + F 1 * t + F 2 * η + F 3 * t ^ 2 + F 4 * (t * η) + F 5 * η ^ 2|
      ≤ |F 0| + |F 1 * t| + |F 2 * η| + |F 3 * t ^ 2| + |F 4 * (t * η)| + |F 5 * η ^ 2| := by
        have := abs_add_le (F 0 + F 1 * t + F 2 * η + F 3 * t ^ 2 + F 4 * (t * η)) (F 5 * η ^ 2)
        have := abs_add_le (F 0 + F 1 * t + F 2 * η + F 3 * t ^ 2) (F 4 * (t * η))
        have := abs_add_le (F 0 + F 1 * t + F 2 * η) (F 3 * t ^ 2)
        have := abs_add_le (F 0 + F 1 * t) (F 2 * η)
        have := abs_add_le (F 0) (F 1 * t)
        linarith
    _ ≤ 6 * X := by linarith

/-- Lipschitz bound of a two-variable quadratic on a box. -/
theorem quad2_lipschitz {F : Fin 6 → ℝ} {X L : ℝ} (hF : ∀ k, |F k| ≤ X) {t t' η η' : ℝ}
    (ht : |t| ≤ L) (ht' : |t'| ≤ L) (hη : |η| ≤ L) (hη' : |η'| ≤ L) :
    |quad2 F t η - quad2 F t' η'| ≤ X * (1 + 3 * L) * (|t - t'| + |η - η'|) := by
  have hX : 0 ≤ X := (abs_nonneg _).trans (hF 0)
  have hL : 0 ≤ L := (abs_nonneg _).trans ht
  have e : quad2 F t η - quad2 F t' η' =
      F 1 * (t - t') + F 2 * (η - η') + F 3 * ((t + t') * (t - t')) +
        F 4 * (t * (η - η') + η' * (t - t')) + F 5 * ((η + η') * (η - η')) := by
    simp only [quad2]; ring
  rw [e]
  set a := |t - t'|
  set c := |η - η'|
  have ha : 0 ≤ a := abs_nonneg _
  have hc : 0 ≤ c := abs_nonneg _
  have b1 : |F 1 * (t - t')| ≤ X * a := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hF 1) ha
  have b2 : |F 2 * (η - η')| ≤ X * c := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hF 2) hc
  have b3 : |F 3 * ((t + t') * (t - t'))| ≤ X * (2 * L * a) := by
    rw [abs_mul, abs_mul]
    have : |t + t'| ≤ 2 * L := (abs_add_le _ _).trans (by linarith)
    exact mul_le_mul (hF 3) (mul_le_mul_of_nonneg_right this ha) (by positivity) hX
  have b4 : |F 4 * (t * (η - η') + η' * (t - t'))| ≤ X * (L * c + L * a) := by
    rw [abs_mul]
    have : |t * (η - η') + η' * (t - t')| ≤ L * c + L * a := by
      calc _ ≤ |t * (η - η')| + |η' * (t - t')| := abs_add_le _ _
        _ = |t| * c + |η'| * a := by rw [abs_mul, abs_mul]
        _ ≤ L * c + L * a := by gcongr
    exact mul_le_mul (hF 4) this (by positivity) hX
  have b5 : |F 5 * ((η + η') * (η - η'))| ≤ X * (2 * L * c) := by
    rw [abs_mul, abs_mul]
    have : |η + η'| ≤ 2 * L := (abs_add_le _ _).trans (by linarith)
    exact mul_le_mul (hF 5) (mul_le_mul_of_nonneg_right this hc) (by positivity) hX
  have tri := abs_add_le (F 1 * (t - t') + F 2 * (η - η') + F 3 * ((t + t') * (t - t')) +
    F 4 * (t * (η - η') + η' * (t - t'))) (F 5 * ((η + η') * (η - η')))
  have tri2 := abs_add_le (F 1 * (t - t') + F 2 * (η - η') + F 3 * ((t + t') * (t - t')))
    (F 4 * (t * (η - η') + η' * (t - t')))
  have tri3 := abs_add_le (F 1 * (t - t') + F 2 * (η - η')) (F 3 * ((t + t') * (t - t')))
  have tri4 := abs_add_le (F 1 * (t - t')) (F 2 * (η - η'))
  nlinarith

/-- The strip coordinate of a base point `(t, Y)` of the strip `Y = y₀ + t v + D (4η - 2)`. -/
def etaFun (y₀ v D t Y : ℝ) : ℝ := (Y - y₀ - t * v) / (4 * D) + 1 / 2

theorem strip_etaFun {y₀ v D : ℝ} (hD : D ≠ 0) (t Y : ℝ) :
    y₀ + t * v + D * (4 * etaFun y₀ v D t Y - 2) = Y := by
  unfold etaFun; field_simp; ring

theorem quad2_sheetCoeff_etaFun {G : MvPolynomial (Fin 2) ℝ} (hG : G.totalDegree ≤ 2)
    {y₀ v D : ℝ} (hD : D ≠ 0) (t Y : ℝ) :
    quad2 (sheetCoeff G y₀ v D) t (etaFun y₀ v D t Y) = MvPolynomial.eval ![t, Y] G := by
  rw [quad2_sheetCoeff hG, strip_etaFun hD]

theorem etaFun_sub {y₀ v D : ℝ} (hD : 0 < D) (t Y t' Y' : ℝ) :
    |etaFun y₀ v D t Y - etaFun y₀ v D t' Y'| ≤ (|Y - Y'| + |v| * |t - t'|) / (4 * D) := by
  unfold etaFun
  have e : (Y - y₀ - t * v) / (4 * D) + 1 / 2 - ((Y' - y₀ - t' * v) / (4 * D) + 1 / 2) =
      ((Y - Y') - v * (t - t')) / (4 * D) := by field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : 0 < 4 * D)]
  gcongr
  calc |Y - Y' - v * (t - t')| ≤ |Y - Y'| + |v * (t - t')| := abs_sub _ _
    _ = |Y - Y'| + |v| * |t - t'| := by rw [abs_mul]

end

end Submission.Obl.k4_horizontal_wide_interval_return.Core
