/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Match/CompareSheets.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
/- Adapted within this LOT tree (g-oai-074) from o227 `k4_horizontal_three_projection_wide_return`,
session x0788, branch x0788, commit d1137a70, file
Submission/Obl/k4_horizontal_three_projection_wide_return/CompareSheets.lean (namespace renamed into o250's). -/
import Mathlib
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticCoefficients
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Match.MatchGML2D

/-!
# Normalized sheets of projected layer cells

A layer cell stores a quadratic `G(t, Y)` controlled on the moving strip
`Y = y₀ + t v + D w`, `|w| ≤ 1`. In the variable `η = (w + 2) / 4` its coefficient
vector is `sheetCoeff G y₀ v D`. A trajectory with intercept `b₁ ∈ [y₀, y₀ + D)` and
slope within `ζ` of `v` sits at `η = etaOf y₀ D b₁ ∈ [1/2, 3/4)`, and the cell's fit
of the hidden coordinate transfers to the sheet with an extra error `40 H ζ / D`.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.CompareSheets

open MatchGML2D
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

lemma quad2_eq (F : Fin 6 → ℝ) (t y : ℝ) : quad2 F t y = quadraticValue F t y := by
  simp [quad2, quadraticValue]

/-- Coefficients of `G` over the moving strip, in the strip variable `w`. -/
noncomputable def stripCoeff (G : MvPolynomial (Fin 2) ℝ) (y₀ v D : ℝ) : Fin 6 → ℝ :=
  if h : G.totalDegree ≤ 2 then
    Classical.choose (isQuad2_affine_second (isQuad2_eval G h) y₀ v D)
  else 0

lemma stripCoeff_spec {G : MvPolynomial (Fin 2) ℝ} (hG : G.totalDegree ≤ 2) (y₀ v D t w : ℝ) :
    MvPolynomial.eval ![t, y₀ + t * v + D * w] G = quadraticValue (stripCoeff G y₀ v D) t w := by
  unfold stripCoeff
  rw [dif_pos hG]
  have := Classical.choose_spec (isQuad2_affine_second (isQuad2_eval G hG) y₀ v D) t w
  simpa [quadraticValue] using this

lemma stripCoeff_bound {G : MvPolynomial (Fin 2) ℝ} (hG : G.totalDegree ≤ 2) {y₀ v D H : ℝ}
    (hb : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ w ∈ Set.Icc (-1:ℝ) 1,
      |MvPolynomial.eval ![t, y₀ + t * v + D * w] G| ≤ H) :
    ∀ k, |stripCoeff G y₀ v D k| ≤ 8 * H :=
  quadratic_coefficients_bound (fun t ht w hw => by rw [← stripCoeff_spec hG]; exact hb t ht w hw)

/-- Change of variable `w = 4 η - 2`. -/
def toEta (c : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![c 0 - 2 * c 2 + 4 * c 5, c 1 - 2 * c 4, 4 * c 2 - 16 * c 5, c 3, 4 * c 4, 16 * c 5]

lemma quad2_toEta (c : Fin 6 → ℝ) (t η : ℝ) :
    quad2 (toEta c) t η = quadraticValue c t (4 * η - 2) := by
  simp [quad2, toEta, quadraticValue]; ring

lemma toEta_bound {c : Fin 6 → ℝ} {X : ℝ} (hc : ∀ k, |c k| ≤ X) : ∀ k, |toEta c k| ≤ 20 * X := by
  have h0 := abs_le.mp (hc 0); have h1 := abs_le.mp (hc 1); have h2 := abs_le.mp (hc 2)
  have h3 := abs_le.mp (hc 3); have h4 := abs_le.mp (hc 4); have h5 := abs_le.mp (hc 5)
  have hX : 0 ≤ X := le_trans (abs_nonneg _) (hc 0)
  have e0 : toEta c 0 = c 0 - 2 * c 2 + 4 * c 5 := rfl
  have e1 : toEta c 1 = c 1 - 2 * c 4 := rfl
  have e2 : toEta c 2 = 4 * c 2 - 16 * c 5 := rfl
  have e3 : toEta c 3 = c 3 := rfl
  have e4 : toEta c 4 = 4 * c 4 := rfl
  have e5 : toEta c 5 = 16 * c 5 := rfl
  intro k
  fin_cases k
  · rw [show ((⟨0, by norm_num⟩ : Fin 6)) = 0 from rfl, e0, abs_le]; constructor <;> linarith
  · rw [show ((⟨1, by norm_num⟩ : Fin 6)) = 1 from rfl, e1, abs_le]; constructor <;> linarith
  · rw [show ((⟨2, by norm_num⟩ : Fin 6)) = 2 from rfl, e2, abs_le]; constructor <;> linarith
  · rw [show ((⟨3, by norm_num⟩ : Fin 6)) = 3 from rfl, e3, abs_le]; constructor <;> linarith
  · rw [show ((⟨4, by norm_num⟩ : Fin 6)) = 4 from rfl, e4, abs_le]; constructor <;> linarith
  · rw [show ((⟨5, by norm_num⟩ : Fin 6)) = 5 from rfl, e5, abs_le]; constructor <;> linarith

/-- The normalized sheet of a cell. -/
noncomputable def sheetCoeff (G : MvPolynomial (Fin 2) ℝ) (y₀ v D : ℝ) : Fin 6 → ℝ :=
  toEta (stripCoeff G y₀ v D)

lemma quad2_sheetCoeff {G : MvPolynomial (Fin 2) ℝ} (hG : G.totalDegree ≤ 2) (y₀ v D t η : ℝ) :
    quad2 (sheetCoeff G y₀ v D) t η = MvPolynomial.eval ![t, y₀ + t * v + D * (4 * η - 2)] G := by
  rw [sheetCoeff, quad2_toEta, stripCoeff_spec hG]

lemma sheetCoeff_bound {G : MvPolynomial (Fin 2) ℝ} (hG : G.totalDegree ≤ 2) {y₀ v D H : ℝ}
    (hb : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ w ∈ Set.Icc (-1:ℝ) 1,
      |MvPolynomial.eval ![t, y₀ + t * v + D * w] G| ≤ H) :
    ∀ k, |sheetCoeff G y₀ v D k| ≤ 160 * H := by
  intro k
  have := toEta_bound (stripCoeff_bound hG hb) k
  unfold sheetCoeff; linarith

/-- The strip coordinate of a trajectory with intercept `b₁`. -/
noncomputable def etaOf (y₀ D b₁ : ℝ) : ℝ := (b₁ - y₀) / (4 * D) + 1 / 2

lemma etaOf_mem {y₀ D b₁ : ℝ} (hD : 0 < D) (h1 : y₀ ≤ b₁) (h2 : b₁ < y₀ + D) :
    etaOf y₀ D b₁ ∈ Set.Icc (1/4 : ℝ) (3/4) := by
  unfold etaOf
  constructor
  · have : 0 ≤ (b₁ - y₀) / (4 * D) := div_nonneg (by linarith) (by positivity)
    linarith
  · have : (b₁ - y₀) / (4 * D) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith

/-- The cell's fit transfers to its normalized sheet along a trajectory. -/
theorem sheet_fit {G : MvPolynomial (Fin 2) ℝ} (hG : G.totalDegree ≤ 2) {y₀ v D H ζ e : ℝ}
    (hD : 0 < D) (hb : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ w ∈ Set.Icc (-1:ℝ) 1,
      |MvPolynomial.eval ![t, y₀ + t * v + D * w] G| ≤ H)
    {b₁ b₄ X : ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (h1 : y₀ ≤ b₁) (h2 : b₁ < y₀ + D) (hζ : |b₄ - v| ≤ ζ) (hζD : ζ ≤ D)
    (hfit : |X - MvPolynomial.eval ![t, b₁ + t * b₄] G| ≤ e) :
    |quad2 (sheetCoeff G y₀ v D) t (etaOf y₀ D b₁) - X| ≤ e + 40 * H * ζ / D := by
  set c := stripCoeff G y₀ v D
  have hc := stripCoeff_bound hG hb
  have hH : 0 ≤ H := by
    have := hb 0 (by norm_num) 0 (by norm_num); exact le_trans (abs_nonneg _) this
  obtain ⟨ht0, ht1⟩ := ht
  set w₁ := (b₁ - y₀) / D
  set w₂ := (b₁ + t * b₄ - y₀ - t * v) / D
  have heta : 4 * etaOf y₀ D b₁ - 2 = w₁ := by
    simp only [etaOf, w₁]; field_simp; ring
  have hsheet : quad2 (sheetCoeff G y₀ v D) t (etaOf y₀ D b₁) = quadraticValue c t w₁ := by
    rw [sheetCoeff, quad2_toEta, heta]
  have hYeq : y₀ + t * v + D * w₂ = b₁ + t * b₄ := by
    simp only [w₂]; field_simp; ring
  have hY : MvPolynomial.eval ![t, b₁ + t * b₄] G = quadraticValue c t w₂ := by
    rw [← hYeq, stripCoeff_spec hG]
  have hw₁ : |w₁| ≤ 1 := by
    simp only [w₁]; rw [abs_le]; constructor
    · rw [le_div_iff₀ hD]; linarith
    · rw [div_le_iff₀ hD]; linarith
  have hdw : |w₁ - w₂| ≤ ζ / D := by
    have : w₁ - w₂ = -(t * (b₄ - v)) / D := by simp only [w₁, w₂]; field_simp; ring
    rw [this, abs_div, abs_neg, abs_of_pos hD, abs_mul, abs_of_nonneg ht0]
    gcongr
    calc t * |b₄ - v| ≤ 1 * ζ := by gcongr
      _ = ζ := one_mul _
  have hw₂ : |w₂| ≤ 2 := by
    have : |w₂| ≤ |w₁| + |w₁ - w₂| := by
      have := abs_sub_abs_le_abs_sub w₂ w₁; rw [abs_sub_comm w₂ w₁] at this; linarith
    have : ζ / D ≤ 1 := by rw [div_le_one hD]; exact hζD
    linarith
  have hdiff : |quadraticValue c t w₁ - quadraticValue c t w₂| ≤ 40 * H * (ζ / D) := by
    have e : quadraticValue c t w₁ - quadraticValue c t w₂ =
        (c 2 + c 4 * t + c 5 * (w₁ + w₂)) * (w₁ - w₂) := by
      simp [quadraticValue]; ring
    rw [e, abs_mul]
    have hc2 := hc 2; have hc4 := hc 4; have hc5 := hc 5
    have hA : |c 2 + c 4 * t + c 5 * (w₁ + w₂)| ≤ 40 * H := by
      have hw12 : |w₁ + w₂| ≤ 3 := by have := abs_add_le w₁ w₂; linarith
      have hc4t : |c 4 * t| ≤ 8 * H := by
        rw [abs_mul, abs_of_nonneg ht0]; nlinarith [abs_nonneg (c 4)]
      have hc5w : |c 5 * (w₁ + w₂)| ≤ 24 * H := by
        rw [abs_mul]; nlinarith [abs_nonneg (c 5), abs_nonneg (w₁ + w₂)]
      have := abs_add_three (c 2) (c 4 * t) (c 5 * (w₁ + w₂))
      linarith
    exact mul_le_mul hA hdw (abs_nonneg _) (by positivity)
  rw [hsheet]
  calc |quadraticValue c t w₁ - X|
      ≤ |quadraticValue c t w₁ - quadraticValue c t w₂| + |quadraticValue c t w₂ - X| := abs_sub_le _ _ _
    _ ≤ 40 * H * (ζ / D) + e := by
        gcongr
        rw [← hY, abs_sub_comm]; exact hfit
    _ = e + 40 * H * ζ / D := by ring

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.CompareSheets
