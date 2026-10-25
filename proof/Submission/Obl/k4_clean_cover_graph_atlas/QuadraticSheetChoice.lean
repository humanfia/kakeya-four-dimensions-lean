-- Adapted from this LOT tree, o173, session x0581 (with x0598), commit 583cb89a,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/QuadraticSheetChoice.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.StableRecenter
import Submission.Obl.k4_clean_cover_graph_atlas.PolynomialSheets

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MvPolynomial

noncomputable def quadraticSheetValue (flat : Bool) (a : ℝ) (b c : MvPolynomial (Fin 3) ℝ)
    (u : Real3) (w : ℝ) : ℝ :=
  if flat then 2 * a * w + eval (fun j => u j) b
  else a * w ^ 2 + eval (fun j => u j) b * w + eval (fun j => u j) c

noncomputable def quadraticSheetSlope (flat : Bool) (a : ℝ) (b : MvPolynomial (Fin 3) ℝ)
    (u : Real3) (w : ℝ) : ℝ :=
  if flat then 2 * a else 2 * a * w + eval (fun j => u j) b

/-- Every normalized quadratic test supplies a comparison sheet in common coordinates:
a stable branch at low curvature, and its affine center at high curvature. -/
theorem exists_quadratic_comparison_sheet_classified (h : stableSheets) :
    ∃ C : ℕ, 20 ≤ C ∧ ∀ A a_fit a : ℝ, 2 ≤ A → 0 < a_fit →
      ∀ b c : MvPolynomial (Fin 3) ℝ, b.totalDegree ≤ 1 → c.totalDegree ≤ 2 →
      (∀ e, |(b * b - MvPolynomial.C (4 * a) * c).coeff e| ≤ A) →
      ∀ (u0 v0 : Real3) (w0 : ℝ), ‖u0‖ ≤ A →
        ‖v0 - u0‖ ≤ A ^ (-(C : ℝ)) / 16 →
        |a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c| ≤ a_fit * A →
        4 * A ^ (-1 : ℝ) ≤ |2 * a * w0 + eval (fun j => u0 j) b| →
        |2 * a * w0 + eval (fun j => u0 j) b| ≤ A →
      ∃ (flat : Bool) (F : RealSheet 2),
        (flat = false ↔ |a| * a_fit ≤ A ^ (-20 : ℝ)) ∧
        let σ := if flat then 2 * a else 2 * a * w0 + eval (fun j => u0 j) b
        0 < |σ| ∧ ∀ x : Real3, ‖x‖ ≤ 1 →
          let u := v0 + (A ^ (-(C : ℝ)) / 128) • x
          let w := (F.f (emb x)).re
          quadraticSheetValue flat a b c u w = 0 ∧
          19 / 20 * |σ| ≤ |quadraticSheetSlope flat a b u w| ∧
          |quadraticSheetSlope flat a b u w| ≤ 21 / 20 * |σ| ∧
          0 < quadraticSheetSlope flat a b u w * σ ∧
          ∀ v : ℝ, |a * v ^ 2 + eval (fun j => u j) b * v + eval (fun j => u j) c| ≤ a_fit * A →
            |2 * a * v + eval (fun j => u j) b| ≤ A →
            (flat = false → 0 < (2 * a * v + eval (fun j => u j) b) *
              (2 * a * w0 + eval (fun j => u0 j) b)) →
            |v - w| ≤ a_fit * A ^ ((C : ℝ) + 2) := by
  obtain ⟨C, hC, hstable⟩ := exists_stable_recentered_sheet h
  refine ⟨C, hC, ?_⟩
  intro A a_fit a hA ha_fit b c hb hc hcoeff u0 v0 w0 hu0 hv0 hvalue hslo hshi
  have hApos : 0 < A := by linarith
  have hAone : 1 ≤ A := by linarith
  have hCreal : (20 : ℝ) ≤ C := by exact_mod_cast hC
  by_cases hsmall : |a| * a_fit ≤ A ^ (-20 : ℝ)
  · obtain ⟨F, hF⟩ := hstable A a_fit a hA ha_fit b c hb hc hcoeff hsmall u0 v0 w0
      hu0 hv0 hvalue hslo hshi
    refine ⟨false, F, ⟨fun _ => hsmall, fun _ => rfl⟩, ?_⟩
    have hσpos : 0 < |2 * a * w0 + eval (fun j => u0 j) b| :=
      (by positivity : 0 < 4 * A ^ (-1 : ℝ)).trans_le hslo
    refine ⟨hσpos, ?_⟩
    intro x hx
    obtain ⟨hroot, hlo, hhi, hsign, hfit⟩ := hF x hx
    refine ⟨hroot, hlo, hhi, hsign, ?_⟩
    intro v hv _ hbranch
    exact (hfit v hv (hbranch rfl)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hAone (by linarith : (C : ℝ) ≤ (C : ℝ) + 2)) ha_fit.le)
  · have hlarge : A ^ (-20 : ℝ) < |a| * a_fit := lt_of_not_ge hsmall
    have hane : a ≠ 0 := by
      intro hz
      rw [hz, abs_zero, zero_mul] at hlarge
      exact (not_lt_of_ge (Real.rpow_nonneg hApos.le _)) hlarge
    have hapos : 0 < |a| := abs_pos.mpr hane
    let r := A ^ (-(C : ℝ))
    have hr : 0 < r / 16 := by dsimp only [r]; positivity
    let F := quadraticCenterSheet a b hb v0 (r / 16) hr
    have hF (x : Real3) : (F.f (emb x)).re =
        -eval (fun j => (v0 + (r / 128) • x) j) b / (2 * a) := by
      rw [quadraticCenterSheet_re]
      rw [show r / 16 / 8 = r / 128 by ring]
    have hfitbound : A / (2 * |a|) ≤ a_fit * A ^ ((C : ℝ) + 2) := by
      have hpow : A ^ (-20 : ℝ) * A ^ (21 : ℝ) = A := by
        rw [← Real.rpow_add hApos, show (-20 : ℝ) + 21 = 1 by norm_num, Real.rpow_one]
      have hprod := mul_le_mul_of_nonneg_right hlarge.le (Real.rpow_nonneg hApos.le 21)
      have hh : A ≤ (a_fit * A ^ (21 : ℝ)) * (2 * |a|) := by
        rw [hpow] at hprod
        nlinarith
      exact ((div_le_iff₀ (by positivity : 0 < 2 * |a|)).mpr hh).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hAone (by linarith)) ha_fit.le)
    refine ⟨true, F, ⟨fun he => Bool.noConfusion he, fun hs => (hsmall hs).elim⟩, ?_⟩
    have h2ane : 2 * a ≠ 0 := mul_ne_zero (by norm_num) hane
    refine ⟨abs_pos.mpr h2ane, ?_⟩
    intro x hx
    change 2 * a * (F.f (emb x)).re + eval (fun j => (v0 + (r / 128) • x) j) b = 0 ∧ _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hF]
      field_simp <;> ring
    · change 19 / 20 * |2 * a| ≤ |2 * a|
      nlinarith [abs_nonneg (2 * a)]
    · change |2 * a| ≤ 21 / 20 * |2 * a|
      nlinarith [abs_nonneg (2 * a)]
    · change 0 < (2 * a) * (2 * a)
      simpa only [pow_two] using sq_pos_of_ne_zero h2ane
    · intro v _ hder _
      have hh := quadraticCenterSheet_fit a b hb v0 (r / 16) hr x (v := v) (U := A) hapos (le_refl |a|)
      rw [show r / 16 / 8 = r / 128 by ring] at hh
      exact (hh hder).trans hfitbound

theorem exists_quadratic_comparison_sheet (h : stableSheets) :
    ∃ C : ℕ, 20 ≤ C ∧ ∀ A a_fit a : ℝ, 2 ≤ A → 0 < a_fit →
      ∀ b c : MvPolynomial (Fin 3) ℝ, b.totalDegree ≤ 1 → c.totalDegree ≤ 2 →
      (∀ e, |(b * b - MvPolynomial.C (4 * a) * c).coeff e| ≤ A) →
      ∀ (u0 v0 : Real3) (w0 : ℝ), ‖u0‖ ≤ A →
        ‖v0 - u0‖ ≤ A ^ (-(C : ℝ)) / 16 →
        |a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c| ≤ a_fit * A →
        4 * A ^ (-1 : ℝ) ≤ |2 * a * w0 + eval (fun j => u0 j) b| →
        |2 * a * w0 + eval (fun j => u0 j) b| ≤ A →
      ∃ (flat : Bool) (F : RealSheet 2),
        let σ := if flat then 2 * a else 2 * a * w0 + eval (fun j => u0 j) b
        0 < |σ| ∧ ∀ x : Real3, ‖x‖ ≤ 1 →
          let u := v0 + (A ^ (-(C : ℝ)) / 128) • x
          let w := (F.f (emb x)).re
          quadraticSheetValue flat a b c u w = 0 ∧
          19 / 20 * |σ| ≤ |quadraticSheetSlope flat a b u w| ∧
          |quadraticSheetSlope flat a b u w| ≤ 21 / 20 * |σ| ∧
          0 < quadraticSheetSlope flat a b u w * σ ∧
          ∀ v : ℝ, |a * v ^ 2 + eval (fun j => u j) b * v + eval (fun j => u j) c| ≤ a_fit * A →
            |2 * a * v + eval (fun j => u j) b| ≤ A →
            (flat = false → 0 < (2 * a * v + eval (fun j => u j) b) *
              (2 * a * w0 + eval (fun j => u0 j) b)) →
            |v - w| ≤ a_fit * A ^ ((C : ℝ) + 2) := by
  obtain ⟨C, hC, hchoose⟩ := exists_quadratic_comparison_sheet_classified h
  refine ⟨C, hC, ?_⟩
  intro A a_fit a hA ha_fit b c hb hc hcoeff u0 v0 w0 hu0 hv0 hvalue hslo hshi
  obtain ⟨flat, F, _, hF⟩ := hchoose A a_fit a hA ha_fit b c hb hc hcoeff
    u0 v0 w0 hu0 hv0 hvalue hslo hshi
  exact ⟨flat, F, hF⟩

end Submission.Obl.k4_clean_cover_graph_atlas
