-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/StableRecenter.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/StableRecenter.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.RecenterSheets
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.StableScale

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MvPolynomial

/-- Stable roots anchored at different incidences may be compared on one common box.
The nearby center and radius are fixed for the whole family. -/
theorem exists_stable_recentered_sheet (h : stableSheets) :
    ∃ C : ℕ, 20 ≤ C ∧ ∀ A a_fit a : ℝ, 2 ≤ A → 0 < a_fit →
      ∀ b c : MvPolynomial (Fin 3) ℝ, b.totalDegree ≤ 1 → c.totalDegree ≤ 2 →
      (∀ e, |(b * b - MvPolynomial.C (4 * a) * c).coeff e| ≤ A) →
      |a| * a_fit ≤ A ^ (-20 : ℝ) →
      ∀ (u0 v0 : Real3) (w0 : ℝ), ‖u0‖ ≤ A →
        ‖v0 - u0‖ ≤ A ^ (-(C : ℝ)) / 16 →
        |a * w0 ^ 2 + eval (fun j => u0 j) b * w0 + eval (fun j => u0 j) c| ≤ a_fit * A →
        4 * A ^ (-1 : ℝ) ≤ |2 * a * w0 + eval (fun j => u0 j) b| →
        |2 * a * w0 + eval (fun j => u0 j) b| ≤ A →
        ∃ F : RealSheet 2, ∀ x : Real3, ‖x‖ ≤ 1 →
          let u := v0 + (A ^ (-(C : ℝ)) / 128) • x
          let w := (F.f (emb x)).re
          (a * w ^ 2 + eval (fun j => u j) b * w + eval (fun j => u j) c = 0) ∧
          19 / 20 * |2 * a * w0 + eval (fun j => u0 j) b| ≤ |2 * a * w + eval (fun j => u j) b| ∧
          |2 * a * w + eval (fun j => u j) b| ≤ 21 / 20 * |2 * a * w0 + eval (fun j => u0 j) b| ∧
          0 < (2 * a * w + eval (fun j => u j) b) * (2 * a * w0 + eval (fun j => u0 j) b) ∧
          ∀ v : ℝ, |a * v ^ 2 + eval (fun j => u j) b * v + eval (fun j => u j) c| ≤ a_fit * A →
            0 < (2 * a * v + eval (fun j => u j) b) * (2 * a * w0 + eval (fun j => u0 j) b) →
            |v - w| ≤ a_fit * A ^ (C : ℝ) := by
  obtain ⟨C, hC, hstable⟩ := exists_stable_normalized_sheet h
  refine ⟨C, hC, ?_⟩
  intro A a_fit a hA ha_fit b c hb hc hcoeff ha u0 v0 w0 hu0 hv0 hvalue hslo hshi
  have hApos : 0 < A := by linarith
  have hAone : 1 ≤ A := by linarith
  have hslo' : A ^ (-1 : ℝ) ≤ |2 * a * w0 + eval (fun j => u0 j) b| := by
    have hh := Real.rpow_pos_of_pos hApos (-1)
    linarith
  obtain ⟨G, hG⟩ := hstable A a_fit a hA ha_fit b c hb hc hcoeff ha u0 w0 hu0 hvalue hslo' hshi
  let r := A ^ (-(C : ℝ))
  have hr : 0 < r := Real.rpow_pos_of_pos hApos _
  let z := (8 / r) • (v0 - u0)
  have hz : ‖z‖ ≤ (1 : ℝ) / 2 := by
    change ‖(8 / r) • (v0 - u0)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 8 / r)]
    have hh := mul_le_mul_of_nonneg_left hv0 (by positivity : 0 ≤ 8 / r)
    have he : 8 / r * (r / 16) = (1 : ℝ) / 2 := by field_simp; ring
    exact hh.trans_eq he
  let F := recenterRealSheet G z hz
  have hrle : r ≤ (A ^ 20)⁻¹ := by
    have he : A ^ (-20 : ℝ) = (A ^ 20)⁻¹ := by
      rw [show (-20 : ℝ) = -((20 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hApos.le, Real.rpow_natCast]
    rw [← he]
    have hCr : (20 : ℝ) ≤ C := by exact_mod_cast hC
    exact Real.rpow_le_rpow_of_exponent_le hAone (by linarith)
  refine ⟨F, ?_⟩
  intro x hx
  let y := z + (1 / 16 : ℝ) • x
  have hy : ‖y‖ ≤ 1 := recenter_real_point_norm_le hz hx
  have hFx : F.f (emb x) = G.f (emb y) := recenterRealSheet_apply G z hz x
  have hbase : u0 + (r / 8) • y = v0 + (r / 128) • x := by
    dsimp only [y, z]
    rw [smul_add, smul_smul, smul_smul]
    have he : r / 8 * (8 / r) = 1 := by field_simp
    rw [he, one_smul, show r / 8 * (1 / 16) = r / 128 by ring]
    abel
  have hbase' : u0 + (A ^ (-(C : ℝ)) / 8) • y =
      v0 + (A ^ (-(C : ℝ)) / 128) • x := hbase
  let u := v0 + (r / 128) • x
  have hu : ‖u - u0‖ < (A ^ 20)⁻¹ := by
    have he : ‖u - u0‖ = (r / 8) * ‖y‖ := by
      rw [show u = u0 + (r / 8) • y from hbase.symm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < r / 8)]
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ r / 8)
    simp only [mul_one] at hh
    exact (hh.trans_lt (by linarith : r / 8 < r)).trans_le hrle
  obtain ⟨hroot, _, _, hsign, hfit⟩ := hG y hy
  change a * (G.f (emb y)).re ^ 2 + eval (fun j => (u0 + (r / 8) • y) j) b * (G.f (emb y)).re +
      eval (fun j => (u0 + (r / 8) • y) j) c = 0 at hroot
  rw [hbase] at hroot
  obtain ⟨hlo, hhi⟩ := stable_root_derivative_window hA b c hb hc hcoeff ha
    u0 u w0 (G.f (emb y)).re hu0 hu hvalue hslo hroot
  change (a * (F.f (emb x)).re ^ 2 + eval (fun j => u j) b * (F.f (emb x)).re +
    eval (fun j => u j) c = 0) ∧ _
  rw [hFx]
  refine ⟨hroot, hlo, hhi, ?_, ?_⟩
  · simpa only [hbase'] using hsign
  · simpa only [hbase'] using hfit

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
