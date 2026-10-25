/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarMotion.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarMotion.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Linarith

/-! Actual scalar quadratic and affine trajectories and their measurable bounds. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

structure ScalarMotion (Λ : Type*) [MeasurableSpace Λ] where
  x₀ : Λ → ℝ
  x₁ : Λ → ℝ
  x₂ : Λ → ℝ
  y₀ : Λ → ℝ
  y₁ : Λ → ℝ
  measurable_x₀ : Measurable x₀
  measurable_x₁ : Measurable x₁
  measurable_x₂ : Measurable x₂
  measurable_y₀ : Measurable y₀
  measurable_y₁ : Measurable y₁

namespace ScalarMotion

variable {Λ : Type*} [MeasurableSpace Λ] (D : ScalarMotion Λ)

def x (l : Λ) (t : ℝ) : ℝ := D.x₀ l + D.x₁ l * t + D.x₂ l * t ^ 2
def y (l : Λ) (t : ℝ) : ℝ := D.y₀ l + D.y₁ l * t
def residual (F : ℝ → ℝ) (l : Λ) (t : ℝ) : ℝ := D.x₁ l + 2 * D.x₂ l * t - F t * D.y₁ l
def scalar (F : ℝ → ℝ) (l : Λ) (t : ℝ) : ℝ := D.x l t - F t * D.y l t
def Bounded (K : ℝ) (l : Λ) : Prop :=
  |D.x₀ l| ≤ K ∧ |D.x₁ l| ≤ K ∧ |D.x₂ l| ≤ K ∧ |D.y₀ l| ≤ K ∧ |D.y₁ l| ≤ K

theorem measurable_x : Measurable (fun p : Λ × ℝ => D.x p.1 p.2) :=
  ((D.measurable_x₀.comp measurable_fst).add ((D.measurable_x₁.comp measurable_fst).mul measurable_snd)).add
    ((D.measurable_x₂.comp measurable_fst).mul (measurable_snd.pow_const 2))

theorem measurable_y : Measurable (fun p : Λ × ℝ => D.y p.1 p.2) :=
  (D.measurable_y₀.comp measurable_fst).add ((D.measurable_y₁.comp measurable_fst).mul measurable_snd)

theorem measurable_residual {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun p : Λ × ℝ => D.residual F p.1 p.2) :=
  ((D.measurable_x₁.comp measurable_fst).add
    ((measurable_const.mul (D.measurable_x₂.comp measurable_fst)).mul measurable_snd)).sub
      ((hF.comp measurable_snd).mul (D.measurable_y₁.comp measurable_fst))

theorem measurable_scalar {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun p : Λ × ℝ => D.scalar F p.1 p.2) :=
  D.measurable_x.sub ((hF.comp measurable_snd).mul D.measurable_y)

theorem measurable_at_x (t : ℝ) : Measurable (fun l => D.x l t) :=
  D.measurable_x.comp (measurable_id.prodMk measurable_const)

theorem measurable_at_y (t : ℝ) : Measurable (fun l => D.y l t) :=
  D.measurable_y.comp (measurable_id.prodMk measurable_const)

theorem measurable_at_residual (F : ℝ → ℝ) (t : ℝ) : Measurable (fun l => D.residual F l t) :=
  (D.measurable_x₁.add ((measurable_const.mul D.measurable_x₂).mul_const t)).sub
    (measurable_const.mul D.measurable_y₁)

theorem measurable_at_scalar (F : ℝ → ℝ) (t : ℝ) : Measurable (fun l => D.scalar F l t) :=
  (D.measurable_at_x t).sub (measurable_const.mul (D.measurable_at_y t))

theorem bounds_at_unit_time {K t : ℝ} (hK : 1 ≤ K) {l : Λ} (hl : D.Bounded K l)
    (ht : t ∈ Icc (0 : ℝ) 1) {F : ℝ → ℝ} (hF : |F t| ≤ K) :
    |D.x l t| ≤ 3 * K ∧ |D.y l t| ≤ 2 * K ∧
      |D.residual F l t| ≤ 4 * K ^ 2 ∧ |D.scalar F l t| ≤ 5 * K ^ 2 := by
  obtain ⟨hx₀, hx₁, hx₂, hy₀, hy₁⟩ := hl
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have ht' : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have ht2 : |t ^ 2| ≤ 1 := by
    rw [abs_pow]
    simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg t) ht' 2
  have hx₁t : |D.x₁ l * t| ≤ K := by
    rw [abs_mul]
    exact (mul_le_mul hx₁ ht' (abs_nonneg _) hK0).trans_eq (mul_one _)
  have hx₂t : |D.x₂ l * t| ≤ K := by
    rw [abs_mul]
    exact (mul_le_mul hx₂ ht' (abs_nonneg _) hK0).trans_eq (mul_one _)
  have hx₂t2 : |D.x₂ l * t ^ 2| ≤ K := by
    rw [abs_mul]
    exact (mul_le_mul hx₂ ht2 (abs_nonneg _) hK0).trans_eq (mul_one _)
  have hy₁t : |D.y₁ l * t| ≤ K := by
    rw [abs_mul]
    exact (mul_le_mul hy₁ ht' (abs_nonneg _) hK0).trans_eq (mul_one _)
  have hx : |D.x l t| ≤ 3 * K := by
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith)
  have hy : |D.y l t| ≤ 2 * K := (abs_add_le _ _).trans (by linarith)
  have hFy₁ : |F t * D.y₁ l| ≤ K ^ 2 := by
    rw [abs_mul]
    have h := mul_le_mul hF hy₁ (abs_nonneg _) hK0
    nlinarith
  have hFy : |F t * D.y l t| ≤ 2 * K ^ 2 := by
    rw [abs_mul]
    have h := mul_le_mul hF hy (abs_nonneg _) hK0
    nlinarith
  have hKsq : K ≤ K ^ 2 := by nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hK)]
  have hderiv : |D.x₁ l + 2 * D.x₂ l * t| ≤ 3 * K := by
    have htwice : |2 * D.x₂ l * t| ≤ 2 * K := by
      rw [mul_assoc, abs_mul]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    exact (abs_add_le _ _).trans (by linarith)
  exact ⟨hx, hy, (abs_sub _ _).trans (by linarith), (abs_sub _ _).trans (by linarith)⟩

end ScalarMotion

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
