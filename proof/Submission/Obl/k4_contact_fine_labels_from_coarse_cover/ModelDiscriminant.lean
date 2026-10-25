-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/ModelDiscriminant.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelBase
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory Filter MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Lib.K4ContactNormalization

variable {α : Type*} [MeasurableSpace α] (p : Model α)

theorem Valid.μ_mass (hp : p.Valid) (k : ℕ) :
    ENNReal.ofReal ((p.K k)⁻¹) ≤ p.μ k univ :=
  ((hp.basic k).2.2.2.2.2.2.1).trans ((hp.basic k).2.2.2.2.1 _)

theorem Valid.exists_good (hp : p.Valid) (k : ℕ) : ∃ u, p.GoodPoint k u := by
  have hsub : p.μ k univ ≤ p.μ k (p.Good k) :=
    measure_mono_ae ((Valid.ae_good p hp k).mono (fun _ hu _ => hu))
  have hpos : 0 < p.μ k (p.Good k) :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (Valid.K_pos p hp k))).trans_le
      ((Valid.μ_mass p hp k).trans hsub)
  exact nonempty_of_measure_ne_zero hpos.ne'

theorem Valid.native_curvature_bound (hp : p.Valid) (k : ℕ) :
    |curvature (p.P k) (3 : Fin 4)| ≤ p.K k := by
  obtain ⟨u, hu⟩ := Valid.exists_good p hp k
  have h := (hu.fit 0 (by constructor <;> norm_num)).2.2
  rw [second_pderiv_eq_curvature (p.P k) (hp.basic k).2.2.2.2.2.2.2.1] at h
  simpa only [eval_C] using h

theorem snoc_base (k : ℕ) (u : α × ℝ) :
    Fin.snoc (p.base k u) (p.x k u.1 u.2 3) = p.x k u.1 u.2 := by
  have hb : p.base k u = Fin.init (p.x k u.1 u.2) := by
    funext i
    fin_cases i <;> rfl
  rw [hb]
  exact Fin.snoc_init_self _

theorem eval_native_discriminant (hp : p.Valid) (k : ℕ) (u : α × ℝ) :
    eval (p.base k u) (baseDiscriminant (p.P k)) =
      eval (p.x k u.1 u.2) (discriminant (p.P k) (3 : Fin 4)) := by
  rw [eval_baseDiscriminant (p.P k) (hp.basic k).2.2.2.2.2.2.2.1
    (p.base k u) (p.x k u.1 u.2 3), snoc_base]
  rfl

theorem GoodPoint.discriminant_bound (hp : p.Valid) {k : ℕ} {u : α × ℝ}
    (hu : p.GoodPoint k u) :
    |eval (p.base k u) (baseDiscriminant (p.P k))| ≤ 3 * p.K k ^ 2 := by
  have hK : 0 ≤ p.K k := (Valid.K_pos p hp k).le
  have hcurv := Valid.native_curvature_bound p hp k
  have hval := (hu.fit u.2 hu.time).1
  have hfirst := (hu.fit u.2 hu.time).2.1
  rw [eval_native_discriminant p hp, discriminant_eval]
  calc
    _ ≤ |(eval (p.x k u.1 u.2) (pderiv 3 (p.P k))) ^ 2| +
        |2 * curvature (p.P k) 3 * eval (p.x k u.1 u.2) (p.P k)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le ((eval (p.x k u.1 u.2) (pderiv 3 (p.P k))) ^ 2)
          (-(2 * curvature (p.P k) 3 * eval (p.x k u.1 u.2) (p.P k)))
    _ = |eval (p.x k u.1 u.2) (pderiv 3 (p.P k))| ^ 2 +
        2 * (|curvature (p.P k) 3| * |eval (p.x k u.1 u.2) (p.P k)|) := by
      rw [abs_pow, abs_mul, abs_mul]
      norm_num
      ring
    _ ≤ p.K k ^ 2 + 2 * (p.K k * p.K k) := by gcongr
    _ = 3 * p.K k ^ 2 := by ring

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
