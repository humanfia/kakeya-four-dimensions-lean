-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/OriginalBlockRemez.lean;
-- only the namespace was renamed into o230's.
import Submission.Lib.K4ChartLifting.Mass
import Submission.Lib.K4PolynomialRemez

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MeasureTheory

/-- Normalizing the original time row keeps its relative length. Only
the coordinate measure is changed; the incidence law is untouched. -/
theorem normalized_original_row_measure (t0 h η : ℝ) (hh : 0 < h) (_hη : 0 ≤ η)
    (S : Set ℝ) (hS : MeasurableSet S) (hmass : ENNReal.ofReal (h*η) ≤ volume S) :
    ENNReal.ofReal η ≤ volume ((fun t : ℝ => t0+h*t) ⁻¹' S) := by
  have hmap := Submission.Lib.K4ChartLifting.map_volume_affine (-t0/h) h⁻¹ (inv_pos.mpr hh)
  have hf : (fun t : ℝ => (t-(-t0/h))/h⁻¹)=(fun t : ℝ => t0+h*t) := by
    ext t
    field_simp
    ring
  rw [hf] at hmap
  have hψ : Measurable (fun t : ℝ => t0+h*t) :=
    measurable_const.add (measurable_const.mul measurable_id)
  rw [← Measure.map_apply hψ hS,hmap,Measure.smul_apply,smul_eq_mul]
  have heq : ENNReal.ofReal η=ENNReal.ofReal h⁻¹*ENNReal.ofReal (h*η) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hh.le)]
    congr 1
    field_simp
  rw [heq]
  exact mul_le_mul' le_rfl hmass

/-- Remez extends a fit from an arbitrary original long row to its
whole original time block, with a cost depending on relative length. -/
theorem polynomial_remez_original_block (p : Polynomial ℝ) (D : ℕ)
    (hp : p.natDegree ≤ D) (t0 h η E : ℝ) (hh : 0 < h)
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (S : Set ℝ) (hSm : MeasurableSet S) (hS : S ⊆ Icc t0 (t0+h))
    (hmass : ENNReal.ofReal (h*η) ≤ volume S)
    (hfit : ∀ t ∈ S, |p.eval t| ≤ E) :
    ∀ t ∈ Icc t0 (t0+h), |p.eval t| ≤ (8*((D : ℝ)+1)/η)^D*E := by
  let A : Polynomial ℝ := Polynomial.C t0+Polynomial.C h*Polynomial.X
  let q := p.comp A
  let U := (fun t : ℝ => t0+h*t) ⁻¹' S
  have hA : A.natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le (by simp) (Polynomial.natDegree_mul_le.trans (by simp)))
  have hq : q.natDegree ≤ D :=
    Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul hp hA).trans_eq (Nat.mul_one D))
  have hU : U ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨hl,hu⟩ := hS ht
    change t0 ≤ t0+h*t at hl
    change t0+h*t ≤ t0+h at hu
    constructor <;> nlinarith
  have hmassU : ENNReal.ofReal η ≤ volume U :=
    normalized_original_row_measure t0 h η hh hη.le S hSm hmass
  have hqfit (t : ℝ) (ht : t ∈ U) : |q.eval t| ≤ E := by
    simpa only [q,A,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X] using hfit (t0+h*t) ht
  have hremez := Submission.Lib.K4PolynomialRemez.polynomial_remez_unit q D hq U
    hη hη1 hE hU hmassU hqfit
  intro t ht
  have hunit : (t-t0)/h ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr ht.1) hh.le,
      (div_le_one hh).mpr (by linarith [ht.2])⟩
  have hback : t0+h*((t-t0)/h)=t := by field_simp; ring
  simpa only [q,A,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,hback] using hremez _ hunit

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
