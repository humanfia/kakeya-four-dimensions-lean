-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.NativeAssignedCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/NativeAssignedCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/NativeAssignedCells.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/NativeAssignedCells.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Mathlib
import Submission.Lib.K4ContinuousKakeya.Incidence
import Submission.Lib.K4VelocityStrips.StripBins
import Submission.Lib.K4QuadraticSheets.JetBins

/-!
Three dimensional base cells assigned by the original fine physical state.
The assignment is a function of the whole fine state, rather than of a
newly rounded trajectory observation. This permits later restrictions to
preserve the original statewise velocity estimates.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeAssigned

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open Submission.Lib.K4ContinuousKakeya

noncomputable section

def cell (ξ : ℝ) (q : Fin 3 → ℤ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | (fun i => (⌊x i / ξ⌋ : ℤ)) = q}

theorem measurableSet_cell (ξ : ℝ) (q : Fin 3 → ℤ) : MeasurableSet (cell ξ q) := by
  have h : Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      fun i : Fin 3 => (⌊x i / ξ⌋ : ℤ)) := by fun_prop
  exact h (measurableSet_singleton q)

theorem volume_cell {ξ : ℝ} (hξ : 0 < ξ) (q : Fin 3 → ℤ) :
    volume (cell ξ q) = ENNReal.ofReal (ξ ^ 3) := by
  let S : Set (Fin 3 → ℝ) := Set.univ.pi
    (fun i => Ico ((q i : ℝ) * ξ) (((q i : ℝ) + 1) * ξ))
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have heq : cell ξ q = WithLp.ofLp ⁻¹' S := by
    ext x
    simp only [cell, mem_ofPred_eq, funext_iff, mem_preimage, S,
      mem_univ_pi, mem_Ico]
    apply forall_congr'
    intro i
    rw [Int.floor_eq_iff, le_div_iff₀ hξ, div_lt_iff₀ hξ]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage hS.nullMeasurableSet]
  change volume (Set.univ.pi _) = _
  rw [Real.volume_pi_Ico]
  have hlen (i : Fin 3) : ((q i : ℝ) + 1) * ξ - (q i : ℝ) * ξ = ξ := by ring
  simp only [hlen, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow hξ.le]

theorem cell_disjoint (ξ : ℝ) : Pairwise
    (fun q q' : Fin 3 → ℤ => Disjoint (cell ξ q) (cell ξ q')) := by
  intro q q' hne
  exact disjoint_left.mpr fun _ hx hx' => hne (hx.symm.trans hx')

theorem coord_distance {ξ : ℝ} (hξ : 0 < ξ) {q : Fin 3 → ℤ}
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ cell ξ q) (hy : y ∈ cell ξ q)
    (i : Fin 3) : |x i - y i| ≤ ξ := by
  have heq : ⌊x i / ξ⌋ = ⌊y i / ξ⌋ := congrFun (hx.trans hy.symm) i
  have h := (Int.abs_sub_lt_one_of_floor_eq_floor heq).le
  rw [← sub_div, abs_div, abs_of_pos hξ, div_le_iff₀ hξ] at h
  simpa only [one_mul] using h

theorem norm_le_three_of_coord {R : ℝ} (hR : 0 ≤ R)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, |x i| ≤ R) : ‖x‖ ≤ 3 * R := by
  have hsq (i : Fin 3) : (x i) ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_abs (x i), hx i, abs_nonneg (x i)]
  have hn := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_three] at hn
  nlinarith [hsq 0, hsq 1, hsq 2, norm_nonneg x]

def point (h b : ℝ) (z : Fin 3 → ℝ) (q : Fin 4 → ℤ) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => (b * (q i.castSucc : ℝ) - z i) / h)

def code (h b ξ : ℝ) (z : Fin 3 → ℝ) (q : Fin 4 → ℤ) : Fin 3 → ℤ :=
  fun i => ⌊point h b z q i / ξ⌋

theorem measurable_point (h b : ℝ) (z : Fin 3 → ℝ) : Measurable (point h b z) := by
  unfold point
  fun_prop

theorem measurable_code (h b ξ : ℝ) (z : Fin 3 → ℝ) : Measurable (code h b ξ z) := by
  unfold code
  fun_prop

theorem point_close {h b : ℝ} (hh : 0 < h) (hb : 0 < b)
    (z : Fin 3 → ℝ) (X : Fin 4 → ℝ) (i : Fin 3) :
    |point h b z (fun j => ⌊X j / b⌋) i - (X i.castSucc - z i) / h| ≤ b / h := by
  have herr := Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hb (X i.castSucc)
  change |(b * (⌊X i.castSucc / b⌋ : ℝ) - z i) / _ - _| ≤ _
  rw [← sub_div, show b * (⌊X i.castSucc / b⌋ : ℝ) - z i - (X i.castSucc - z i) =
    -(X i.castSucc - (⌊X i.castSucc / b⌋ : ℝ) * b) by ring,
    abs_div, abs_neg, abs_of_pos hh]
  exact div_le_div_of_nonneg_right herr hh.le

def direction (v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  ‖v‖⁻¹ • v

theorem norm_direction {v : EuclideanSpace ℝ (Fin 3)} (hv : v ≠ 0) :
    ‖direction v‖ = 1 := norm_smul_inv_norm hv

theorem measurable_direction : Measurable direction := by unfold direction; fun_prop

theorem affine_point_mem_line (a v : EuclideanSpace ℝ (Fin 3)) (t : ℝ) (hv : v ≠ 0) :
    a + t • v ∈ range (fun s : ℝ => a + s • direction v) := by
  refine ⟨t * ‖v‖, ?_⟩
  simp only [direction, smul_smul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),
    mul_one]

/-- A true affine trajectory witnessing an assigned fine state controls
the entire assigned coarse cell, with a fixed enlargement of its tube. -/
theorem cell_mem_tube {h b ξ : ℝ} (hh : 0 < h) (hb : 0 < b) (hξ : 0 < ξ)
    (hbξ : b ≤ h * ξ) (z : Fin 3 → ℝ) (X : Fin 4 → ℝ)
    (a v : EuclideanSpace ℝ (Fin 3)) (t : ℝ) (hv : v ≠ 0)
    (hbase : ∀ i, (a + t • v) i = (X i.castSucc - z i) / h)
    (q : Fin 3 → ℤ) (hcode : code h b ξ z (fun j => ⌊X j / b⌋) = q)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ cell ξ q) :
    x ∈ tube (7 * ξ) a (direction v) := by
  let center := point h b z (fun j => ⌊X j / b⌋)
  have hc : center ∈ cell ξ q := hcode
  have hclose (i : Fin 3) : |center i - (a + t • v) i| ≤ ξ := by
    rw [hbase]
    exact (point_close hh hb z X i).trans ((div_le_iff₀ hh).mpr (by simpa [mul_comm] using hbξ))
  have hcoord (i : Fin 3) : |(x - (a + t • v)) i| ≤ 2 * ξ := by
    change |x i - (a + t • v) i| ≤ 2 * ξ
    have htriangle := abs_sub_le (x i) (center i) ((a + t • v) i)
    linarith [coord_distance hξ hx hc i, hclose i]
  have hnorm := norm_le_three_of_coord (by positivity : 0 ≤ 2 * ξ) _ hcoord
  apply Metric.mem_thickening_iff.mpr
  refine ⟨a + t • v, affine_point_mem_line a v t hv, ?_⟩
  rw [dist_eq_norm]
  linarith

def offsets : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-1 : ℤ) 1)

theorem card_offsets : offsets.card = 27 := by
  norm_num [offsets, Fintype.card_piFinset, Fin.prod_univ_three]

theorem code_offset {h b ξ : ℝ} (hh : 0 < h) (hb : 0 < b) (hξ : 0 < ξ)
    (hbξ : b ≤ h * ξ) (z : Fin 3 → ℝ) (X : Fin 4 → ℝ) :
    ∃ o ∈ offsets, code h b ξ z (fun j => ⌊X j / b⌋) =
      (fun i => (⌊(X i.castSucc - z i) / h / ξ⌋ : ℤ)) + o := by
  let a := code h b ξ z (fun j => ⌊X j / b⌋)
  let q : Fin 3 → ℤ := fun i => ⌊(X i.castSucc - z i) / h / ξ⌋
  let o : Fin 3 → ℤ := a - q
  refine ⟨o, ?_, ?_⟩
  · apply Fintype.mem_piFinset.mpr
    intro i
    have hclose := (point_close hh hb z X i).trans
      ((div_le_iff₀ hh).mpr (by simpa [mul_comm] using hbξ))
    have hfloor := Submission.Lib.K4QuadraticSheets.floor_sub_le_one_of_abs_le hξ hclose
    simpa only [offsets, Finset.mem_Icc, abs_le, a, q, o, Pi.sub_apply, code] using hfloor
  · dsimp [o, a, q]
    abel

/-- The finite assigned cells have a common bounded enclosure; its
radius has no role in the quantitative Kakeya constant. -/
theorem exists_cell_radius {ξ : ℝ} (hξ : 0 < ξ) (F : Finset (Fin 3 → ℤ)) :
    ∃ R : ℝ, ∀ q ∈ F, cell ξ q ⊆ Metric.closedBall 0 R := by
  let A : (Fin 3 → ℤ) → ℝ := fun q => ∑ i, |(q i : ℝ) * ξ|
  refine ⟨3 * (ξ + ∑ q ∈ F, A q), ?_⟩
  intro q hq x hx
  have hA : ∀ q, 0 ≤ A q := fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcoord (i : Fin 3) : |x i| ≤ ξ + ∑ q ∈ F, A q := by
    have herr := Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hξ (x i)
    rw [congrFun hx i] at herr
    have hi : |(q i : ℝ) * ξ| ≤ A q := by
      change |(q i : ℝ) * ξ| ≤ ∑ j, |(q j : ℝ) * ξ|
      exact Finset.single_le_sum (f := fun j : Fin 3 => |(q j : ℝ) * ξ|)
        (fun j _ => abs_nonneg ((q j : ℝ) * ξ)) (Finset.mem_univ i)
    have hqsum : A q ≤ ∑ q ∈ F, A q := Finset.single_le_sum
      (fun q _ => hA q) hq
    have htri := abs_add_le (x i - (q i : ℝ) * ξ) ((q i : ℝ) * ξ)
    rw [sub_add_cancel] at htri
    linarith
  have hn := norm_le_three_of_coord (by positivity : 0 ≤ ξ + ∑ q ∈ F, A q) x hcoord
  simpa only [Metric.mem_closedBall, dist_zero_right] using hn

def window (ξ H : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc ⌊-(H + 1) / ξ⌋ ⌊(H + 1) / ξ⌋

theorem code_mem_window {h b ξ H : ℝ} (hh : 0 < h) (hb : 0 < b)
    (hξ : 0 < ξ) (hξ₁ : ξ ≤ 1) (hbξ : b ≤ h * ξ)
    (z : Fin 3 → ℝ) (X : Fin 4 → ℝ)
    (hbound : ∀ i : Fin 3, |(X i.castSucc - z i) / h| ≤ H) :
    code h b ξ z (fun j => ⌊X j / b⌋) ∈ window ξ H := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hs : b / h ≤ 1 :=
    ((div_le_iff₀ hh).mpr (by simpa [mul_comm] using hbξ)).trans hξ₁
  have herr := point_close hh hb z X i
  have htri := abs_sub_le (point h b z (fun j => ⌊X j / b⌋) i)
    ((X i.castSucc - z i) / h) 0
  simp only [sub_zero] at htri
  have hpoint : |point h b z (fun j => ⌊X j / b⌋) i| ≤ H + 1 := by
    linarith [hbound i]
  exact Finset.mem_Icc.mpr
    ⟨Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hpoint).1 hξ.le),
      Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hpoint).2 hξ.le)⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeAssigned
