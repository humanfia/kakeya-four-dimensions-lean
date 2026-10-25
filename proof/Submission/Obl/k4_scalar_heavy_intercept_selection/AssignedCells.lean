/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/AssignedCells.lean.
Earlier source credits are retained below. -/

import Submission.Obl.k4_scalar_heavy_intercept_selection.PlanarCells
import Submission.Lib.K4VelocityStrips.StripBins
import Submission.Lib.K4QuadraticSheets.JetBins

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open MeasureTheory Set
open Submission.Lib.K4ContinuousKakeya
open Submission.Lib.K4VelocityStrips

noncomputable section

/-- The normalized base coordinate recorded by a fine physical state. -/
def fineBasePoint (h b : ℝ) (z : Fin 2 → ℝ) (q : Fin 3 → ℤ) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i => (b * (q i.castSucc : ℝ) - z i) / h)

/-- Coarse cells are assigned by the fine state, so taking a coarse
cell is a union of whole fine states. -/
def assignedBaseCode (h b ξ : ℝ) (z : Fin 2 → ℝ) (q : Fin 3 → ℤ) : Fin 2 → ℤ :=
  fun i => ⌊fineBasePoint h b z q i / ξ⌋

theorem measurable_fineBasePoint (h b : ℝ) (z : Fin 2 → ℝ) :
    Measurable (fineBasePoint h b z) := by
  unfold fineBasePoint
  fun_prop

theorem measurable_assignedBaseCode (h b ξ : ℝ) (z : Fin 2 → ℝ) :
    Measurable (assignedBaseCode h b ξ z) := by
  unfold assignedBaseCode
  fun_prop

/-- The fine-state representative stays close to the actual normalized
base coordinate, including at unaligned cell boundaries. -/
theorem fineBasePoint_close (h b : ℝ) (z : Fin 2 → ℝ) (x : Fin 3 → ℝ)
    (hh : 0 < h) (hb : 0 < b) (i : Fin 2) :
    |fineBasePoint h b z (fun j => ⌊x j / b⌋) i - (x i.castSucc - z i) / h| ≤ b / h := by
  have ht := midpoint_floor_center_bound hb (x i.castSucc)
  change |(b * (⌊x i.castSucc / b⌋ : ℝ) - z i) / h - (x i.castSucc - z i) / h| ≤ b / h
  rw [← sub_div, show b * (⌊x i.castSucc / b⌋ : ℝ) - z i - (x i.castSucc - z i) =
    -(x i.castSucc - (⌊x i.castSucc / b⌋ : ℝ) * b) by ring,
    abs_div, abs_neg, abs_of_pos hh]
  exact div_le_div_of_nonneg_right ht hh.le

/-- Assignment to one base time cell bounds the actual time by one
physical slab, with only one additional fine width. -/
theorem assigned_time_slab {h b ξ t t₀ : ℝ}
    (hh : 0 < h) (hb : 0 < b) (hξ : 0 < ξ) (q : ℤ)
    (hcode : (⌊((b * (⌊t / b⌋ : ℝ) - t₀) / h) / ξ⌋ : ℤ) = q) :
    t ∈ Icc (t₀ + h * ξ * (q : ℝ)) (t₀ + h * ξ * ((q : ℝ) + 1) + b) := by
  have hcoarse := Int.floor_eq_iff.mp hcode
  rw [div_div, le_div_iff₀ (mul_pos hh hξ), div_lt_iff₀ (mul_pos hh hξ)] at hcoarse
  have hlo := Int.floor_le (t / b)
  have hhi := Int.lt_floor_add_one (t / b)
  rw [le_div_iff₀ hb] at hlo
  rw [div_lt_iff₀ hb] at hhi
  constructor <;> nlinarith [hcoarse.1, hcoarse.2]

/-- The actual time sections of an assigned cell have the expected
coarse time length. The statement allows arbitrary extra restrictions. -/
theorem volume_assigned_time_section_le {h b ξ t₀ : ℝ}
    (hh : 0 < h) (hb : 0 < b) (hξ : 0 < ξ) (hbξ : b ≤ h * ξ)
    (q : ℤ) (S : Set ℝ)
    (hS : ∀ t ∈ S, (⌊((b * (⌊t / b⌋ : ℝ) - t₀) / h) / ξ⌋ : ℤ) = q) :
    volume S ≤ ENNReal.ofReal (3 * h * ξ) := by
  calc
    _ ≤ volume (Icc (t₀ + h * ξ * (q : ℝ))
        (t₀ + h * ξ * ((q : ℝ) + 1) + b)) :=
      measure_mono fun t ht => assigned_time_slab hh hb hξ q (hS t ht)
    _ ≤ _ := by
      rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      nlinarith

/-- The actual normalized affine base point lies on its attached full
line with the unit direction used by multilinear Kakeya. -/
theorem normalized_affine_point_mem_line (u v t : ℝ) :
    WithLp.toLp 2 (![t, u + t * v] : Fin 2 → ℝ) ∈
      Set.range (fun s : ℝ => WithLp.toLp 2 (![0, u] : Fin 2 → ℝ) + s • unitBaseDirection v) := by
  refine ⟨t * ‖baseLine v‖, ?_⟩
  have hn : ‖baseLine v‖ ≠ 0 := (zero_lt_one.trans_le (baseLine_norm_lower v)).ne'
  change WithLp.toLp 2 (![0, u] : Fin 2 → ℝ) +
    (t * ‖baseLine v‖) • (‖baseLine v‖⁻¹ • baseLine v) =
      WithLp.toLp 2 (![t, u + t * v] : Fin 2 → ℝ)
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hn, mul_one]
  ext i
  fin_cases i <;> simp [baseLine]

/-- Every assigned cell is inside the tube of each actual affine line
that visits its fine states. -/
theorem assigned_base_cell_mem_tube {h b ξ : ℝ} (hh : 0 < h) (hb : 0 < b)
    (hξ : 0 < ξ) (hbξ : b ≤ h * ξ) (z : Fin 2 → ℝ) (X : Fin 3 → ℝ)
    (u v t : ℝ)
    (hbase : (fun i : Fin 2 => (X i.castSucc - z i) / h) = ![t, u + t * v])
    (q : Fin 2 → ℤ)
    (hcode : assignedBaseCode h b ξ z (fun j => ⌊X j / b⌋) = q)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ euclideanBaseCell ξ q) :
    x ∈ tube (5 * ξ) (WithLp.toLp 2 (![0, u] : Fin 2 → ℝ)) (unitBaseDirection v) := by
  let center := fineBasePoint h b z (fun j => ⌊X j / b⌋)
  let p : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![t, u + t * v]
  have hc : center ∈ euclideanBaseCell ξ q := hcode
  have hclose : ∀ i, |p i - center i| ≤ ξ := by
    intro i
    have hc' := fineBasePoint_close h b z X hh hb i
    have h' : b / h ≤ ξ := (div_le_iff₀ hh).2 (by simpa [mul_comm] using hbξ)
    rw [congrFun hbase i] at hc'
    change |center i - p i| ≤ b / h at hc'
    rw [abs_sub_comm] at hc'
    exact hc'.trans h'
  have hdist := dist_le_four_mesh_of_assigned_cell hξ p center q hc hclose x hx
  apply Metric.mem_thickening_iff.mpr
  exact ⟨p, normalized_affine_point_mem_line u v t, hdist.trans_lt (by linarith)⟩


/-- The nine possible offsets between an actual normalized cell and
the cell assigned using the fine-state corner. -/
def baseAssignmentOffsets : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-1 : ℤ) 1)

theorem card_baseAssignmentOffsets : baseAssignmentOffsets.card = 9 := by
  norm_num [baseAssignmentOffsets, Fintype.card_piFinset, Fin.prod_univ_two]

theorem assigned_code_has_small_offset {h b ξ : ℝ}
    (hh : 0 < h) (hb : 0 < b) (hξ : 0 < ξ) (hbξ : b ≤ h * ξ)
    (z : Fin 2 → ℝ) (X : Fin 3 → ℝ) :
    ∃ o ∈ baseAssignmentOffsets,
      assignedBaseCode h b ξ z (fun j => ⌊X j / b⌋) =
        (fun i : Fin 2 => (⌊(X i.castSucc - z i) / h / ξ⌋ : ℤ)) + o := by
  let a := assignedBaseCode h b ξ z (fun j => ⌊X j / b⌋)
  let q : Fin 2 → ℤ := fun i => ⌊(X i.castSucc - z i) / h / ξ⌋
  let o : Fin 2 → ℤ := fun i => a i - q i
  refine ⟨o, ?_, ?_⟩
  · apply Fintype.mem_piFinset.mpr
    intro i
    have hc : |fineBasePoint h b z (fun j => ⌊X j / b⌋) i -
        (X i.castSucc - z i) / h| ≤ ξ :=
      (fineBasePoint_close h b z X hh hb i).trans
        ((div_le_iff₀ hh).2 (by simpa [mul_comm] using hbξ))
    have hf := Submission.Lib.K4QuadraticSheets.floor_sub_le_one_of_abs_le hξ hc
    simpa only [Finset.mem_Icc, abs_le, a, q, o,
      assignedBaseCode] using hf
  · ext i
    dsimp [o, q, a]
    omega

/-- A finite code box containing every assigned cell over a bounded
normalized base. Its cardinality is not used in the Kakeya estimate. -/
def assignedBaseWindow (ξ H : ℝ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc ⌊-(H + 1) / ξ⌋ ⌊(H + 1) / ξ⌋)

theorem assigned_code_mem_window {h b ξ H : ℝ}
    (hh : 0 < h) (hb : 0 < b) (hξ : 0 < ξ) (hξ₁ : ξ ≤ 1) (hbξ : b ≤ h * ξ)
    (z : Fin 2 → ℝ) (X : Fin 3 → ℝ)
    (hbox : ∀ i : Fin 2, |(X i.castSucc - z i) / h| ≤ H) :
    assignedBaseCode h b ξ z (fun j => ⌊X j / b⌋) ∈ assignedBaseWindow ξ H := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hc := fineBasePoint_close h b z X hh hb i
  have hsmall : b / h ≤ 1 :=
    ((div_le_iff₀ hh).2 (by simpa [mul_comm] using hbξ)).trans hξ₁
  have hbound : |fineBasePoint h b z (fun j => ⌊X j / b⌋) i| ≤ H + 1 := by
    have ht := abs_sub_le (fineBasePoint h b z (fun j => ⌊X j / b⌋) i)
      ((X i.castSucc - z i) / h) 0
    simp only [sub_zero] at ht
    linarith [hbox i]
  exact Finset.mem_Icc.mpr
    ⟨Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hbound).1 hξ.le),
      Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hbound).2 hξ.le)⟩


/-- A finite family of coarse cells fits in one Euclidean ball. The
radius disappears from the uniform Kakeya estimate. -/
theorem exists_radius_euclideanBaseCells {ξ : ℝ} (hξ : 0 < ξ)
    (F : Finset (Fin 2 → ℤ)) :
    ∃ R : ℝ, ∀ q ∈ F, euclideanBaseCell ξ q ⊆ Metric.closedBall 0 R := by
  let A : (Fin 2 → ℤ) → ℝ := fun q => 2 * ξ + |(q 0 : ℝ) * ξ| + |(q 1 : ℝ) * ξ|
  refine ⟨∑ q ∈ F, A q, ?_⟩
  intro q hq x hx
  have hcoord (i : Fin 2) : |x i| ≤ ξ + |(q i : ℝ) * ξ| := by
    have hf : (⌊x i / ξ⌋ : ℤ) = q i := congrFun hx i
    have ht := midpoint_floor_center_bound hξ (x i)
    rw [hf] at ht
    have hu := abs_sub_le (x i) ((q i : ℝ) * ξ) 0
    simp only [sub_zero] at hu
    linarith
  have hnorm : ‖x‖ ≤ |x 0| + |x 1| := by
    apply (sq_le_sq₀ (norm_nonneg x) (by positivity : 0 ≤ |x 0| + |x 1|)).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
    nlinarith [sq_abs (x 0), sq_abs (x 1), mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]
  have hA : ‖x‖ ≤ A q := by
    have h₀ := hcoord 0
    have h₁ := hcoord 1
    dsimp [A]
    linarith
  have hsum : A q ≤ ∑ q' ∈ F, A q' :=
    Finset.single_le_sum (fun q' hq' => by dsimp [A]; positivity) hq
  simpa only [Metric.mem_closedBall, dist_zero_right] using hA.trans hsum

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
