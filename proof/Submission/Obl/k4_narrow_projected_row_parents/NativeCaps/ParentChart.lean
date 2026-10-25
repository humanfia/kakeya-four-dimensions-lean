import Submission.Obl.k4_narrow_projected_row_parents.RowApply
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.ParentZoom
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMeshPowers
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedBaseCaps

namespace Submission.Obl.k4_narrow_projected_row_parents.NativeCaps

open MeasureTheory Set Filter Matrix
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Obl.k4_narrow_projected_row_parents.PreparedModel

noncomputable section

/-- The three base coordinates in a parent chart. -/
def rowBase (Z : Zoom) (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  affineBase Z.baseMatrix Z.baseShift (basePoint b t)

theorem rowBase_eq (Z : Zoom) (b : Fin 6 → ℝ) (t : ℝ) :
    rowBase Z b t = ![(t - Z.t₀) / Z.q, (b 0 + t * b 3 - Z.z₀) / Z.q,
      (b 1 + t * b 4 - Z.c₂ - Z.c₃ * t - Z.c₄ * (b 0 + t * b 3)) / Z.w] := by
  ext e
  fin_cases e <;>
    simp [rowBase, affineBase, Submission.Lib.K4AffineMeshCaps.affineBase, Zoom.baseMatrix, Zoom.baseShift, basePoint,
      Submission.Lib.K4MovingMeshBoxes.basePoint, dotProduct, Fin.sum_univ_three] <;> ring

theorem rowBase_horizontal (Z : Zoom) (hq : Z.q ≠ 0) (b : Fin 6 → ℝ) (t : ℝ) :
    hpos Z b ((t - Z.t₀) / Z.q) =
      fun e : Fin 2 => rowBase Z b t (Fin.castLE (by decide : 2 ≤ 3) e) := by
  ext e
  fin_cases e
  · simp [hpos, rowBase_eq]
  · simp [hpos, rowBase_eq, Zoom.coeff_zero]
    field_simp
    ring

theorem hcell_eq_rowBase (Z : Zoom) (hq : Z.q ≠ 0) (ξ : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    hcell Z ξ b t = fun e : Fin 2 =>
      baseMesh ξ (rowBase Z b t) (Fin.castLE (by decide : 2 ≤ 3) e) := by
  unfold Submission.Obl.k4_narrow_projected_row_parents.hcell
  rw [rowBase_horizontal Z hq]
  rfl

theorem zoom_row_sum_le (Z : Zoom) {K : ℝ} (hK : 1 ≤ K)
    (hq : 0 < Z.q) (hw : 0 < Z.w) (hwq : Z.w ≤ Z.q)
    (hc3 : |Z.c₃| ≤ K) (hc4 : |Z.c₄| ≤ K) (e : Fin 3) :
    (∑ j, |Z.baseMatrix e j|) ≤ 3 * K / Z.w := by
  have hmajor : Z.q⁻¹ ≤ 3 * K / Z.w := by
    calc Z.q⁻¹ ≤ Z.w⁻¹ := inv_anti₀ hw hwq
      _ = 1 / Z.w := (one_div _).symm
      _ ≤ 3 * K / Z.w := div_le_div_of_nonneg_right (by linarith) hw.le
  fin_cases e
  · simpa [Zoom.baseMatrix, Fin.sum_univ_three, abs_inv, abs_of_pos hq] using hmajor
  · simpa [Zoom.baseMatrix, Fin.sum_univ_three, abs_inv, abs_of_pos hq] using hmajor
  · have hsum : (|Z.c₃| + |Z.c₄| + 1) / Z.w ≤ 3 * K / Z.w :=
      div_le_div_of_nonneg_right (by linarith) hw.le
    simpa [Zoom.baseMatrix, Fin.sum_univ_three, abs_div, abs_neg, abs_inv,
      abs_of_pos hw, add_div, one_div] using hsum

variable {α : Type} [MeasurableSpace α]

theorem parentChart_det (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (k : ℕ) (r : ℝ) (i : Fin (a.n k r)) :
    (parentZoom p a k r i).baseMatrix.det ≠ 0 ∧
      |(parentZoom p a k r i).baseMatrix.det|⁻¹ =
        a.q k r ^ 3 * narrow p k r := by
  have hq := q_pos a k r
  have hg := narrow_pos p hp k r
  refine ⟨Zoom.baseMatrix_det_ne_zero _ (parentZoom_ok p hp a k r i), ?_⟩
  rw [Zoom.baseMatrix_abs_det_inv _ hq (mul_pos hq hg)]
  dsimp [parentZoom]
  ring

theorem parentChart_transverse_bound (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    {R : ℝ} {k : ℕ} {r : ℝ} (hA : a.AtlasAt p R k r) (i : Fin (a.n k r))
    {l : α} {t : ℝ} (hl : l ∈ a.B k r i) (ht : t ∈ a.block k r i) :
    |rowBase (parentZoom p a k r i) (a.b k l) t 2| ≤ p.K k := by
  have hq := q_pos a k r
  have hg := narrow_pos p hp k r
  rw [rowBase_eq]
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  dsimp only [parentZoom]
  rw [abs_div, abs_of_pos (mul_pos hq hg), div_le_iff₀ (mul_pos hq hg)]
  have h := ((hA.2.2.2.2.1 i).2.2.2.2.2.1 l ((hA.2.2.1 i).2.2 hl) t ht).2.1
  simpa only [PreparedModel.x, Submission.Lib.K4ContactNormalization.point, parentZoom,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, mul_comm t, mul_assoc] using h

/-- The unskewed parent matrix has a fixed power bound, uniformly over its labels. -/
theorem eventually_parentChart_matrix_bound (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ R : ℝ, a.AtlasAt p R k r →
      ∀ i e, (∑ j, |(parentZoom p a k r i).baseMatrix e j|) ≤ p.N k ^ C := by
  let C : ℝ := (p.kappa + p.ell) * r + 3
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [a.eventually_q_narrow_lower p hp r (eps := 1) one_pos,
    hp.2.2.1.2 1 one_pos, hp.2.1.eventually_ge_atTop 3] with k hkqg hkK hk3
  intro R hA i e
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hq := q_pos a k r
  have hg := narrow_pos p hp k r
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hg1 : narrow p k r ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.1 k]) (by nlinarith)
  have hqg : p.N k ^ (-(p.kappa + p.ell) * r - 1) ≤ a.q k r * narrow p k r :=
    hkqg R r hA le_rfl
  have hsum := zoom_row_sum_le (parentZoom p a k r i) hK hq (mul_pos hq hg)
    (by dsimp [parentZoom]; nlinarith) ((hA.2.2.2.2.1 i).2.2.2.1 3)
    ((hA.2.2.2.2.1 i).2.2.2.1 4) e
  calc (∑ j, |(parentZoom p a k r i).baseMatrix e j|)
      ≤ 3 * p.K k / (a.q k r * narrow p k r) := hsum
    _ ≤ 3 * p.N k / p.N k ^ (-(p.kappa + p.ell) * r - 1) := by
      gcongr
      · simpa only [Real.rpow_one] using hkK
    _ ≤ p.N k * p.N k / p.N k ^ (-(p.kappa + p.ell) * r - 1) := by gcongr
    _ = p.N k ^ C := by
      rw [← pow_two, ← Real.rpow_two, ← Real.rpow_sub hN]
      congr 1
      dsimp [C]
      ring

end

end Submission.Obl.k4_narrow_projected_row_parents.NativeCaps
