-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ShearRect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.Restricted

/-!
# Sheared rectangles and second-order following

A sheared rectangle has half-length `h` in time. In value it has half-width `w`
about the line `u₀ + s (z - z₀)`, measured relative to a reference curve `g₀`.
Its area is `4 h w`. A curve follows the rectangle when it stays within `w` of
the central line on the part of the time window inside `[-1,1]`.

The jet hypotheses bound the second derivative of any difference of curves by
`19 d`. Every curve near the rectangle's base point, with slope near `s`,
therefore follows the rectangle up to an error `19 d |z - z₁|²`.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_jet_close_pair_moment (strip JetControlled)

/-- The closed sheared rectangle. -/
def shearRect (g₀ : ℝ → ℝ) (z₀ h u₀ s w : ℝ) : Set (ℝ × ℝ) :=
  {p | |p.2 - z₀| ≤ h ∧ |p.1 - g₀ p.2 - (u₀ + s * (p.2 - z₀))| ≤ w}

/-- `f` follows the sheared rectangle on its time window inside `[-1,1]`. -/
def Follows (f g₀ : ℝ → ℝ) (z₀ h u₀ s w : ℝ) : Prop :=
  ∀ z ∈ Icc (-1 : ℝ) 1, |z - z₀| ≤ h → |f z - g₀ z - (u₀ + s * (z - z₀))| ≤ w

theorem measurableSet_shearRect {g₀ : ℝ → ℝ} (hg₀ : Continuous g₀) (z₀ h u₀ s w : ℝ) :
    MeasurableSet (shearRect g₀ z₀ h u₀ s w) := by
  have h1 : IsClosed {p : ℝ × ℝ | |p.2 - z₀| ≤ h} :=
    isClosed_le ((continuous_snd.sub continuous_const).abs) continuous_const
  have h2 : IsClosed {p : ℝ × ℝ | |p.1 - g₀ p.2 - (u₀ + s * (p.2 - z₀))| ≤ w} :=
    isClosed_le ((continuous_fst.sub (hg₀.comp continuous_snd)).sub
      (continuous_const.add (continuous_const.mul
        (continuous_snd.sub continuous_const)))).abs continuous_const
  exact (h1.inter h2).measurableSet

/-- The area of a sheared rectangle is at most `4 h w`. -/
theorem volume_shearRect_le {g₀ : ℝ → ℝ} (hg₀ : Continuous g₀) (z₀ h u₀ s w : ℝ)
    (hw : 0 ≤ w) :
    volume (shearRect g₀ z₀ h u₀ s w) ≤ ENNReal.ofReal (4 * h * w) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_shearRect hg₀ _ _ _ _ _)]
  have hfib : ∀ z : ℝ, volume ((fun x : ℝ => (x, z)) ⁻¹' shearRect g₀ z₀ h u₀ s w) ≤
      (Icc (z₀ - h) (z₀ + h)).indicator (fun _ => ENNReal.ofReal (2 * w)) z := by
    intro z
    by_cases hz : z ∈ Icc (z₀ - h) (z₀ + h)
    · rw [indicator_of_mem hz]
      have hsub : (fun x : ℝ => (x, z)) ⁻¹' shearRect g₀ z₀ h u₀ s w ⊆
          Icc (g₀ z + (u₀ + s * (z - z₀)) - w) (g₀ z + (u₀ + s * (z - z₀)) + w) := by
        intro x hx
        simp only [shearRect, mem_preimage, Set.mem_ofPred_eq] at hx
        have := abs_le.mp hx.2
        constructor <;> linarith
      calc _ ≤ volume (Icc (g₀ z + (u₀ + s * (z - z₀)) - w)
              (g₀ z + (u₀ + s * (z - z₀)) + w)) := measure_mono hsub
        _ = ENNReal.ofReal (2 * w) := by rw [Real.volume_Icc]; congr 1; ring
    · rw [indicator_of_notMem hz]
      have hempty : (fun x : ℝ => (x, z)) ⁻¹' shearRect g₀ z₀ h u₀ s w = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        simp only [shearRect, mem_preimage, Set.mem_ofPred_eq] at hx
        apply hz
        have := abs_le.mp hx.1
        constructor <;> linarith
      rw [hempty, measure_empty]
  calc (∫⁻ z, volume ((fun x : ℝ => (x, z)) ⁻¹' shearRect g₀ z₀ h u₀ s w))
      ≤ ∫⁻ z, (Icc (z₀ - h) (z₀ + h)).indicator (fun _ => ENNReal.ofReal (2 * w)) z :=
        lintegral_mono hfib
    _ = ENNReal.ofReal (2 * w) * volume (Icc (z₀ - h) (z₀ + h)) := by
        rw [lintegral_indicator measurableSet_Icc, lintegral_const,
          Measure.restrict_apply_univ]
    _ = ENNReal.ofReal (4 * h * w) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith)]
        congr 1
        ring

/-- Second-order control of the difference of two curves: its deviation from
the tangent line at `z₁` is at most `19 d (z - z₁)²` on `[-1,1]`. -/
theorem JetControlled.sub_tangent_le {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (hg : ∀ i, ContDiff ℝ 2 (g i)) (i j : Fin n)
    {z₁ z : ℝ} (hz₁ : z₁ ∈ Icc (-1 : ℝ) 1) (hz : z ∈ Icc (-1 : ℝ) 1) :
    |(g i z - g j z) - (g i z₁ - g j z₁) - (deriv (g i) z₁ - deriv (g j) z₁) * (z - z₁)| ≤
      19 * dist (q i) (q j) * (z - z₁) ^ 2 := by
  set c := deriv (g i) z₁ - deriv (g j) z₁ with hc
  set φ : ℝ → ℝ := fun x => (g i x - g j x) - c * x with hφ
  have hdi : Differentiable ℝ (g i) := (hg i).differentiable (by norm_num)
  have hdj : Differentiable ℝ (g j) := (hg j).differentiable (by norm_num)
  have hφd : ∀ x, HasDerivAt φ ((deriv (g i) x - deriv (g j) x) - c) x := by
    intro x
    have h1 : HasDerivAt (fun y => g i y - g j y - c * y)
        ((deriv (g i) x - deriv (g j) x) - c * 1) x :=
      ((hdi x).hasDerivAt.sub (hdj x).hasDerivAt).sub ((hasDerivAt_id' x).const_mul c)
    rw [mul_one] at h1
    exact h1
  have hsub : uIcc z₁ z ⊆ Icc (-1 : ℝ) 1 := uIcc_subset_Icc hz₁ hz
  have hbound : ∀ x ∈ uIcc z₁ z, ‖deriv φ x‖ ≤ 19 * dist (q i) (q j) * |z - z₁| := by
    intro x hx
    rw [(hφd x).deriv, Real.norm_eq_abs]
    have h1 := hjet.slope_difference_lipschitz hg i j (hsub hx) hz₁
    have h2 : |x - z₁| ≤ |z - z₁| := abs_sub_left_of_mem_uIcc hx
    have hd : 0 ≤ 19 * dist (q i) (q j) := by positivity
    calc |deriv (g i) x - deriv (g j) x - c| ≤ 19 * dist (q i) (q j) * |x - z₁| := h1
      _ ≤ 19 * dist (q i) (q j) * |z - z₁| := mul_le_mul_of_nonneg_left h2 hd
  have hmv := (convex_uIcc z₁ z).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => (hφd x).differentiableAt) hbound left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  have heq : φ z - φ z₁ =
      (g i z - g j z) - (g i z₁ - g j z₁) - c * (z - z₁) := by
    simp only [hφ]; ring
  rw [heq] at hmv
  calc _ ≤ 19 * dist (q i) (q j) * |z - z₁| * |z - z₁| := hmv
    _ = 19 * dist (q i) (q j) * (z - z₁) ^ 2 := by
        rw [mul_assoc, ← sq, sq_abs]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
