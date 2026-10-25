-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_compact_offset_normalization.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Basic definitions for the compact offset normalization

The hypotheses of the frozen statement, as named predicates, and a few coordinate facts
about `Space = EuclideanSpace ℝ (Fin 3)`.
-/

namespace WangZahlLot.Obl.wz_compact_offset_normalization

open Set Metric MeasureTheory
open scoped ENNReal

abbrev Space := LeanEval.Analysis.WangZahlKakeya.Space

abbrev Tube (δ : ℝ) (x v : Space) : Set Space :=
  thickening δ (segment ℝ x (x + v))

/-- The family hypothesis `H` of the frozen statement. -/
def Family (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1) ∧
  (∀ i, Tube δ (x i) (v i) ⊆ ball 0 1) ∧
  (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
    (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i))) ∧
  (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ Tube δ (x i) (v i)) ∧
  ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)

/-- The convex count hypothesis `F` of the frozen statement. -/
def Frostman (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
      ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W

/-- The slope hypothesis `N` of the frozen statement. -/
def Slope (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 →
    1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1 / 100 : ℝ)

/-- The twisted projection `P_f`. -/
def Projection (f : ℝ → ℝ) (E : Set Space) : Set (ℝ × ℝ) :=
  (fun p : Space => (p 0 + f (p 2) * p 1, p 2)) '' E

/-- The projection estimate restricted to offsets `f 0` satisfying `R`. -/
def Estimate (R : ℝ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
      Frostman η δ n x v → ∀ f : ℝ → ℝ, Slope f → R (f 0) →
      ENNReal.ofReal (δ ^ ε) ≤ volume (Projection f (⋃ i, Y i))

/-! ### Coordinates -/

theorem norm_sq_eq (p : Space) : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem abs_coord_le_norm (p : Space) (i : Fin 3) : |p i| ≤ ‖p‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le p i

theorem norm_le_of_sq_le {p : Space} {r : ℝ} (hr : 0 ≤ r)
    (h : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 ≤ r ^ 2) : ‖p‖ ≤ r := by
  rw [← sq_le_sq₀ (norm_nonneg p) hr, norm_sq_eq]
  exact h

/-- A ball inside the unit ball forces its center into the shrunken closed ball. -/
theorem norm_add_le_of_ball_subset {p : Space} {δ : ℝ} (hδ : 0 < δ)
    (h : ball p δ ⊆ ball (0 : Space) 1) : ‖p‖ ≤ 1 - δ := by
  by_contra hlt
  push Not at hlt
  rcases le_or_gt 1 ‖p‖ with hp1 | hp1
  · have := h (mem_ball_self hδ)
    rw [mem_ball_zero_iff] at this
    linarith
  set r : ℝ := (1 - ‖p‖ + δ) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  -- a unit vector `e` pointing away from the origin
  obtain ⟨e, he, hpe⟩ : ∃ e : Space, ‖e‖ = 1 ∧ ‖p + r • e‖ = ‖p‖ + r := by
    by_cases hp : p = 0
    · refine ⟨EuclideanSpace.single 0 1, by simp, ?_⟩
      subst hp
      simp [norm_smul, abs_of_pos hr0]
    · have hnp : 0 < ‖p‖ := norm_pos_iff.mpr hp
      refine ⟨‖p‖⁻¹ • p, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnp.ne']
      · have : p + r • (‖p‖⁻¹ • p) = (1 + r * ‖p‖⁻¹) • p := by
          rw [add_smul, one_smul, smul_smul]
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), add_mul, one_mul,
          mul_assoc, inv_mul_cancel₀ hnp.ne', mul_one]
  have hmem : p + r • e ∈ ball p δ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_pos hr0, hr]
    linarith
  have := h hmem
  rw [mem_ball_zero_iff, hpe, hr] at this
  linarith

/-- The axis of a tube inside the unit ball lies in the closed ball of radius `1 - δ`. -/
theorem segment_subset_of_tube {δ : ℝ} (hδ : 0 < δ) {x v : Space}
    (h : Tube δ x v ⊆ ball 0 1) : segment ℝ x (x + v) ⊆ closedBall 0 (1 - δ) := by
  intro p hp
  rw [mem_closedBall_zero_iff]
  exact norm_add_le_of_ball_subset hδ ((ball_subset_thickening hp δ).trans h)

/-- A tube whose axis lies in the closed ball of radius `1 - δ` lies in the unit ball. -/
theorem tube_subset_of_segment {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {x v : Space}
    (h : segment ℝ x (x + v) ⊆ closedBall 0 (1 - δ)) : Tube δ x v ⊆ ball 0 1 := by
  calc Tube δ x v ⊆ thickening δ (closedBall (0 : Space) (1 - δ)) := thickening_subset_of_subset δ h
    _ = ball 0 (δ + (1 - δ)) := thickening_closedBall hδ (by linarith) 0
    _ = ball 0 1 := by ring_nf

/-- Points of a segment, parametrized. -/
theorem mem_segment_param {x v p : Space} :
    p ∈ segment ℝ x (x + v) ↔ ∃ t ∈ Icc (0 : ℝ) 1, p = x + t • v := by
  rw [segment_eq_image']
  simp only [add_sub_cancel_left, mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

/-- Points of a tube, parametrized. -/
theorem mem_tube_iff {δ : ℝ} {x v p : Space} :
    p ∈ Tube δ x v ↔ ∃ t ∈ Icc (0 : ℝ) 1, dist p (x + t • v) < δ := by
  rw [Tube, mem_thickening_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨t, ht, rfl⟩ := mem_segment_param.mp hq
    exact ⟨t, ht, hpq⟩
  · rintro ⟨t, ht, hpt⟩
    exact ⟨x + t • v, mem_segment_param.mpr ⟨t, ht, rfl⟩, hpt⟩

/-- Reversing the orientation of the axis does not change the tube. -/
theorem tube_flip (δ : ℝ) (x v : Space) : Tube δ (x + v) (-v) = Tube δ x v := by
  rw [Tube, Tube, add_neg_cancel_right, segment_symm]

end WangZahlLot.Obl.wz_compact_offset_normalization
