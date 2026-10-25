-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Normalize.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Basic

/-!
# A unit plane field on a coarse set

The plane map `P` of a family is 1-Lipschitz and has unit length on the fine set only. On a
union of coarse cubes near the fine set, `p ↦ P (pc + (1 - 4 s) • (p - pc)) / ‖⋯‖` is a unit
field which is still exactly 1-Lipschitz, provided the coarse set lies in a ball of radius
`2/5` about `pc` and every coarse point is within `2 s` of a fine point: the contraction of the
argument pays for the expansion of the radial normalization near the unit sphere.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

/-- Radial normalization. -/
noncomputable def unitize (x : Space) : Space := ‖x‖⁻¹ • x

lemma norm_unitize {x : Space} (hx : x ≠ 0) : ‖unitize x‖ = 1 := by
  unfold unitize
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- `‖x‖ ‖y‖ ‖x/‖x‖ - y/‖y‖‖² ≤ ‖x - y‖²`. -/
lemma mul_norm_sq_unitize_sub_le {x y : Space} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x‖ * ‖y‖ * ‖unitize x - unitize y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h1 : ‖unitize x - unitize y‖ ^ 2 = 2 - 2 * (⟪x, y⟫ / (‖x‖ * ‖y‖)) := by
    rw [@norm_sub_sq_real, norm_unitize hx, norm_unitize hy]
    unfold unitize
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
    ring
  have h2 : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := @norm_sub_sq_real _ _ _ x y
  rw [h1, h2]
  have : ‖x‖ * ‖y‖ * (2 - 2 * (⟪x, y⟫ / (‖x‖ * ‖y‖))) = 2 * ‖x‖ * ‖y‖ - 2 * ⟪x, y⟫ := by
    field_simp
  rw [this]
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

lemma dist_unitize_le {x y : Space} {r : ℝ} (hr : 0 < r) (hx : r ≤ ‖x‖) (hy : r ≤ ‖y‖) :
    dist (unitize x) (unitize y) ≤ dist x y / r := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hr.trans_le hx)
  have hy0 : y ≠ 0 := norm_pos_iff.mp (hr.trans_le hy)
  rw [dist_eq_norm, dist_eq_norm, le_div_iff₀ hr]
  have h := mul_norm_sq_unitize_sub_le hx0 hy0
  have hrr : r * r ≤ ‖x‖ * ‖y‖ := mul_le_mul hx hy hr.le (norm_nonneg _)
  have h3 : (r * ‖unitize x - unitize y‖) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    calc (r * ‖unitize x - unitize y‖) ^ 2 = r * r * ‖unitize x - unitize y‖ ^ 2 := by ring
      _ ≤ ‖x‖ * ‖y‖ * ‖unitize x - unitize y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hrr (sq_nonneg _)
      _ ≤ _ := h
  have h4 := (sq_le_sq₀ (mul_nonneg hr.le (norm_nonneg _)) (norm_nonneg _)).mp h3
  linarith

lemma dist_unitize_self_le {x w : Space} (hw : ‖w‖ = 1) (hx : x ≠ 0) :
    dist (unitize x) x ≤ dist x w := by
  rw [dist_eq_norm, dist_eq_norm]
  unfold unitize
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : ‖x‖⁻¹ • x - x = (‖x‖⁻¹ - 1) • x := by rw [sub_smul, one_smul]
  rw [he, norm_smul, Real.norm_eq_abs]
  have h1 : |‖x‖⁻¹ - 1| * ‖x‖ = |1 - ‖x‖| := by
    rw [← abs_of_pos hnx, ← abs_mul, abs_of_pos hnx]
    congr 1
    field_simp
  rw [h1]
  have h2 := abs_norm_sub_norm_le x w
  rw [hw] at h2
  rw [abs_sub_comm]
  exact h2

/-- The unit plane field on a coarse set. -/
noncomputable def unitField (P : Space → Space) (pc : Space) (s : ℝ) (p : Space) : Space :=
  unitize (P (pc + (1 - 4 * s) • (p - pc)))

theorem unitField_spec {P : Space → Space} (hP : LipschitzWith 1 P) {pc : Space} {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1 / 20) {E : Set Space} (hE : E ⊆ ball pc (2 / 5))
    (hnear : ∀ p ∈ E, ∃ p', ‖P p'‖ = 1 ∧ dist p p' ≤ 2 * s) :
    (∀ p ∈ E, ‖unitField P pc s p‖ = 1) ∧
    (∀ p ∈ E, ∀ q ∈ E, dist (unitField P pc s p) (unitField P pc s q) ≤ dist p q) ∧
    (∀ p ∈ E, ∀ p', ‖P p'‖ = 1 → dist p p' ≤ 2 * s →
      dist (unitField P pc s p) (P p') ≤ 8 * s) := by
  set c := 1 - 4 * s with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  -- the contracted point is close to a fine point
  have hφ : ∀ p ∈ E, ∀ p' : Space, dist p p' ≤ 2 * s →
      dist (pc + c • (p - pc)) p' ≤ 18 / 5 * s := by
    intro p hp p' hpp'
    have h1 : dist (pc + c • (p - pc)) p = 4 * s * dist p pc := by
      rw [dist_eq_norm, dist_eq_norm]
      have : pc + c • (p - pc) - p = (-(4 * s)) • (p - pc) := by rw [hc]; module
      rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith)]
    have h2 : dist p pc < 2 / 5 := mem_ball.mp (hE hp)
    calc dist (pc + c • (p - pc)) p' ≤ dist (pc + c • (p - pc)) p + dist p p' :=
          dist_triangle _ _ _
      _ ≤ 4 * s * (2 / 5) + 2 * s := by
          rw [h1]; gcongr
      _ = 18 / 5 * s := by ring
  have hnorm : ∀ p ∈ E, 1 - 18 / 5 * s ≤ ‖P (pc + c • (p - pc))‖ := by
    intro p hp
    obtain ⟨p', hp'1, hpp'⟩ := hnear p hp
    have h := hφ p hp p' hpp'
    have hl : dist (P (pc + c • (p - pc))) (P p') ≤ dist (pc + c • (p - pc)) p' := by
      simpa using hP.dist_le_mul (pc + c • (p - pc)) p'
    have h3 := abs_norm_sub_norm_le (P (pc + c • (p - pc))) (P p')
    rw [hp'1, ← dist_eq_norm] at h3
    have := (abs_le.mp (h3.trans (hl.trans h))).1
    linarith
  have hr : 0 < 1 - 18 / 5 * s := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact norm_unitize (norm_pos_iff.mp (hr.trans_le (hnorm p hp)))
  · intro p hp q hq
    calc dist (unitField P pc s p) (unitField P pc s q)
        ≤ dist (P (pc + c • (p - pc))) (P (pc + c • (q - pc))) / (1 - 18 / 5 * s) :=
          dist_unitize_le hr (hnorm p hp) (hnorm q hq)
      _ ≤ dist (pc + c • (p - pc)) (pc + c • (q - pc)) / (1 - 18 / 5 * s) := by
          gcongr
          simpa using hP.dist_le_mul (pc + c • (p - pc)) (pc + c • (q - pc))
      _ = c * dist p q / (1 - 18 / 5 * s) := by
          congr 1
          rw [dist_eq_norm, dist_eq_norm]
          have : pc + c • (p - pc) - (pc + c • (q - pc)) = c • (p - q) := by module
          rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
      _ ≤ dist p q := by
          rw [div_le_iff₀ hr]
          have : c ≤ 1 - 18 / 5 * s := by rw [hc]; linarith
          nlinarith [dist_nonneg (x := p) (y := q)]
  · intro p hp p' hp'1 hpp'
    have h := hφ p hp p' hpp'
    have hl0 : dist (P (pc + c • (p - pc))) (P p') ≤ dist (pc + c • (p - pc)) p' := by
      simpa using hP.dist_le_mul (pc + c • (p - pc)) p'
    have hl : dist (P (pc + c • (p - pc))) (P p') ≤ 18 / 5 * s := hl0.trans h
    have hx0 : P (pc + c • (p - pc)) ≠ 0 := norm_pos_iff.mp (hr.trans_le (hnorm p hp))
    calc dist (unitField P pc s p) (P p')
        ≤ dist (unitize (P (pc + c • (p - pc)))) (P (pc + c • (p - pc))) +
          dist (P (pc + c • (p - pc))) (P p') := dist_triangle _ _ _
      _ ≤ dist (P (pc + c • (p - pc))) (P p') + dist (P (pc + c • (p - pc))) (P p') :=
          add_le_add (dist_unitize_self_le hp'1 hx0) le_rfl
      _ ≤ 8 * s := by linarith

/-- The horizontal part `(a 0, a 1, 0)` of a vector. -/
noncomputable def horiz (a : Space) : Space := pt (a 0) (a 1) 0

lemma norm_horiz_sq (a : Space) : ‖horiz a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Fin.sum_univ_three, horiz, pt]

lemma norm_sq_eq_three (a : Space) : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Fin.sum_univ_three]

lemma horiz_sub (a b : Space) : horiz (a - b) = horiz a - horiz b := by
  ext i
  fin_cases i <;> simp [horiz, pt]

lemma norm_horiz_le (a : Space) : ‖horiz a‖ ≤ ‖a‖ := by
  have h1 := norm_horiz_sq a
  have h2 := norm_sq_eq_three a
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg (a 2)])

/-- A unit vector almost orthogonal to a quantitatively non-horizontal unit vector has a
quantitatively large horizontal part. -/
lemma norm_horiz_ge_of_perp {v w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {δ θ : ℝ}
    (hθ0 : 0 ≤ θ) (hvθ : θ ≤ |v 2|) (hθ1 : θ ≤ 1) (hvw : |⟪v, w⟫| ≤ δ) :
    (θ - δ) / 2 ≤ ‖horiz w‖ := by
  have hinner : ⟪v, w⟫ = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]
  have hhv : ⟪horiz v, horiz w⟫ = v 0 * w 0 + v 1 * w 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_three, horiz, pt, mul_comm]
  have hcs : |⟪horiz v, horiz w⟫| ≤ ‖horiz v‖ * ‖horiz w‖ := abs_real_inner_le_norm _ _
  have hvh : ‖horiz v‖ ≤ 1 := (norm_horiz_le v).trans hv.le
  have hw2 : 1 - ‖horiz w‖ ≤ |w 2| := by
    have h1 := norm_horiz_sq w
    have h2 := norm_sq_eq_three w
    rw [hw] at h2
    have hh : 0 ≤ ‖horiz w‖ := norm_nonneg _
    by_contra hlt
    push Not at hlt
    have hsq : |w 2| ^ 2 < (1 - ‖horiz w‖) ^ 2 := by
      have := abs_nonneg (w 2)
      nlinarith
    rw [sq_abs] at hsq
    nlinarith
  have hv2 : |v 2 * w 2| ≤ δ + ‖horiz w‖ := by
    have e : v 2 * w 2 = ⟪v, w⟫ - (v 0 * w 0 + v 1 * w 1) := by rw [hinner]; ring
    rw [e]
    calc |⟪v, w⟫ - (v 0 * w 0 + v 1 * w 1)| ≤ |⟪v, w⟫| + |v 0 * w 0 + v 1 * w 1| :=
          abs_sub _ _
      _ ≤ δ + 1 * ‖horiz w‖ := by
          rw [← hhv]
          exact add_le_add hvw (hcs.trans (mul_le_mul_of_nonneg_right hvh (norm_nonneg _)))
      _ = δ + ‖horiz w‖ := by ring
  rw [abs_mul] at hv2
  have hh : 0 ≤ ‖horiz w‖ := norm_nonneg _
  have hθ0 : 0 ≤ |v 2| := abs_nonneg _
  have : θ * (1 - ‖horiz w‖) ≤ |v 2| * |w 2| := by
    by_cases h : 1 - ‖horiz w‖ ≤ 0
    · nlinarith [abs_nonneg (w 2), abs_nonneg (v 2)]
    · push Not at h
      exact mul_le_mul hvθ hw2 h.le hθ0
  nlinarith

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
