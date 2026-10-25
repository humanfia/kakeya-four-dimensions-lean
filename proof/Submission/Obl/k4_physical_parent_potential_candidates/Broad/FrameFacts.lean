-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/FrameFacts.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.GroupMeasure
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.GroupEvents

/-!
# Group events in the diagonal frame

Facts used to instantiate the sampled exit in the diagonal frame:

* placement: incidences whose time lies in the block and whose spatial base coordinates lie in
  `[y₀, y₀ + D/2]` have normalized base point in `[0, 1/2]³`, hence in the closed unit ball;
* speed: a trajectory with base velocity at most `Kv` and `4 h Kv ≤ D` moves its normalized
  base point at speed at most `1/h`;
* the hidden curvature of the transported test: `|nativeA| ≤ κ / (2δ)` when `|∂₃∂₃R_b| ≤ κB²/δ`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_physical_parent_potential_candidates.Analytic
open Submission.Obl.k4_quadratic_atlas_normalization

noncomputable section

/-- The corner of the frame: block start in time, `y₀` in space. -/
def frameCorner (t₀ : ℝ) (y₀ : Fin 2 → ℝ) : Fin 3 → ℝ := ![t₀, y₀ 0, y₀ 1]

lemma normalizedBase_frame_coord {h D t₀ : ℝ} (y₀ : Fin 2 → ℝ) (B : ℝ) (q : Ev) (i : Fin 3) :
    normalizedBase (frameShift h D (frameCorner t₀ y₀)) (frameMat h D) B (graphPoint q.1 q.2) i =
      (basePoint q i - frameCorner t₀ y₀ i) / frameScale h D i := by
  rw [normalizedBase_frame, graphPoint_castSucc_eq_basePoint]

/-- **Placement.** -/
lemma normalizedBase_frame_mem {h D t₀ : ℝ} (hh : 0 < h) (hD : 0 < D) (y₀ : Fin 2 → ℝ) (B : ℝ)
    {q : Ev} (ht : q.2 ∈ Icc t₀ (t₀ + h))
    (hy : ∀ e : Fin 2, y₀ e ≤ basePoint q e.succ ∧ basePoint q e.succ ≤ y₀ e + D / 2) :
    (∀ i, normalizedBase (frameShift h D (frameCorner t₀ y₀)) (frameMat h D) B
        (graphPoint q.1 q.2) i ∈ Icc (0:ℝ) (1 / 2)) ∧
      normalizedBase (frameShift h D (frameCorner t₀ y₀)) (frameMat h D) B
        (graphPoint q.1 q.2) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hc : ∀ i (lo hi : ℝ), lo ≤ basePoint q i → basePoint q i ≤ hi →
      frameCorner t₀ y₀ i = lo → hi ≤ lo + frameScale h D i / 2 →
      normalizedBase (frameShift h D (frameCorner t₀ y₀)) (frameMat h D) B
        (graphPoint q.1 q.2) i ∈ Icc (0:ℝ) (1 / 2) := by
    intro i lo hi hlo hhi hcl hlh
    rw [normalizedBase_frame_coord, hcl]
    have hs := frameScale_pos hh hD i
    rw [Set.mem_Icc, le_div_iff₀ hs, div_le_iff₀ hs]
    constructor <;> linarith
  have hb0 : basePoint q 0 = q.2 := basePoint_apply_zero q
  have hs0 : frameScale h D 0 = 2 * h := by simp [frameScale]
  have hs1 : frameScale h D 1 = D := by simp [frameScale]
  have hs2 : frameScale h D 2 = D := by simp [frameScale]
  have hc0 : frameCorner t₀ y₀ 0 = t₀ := by simp [frameCorner]
  have hc1 : frameCorner t₀ y₀ 1 = y₀ 0 := by simp [frameCorner]
  have hc2 : frameCorner t₀ y₀ 2 = y₀ 1 := by simp [frameCorner]
  have hy0 := hy 0
  have hy1 := hy 1
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hy0 hy1
  have h0 := hc 0 t₀ (t₀ + h) (by rw [hb0]; exact ht.1) (by rw [hb0]; exact ht.2) hc0
    (by rw [hs0]; linarith)
  have h1 := hc 1 (y₀ 0) (y₀ 0 + D / 2) hy0.1 hy0.2 hc1 (by rw [hs1])
  have h2 := hc 2 (y₀ 1) (y₀ 1 + D / 2) hy1.1 hy1.2 hc2 (by rw [hs2])
  have hcoord : ∀ i, normalizedBase (frameShift h D (frameCorner t₀ y₀)) (frameMat h D) B
      (graphPoint q.1 q.2) i ∈ Icc (0:ℝ) (1 / 2) := by
    intro i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
  refine ⟨hcoord, ?_⟩
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  rw [Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

/-- **Speed in the frame.** -/
lemma normalizedBase_frame_speed {h D Kv : ℝ} (hh : 0 < h) (hD : 0 < D) (hKv : 0 ≤ Kv)
    (hDK : 4 * h * Kv ≤ D) (z₀ : Fin 3 → ℝ) (B : ℝ) {l : Ln}
    (hl3 : |l.2 3| ≤ Kv) (hl4 : |l.2 4| ≤ Kv) (t s : ℝ) :
    ‖normalizedBase (frameShift h D z₀) (frameMat h D) B (graphPoint l t) -
        normalizedBase (frameShift h D z₀) (frameMat h D) B (graphPoint l s)‖ ≤
      h⁻¹ * |t - s| := by
  refine (norm_le_sum_abs_three _).trans ?_
  have hc : ∀ i, (normalizedBase (frameShift h D z₀) (frameMat h D) B (graphPoint l t) -
      normalizedBase (frameShift h D z₀) (frameMat h D) B (graphPoint l s)) i =
        (graphPoint l t i.castSucc - graphPoint l s i.castSucc) / frameScale h D i := by
    intro i
    rw [PiLp.sub_apply, normalizedBase_frame, normalizedBase_frame]
    ring
  rw [hc 0, hc 1, hc 2]
  have g0 : ∀ t, graphPoint l t (0 : Fin 3).castSucc = t := fun t => by simp [graphPoint]
  have g1 : ∀ t, graphPoint l t (1 : Fin 3).castSucc = l.2 0 + t * l.2 3 :=
    fun t => by simp [graphPoint]
  have g2 : ∀ t, graphPoint l t (2 : Fin 3).castSucc = l.2 1 + t * l.2 4 :=
    fun t => by simp [graphPoint]
  have hs0 : frameScale h D 0 = 2 * h := by simp [frameScale]
  have hs1 : frameScale h D 1 = D := by simp [frameScale]
  have hs2 : frameScale h D 2 = D := by simp [frameScale]
  rw [g0, g0, g1, g1, g2, g2, hs0, hs1, hs2]
  have hts : 0 ≤ |t - s| := abs_nonneg _
  have e1 : |(l.2 0 + t * l.2 3 - (l.2 0 + s * l.2 3)) / D| = |t - s| * |l.2 3| / D := by
    rw [abs_div, abs_of_pos hD, ← abs_mul]; ring_nf
  have e2 : |(l.2 1 + t * l.2 4 - (l.2 1 + s * l.2 4)) / D| = |t - s| * |l.2 4| / D := by
    rw [abs_div, abs_of_pos hD, ← abs_mul]; ring_nf
  have e0 : |(t - s) / (2 * h)| = |t - s| / (2 * h) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * h)]
  rw [e0, e1, e2]
  have hk : Kv / D ≤ 1 / (4 * h) := by
    rw [div_le_div_iff₀ hD (by positivity)]; linarith
  have b1 : |t - s| * |l.2 3| / D ≤ |t - s| * (1 / (4 * h)) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right hl3 hD.le).trans hk) hts
  have b2 : |t - s| * |l.2 4| / D ≤ |t - s| * (1 / (4 * h)) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right hl4 hD.le).trans hk) hts
  have : |t - s| / (2 * h) + |t - s| * (1 / (4 * h)) + |t - s| * (1 / (4 * h)) = h⁻¹ * |t - s| := by
    field_simp; ring
  linarith

/-- **Hidden curvature of the transported test.** -/
lemma abs_nativeA_transport_le {R0 : Poly} (hR0 : R0.totalDegree ≤ 2) (c' : Fin 3 → ℝ)
    (M' : Matrix (Fin 3) (Fin 3) ℝ) {B' Bv κ δ' : ℝ} (hBv : 0 < Bv) (hB' : B' * Bv = 1)
    (hδ : 0 < δ') (x₀ : Fin 4 → ℝ)
    (hcurv : |MvPolynomial.eval x₀ (pderiv 3 (pderiv 3 R0))| ≤ κ * Bv ^ 2 / δ') :
    |nativeA (transportPolynomial c' M' B' R0)| ≤ κ / (2 * δ') := by
  have hdeg : (transportPolynomial c' M' B' R0).totalDegree ≤ 2 :=
    (totalDegree_transportPolynomial_le _ _ _ _).trans hR0
  have hsec := second_pderiv_eq_curvature _ hdeg (3 : Fin 4)
  -- evaluate the constant second derivative at a point mapping to `x₀`
  have hdeg0 : (pderiv 3 (pderiv 3 R0)).totalDegree = 0 := by
    have h1 := Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred (pderiv 3 R0) 3
    have h2 := Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred R0 3
    omega
  have hev := (eval_transport_hidden_derivatives c' M' B' R0 (fun _ => 0)).2
  rw [hsec, MvPolynomial.eval_C] at hev
  rw [nativeA, hev, eval_eq_of_totalDegree_eq_zero hdeg0 _ x₀]
  have hB'v : B' = Bv⁻¹ := by field_simp; linarith [hB']
  rw [abs_div, abs_two, abs_mul, hB'v, abs_pow, abs_inv, abs_of_pos hBv]
  calc (Bv⁻¹) ^ 2 * |MvPolynomial.eval x₀ (pderiv 3 (pderiv 3 R0))| / 2
      ≤ (Bv⁻¹) ^ 2 * (κ * Bv ^ 2 / δ') / 2 := by gcongr
    _ = κ / (2 * δ') := by field_simp

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
