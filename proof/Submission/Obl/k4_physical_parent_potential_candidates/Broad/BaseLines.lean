-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/BaseLines.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Interface
import Submission.Lib.K4ContinuousKakeya.Incidence

/-!
# Base lines of trajectories, their tubes and their time in a cell

The base point of an incidence `(l, t)` is `(t, l₀ + t l₃, l₁ + t l₄)`; along `l` it moves on
the base line through `(0, l₀, l₁)` with direction `(1, l₃, l₄)`.  For the base-filling
estimate we need, for trajectories in a bounded family `Λ`:

* the unit base direction and a bounded anchor (the anchor is clamped outside `Λ`);
* every point of a base cell of diameter at most `D` met by a trajectory lies in the tube of
  radius `R > D` about the trajectory's full base line (`mem_tube_of_cell`);
* a trajectory spends time at most `p` in a cell whose time extent is at most `p`, so the
  pushforward to trajectories of the incidences in the cell is at most `p` times the prior
  (`push_le_of_time_extent`, from lib's `map_fst_restrict_le`).
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set
open Submission.Lib.K4ContinuousKakeya
open scoped NNReal ENNReal

noncomputable section

/-- The base point `(t, y(l,t))` of an incidence. -/
def basePoint (q : Ev) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![q.2, q.1.2 0 + q.2 * q.1.2 3, q.1.2 1 + q.2 * q.1.2 4]

/-- The (unnormalized) base velocity `(1, l₃, l₄)`. -/
def baseVel (l : Ln) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![1, l.2 3, l.2 4]

/-- The base anchor `(0, l₀, l₁)`. -/
def baseAnchor0 (l : Ln) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![0, l.2 0, l.2 1]

lemma basePoint_eq (l : Ln) (t : ℝ) : basePoint (l, t) = baseAnchor0 l + t • baseVel l := by
  ext i
  fin_cases i <;> simp [basePoint, baseAnchor0, baseVel]

lemma one_le_norm_baseVel (l : Ln) : 1 ≤ ‖baseVel l‖ := by
  have h := (EuclideanSpace.norm_eq (baseVel l))
  rw [h, Fin.sum_univ_three]
  have : (1:ℝ) ≤ ‖(baseVel l) 0‖ ^ 2 + ‖(baseVel l) 1‖ ^ 2 + ‖(baseVel l) 2‖ ^ 2 := by
    have h0 : ‖(baseVel l) 0‖ = 1 := by simp [baseVel]
    rw [h0]; nlinarith [sq_nonneg ‖(baseVel l) 1‖, sq_nonneg ‖(baseVel l) 2‖]
  calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt this

/-- The unit base direction. -/
def baseDir (l : Ln) : EuclideanSpace ℝ (Fin 3) := ‖baseVel l‖⁻¹ • baseVel l

lemma norm_baseDir (l : Ln) : ‖baseDir l‖ = 1 := by
  have h := one_le_norm_baseVel l
  rw [baseDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (by linarith)]

/-- The anchor, clamped to the ball of radius `Bd`. -/
def baseAnchor (Bd : ℝ) (l : Ln) : EuclideanSpace ℝ (Fin 3) :=
  if ‖baseAnchor0 l‖ ≤ Bd then baseAnchor0 l else 0

lemma norm_baseAnchor_le {Bd : ℝ} (hBd : 0 ≤ Bd) (l : Ln) : ‖baseAnchor Bd l‖ ≤ Bd := by
  unfold baseAnchor
  split_ifs with h
  · exact h
  · simpa using hBd

lemma measurable_basePoint : Measurable basePoint := by
  apply (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp
  refine Measurable.of_eval (fun i => ?_)
  fin_cases i
  · exact measurable_snd
  · exact ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_fst)).add
      (measurable_snd.mul ((measurable_pi_apply 3).comp (measurable_snd.comp measurable_fst)))
  · exact ((measurable_pi_apply 1).comp (measurable_snd.comp measurable_fst)).add
      (measurable_snd.mul ((measurable_pi_apply 4).comp (measurable_snd.comp measurable_fst)))

lemma measurable_baseVel : Measurable baseVel := by
  apply (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp
  refine Measurable.of_eval (fun i => ?_)
  fin_cases i
  · exact measurable_const
  · exact (measurable_pi_apply 3).comp measurable_snd
  · exact (measurable_pi_apply 4).comp measurable_snd

lemma measurable_baseAnchor0 : Measurable baseAnchor0 := by
  apply (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp
  refine Measurable.of_eval (fun i => ?_)
  fin_cases i
  · exact measurable_const
  · exact (measurable_pi_apply 0).comp measurable_snd
  · exact (measurable_pi_apply 1).comp measurable_snd

lemma measurable_baseDir : Measurable baseDir :=
  (measurable_baseVel.norm.inv).smul measurable_baseVel

lemma measurable_baseAnchor (Bd : ℝ) : Measurable (baseAnchor Bd) := by
  unfold baseAnchor
  refine Measurable.ite ?_ measurable_baseAnchor0 measurable_const
  exact measurableSet_le measurable_baseAnchor0.norm measurable_const

/-- The base point lies on the line through the (unclamped) anchor in the unit direction. -/
lemma basePoint_mem_line (l : Ln) (t : ℝ) :
    basePoint (l, t) ∈ Set.range fun s : ℝ => baseAnchor0 l + s • baseDir l := by
  refine ⟨t * ‖baseVel l‖, ?_⟩
  have h := one_le_norm_baseVel l
  show baseAnchor0 l + (t * ‖baseVel l‖) • (‖baseVel l‖⁻¹ • baseVel l) = basePoint (l, t)
  rw [basePoint_eq, smul_smul, mul_assoc, mul_inv_cancel₀ (by linarith), mul_one]

/-- **Tubes.**  If an incidence of a trajectory with bounded anchor lies in a cell of diameter
less than `r`, every point of the cell lies in the tube of radius `r` about the trajectory's
full base line. -/
theorem mem_tube_of_cell {Bd r : ℝ} {l : Ln} (hl : ‖baseAnchor0 l‖ ≤ Bd) {t : ℝ}
    {E : Set (EuclideanSpace ℝ (Fin 3))} (hq : basePoint (l, t) ∈ E)
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, dist x y < r) :
    ∀ x ∈ E, x ∈ tube r (baseAnchor Bd l) (baseDir l) := by
  intro x hx
  have hanchor : baseAnchor Bd l = baseAnchor0 l := by simp [baseAnchor, hl]
  rw [tube, hanchor, Metric.mem_thickening_iff]
  exact ⟨basePoint (l, t), basePoint_mem_line l t, hdiam x hx _ hq⟩

/-- **Time in a cell.**  The incidences of `Λ` in a cell whose time extent is at most `p` push
forward to trajectories below `p` times the prior. -/
theorem push_le_of_time_extent (θ : Measure Ln) [SFinite θ] (inc : Measure Ev)
    (hinc : inc ≤ θ.prod volume) (Λ : Set Ln) (hΛ : MeasurableSet Λ)
    (E : Set (EuclideanSpace ℝ (Fin 3))) (hE : MeasurableSet E) (p : ℝ)
    (t₀ : ℝ) (htime : ∀ x ∈ E, x 0 ∈ Icc t₀ (t₀ + p)) :
    (inc.restrict {ω | ω.1 ∈ Λ ∧ basePoint ω ∈ E}).map Prod.fst ≤
      p.toNNReal • θ.restrict Λ := by
  have hS : MeasurableSet {ω : Ev | ω.1 ∈ Λ ∧ basePoint ω ∈ E} :=
    (measurable_fst hΛ).inter (measurable_basePoint hE)
  have hinc' : inc ≤ (1 : ℝ≥0) • θ.prod volume := by simpa using hinc
  have h := map_fst_restrict_le θ inc 1 p.toNNReal hinc' _ hS Λ hΛ (fun ω hω => hω.1) ?_
  · simpa using h
  intro l _
  calc volume {t : ℝ | (l, t) ∈ {ω : Ev | ω.1 ∈ Λ ∧ basePoint ω ∈ E}}
      ≤ volume (Icc t₀ (t₀ + p)) := by
        apply measure_mono
        intro t ht
        have := htime _ ht.2
        simpa [basePoint] using this
    _ = (p.toNNReal : ℝ≥0∞) := by
        rw [Real.volume_Icc, add_sub_cancel_left, ENNReal.ofReal]

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
