/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/ScalarFrames.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ScalarChange
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.WitnessChains
import Submission.Obl.k4_native_finite_terminal_atlas_lift.DyadicComposition

/-! Literal scalar coordinates and cumulative hidden depth for original-law frames. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- An original-law frame whose maps are one explicit quadratic scalar
normalization, with the exact original-resolution hidden scale. -/
structure ScalarFrame (p q : Code) (depth : ℝ) where
  frame : OriginalFrame p q
  change : (k : ℕ) → Fin (W q k) → ScalarChange
  generation : ℕ → ℕ
  block : (k : ℕ) → Fin (W q k) → Fin (2 ^ generation k)
  duration_eq : ∀ k i, (change k i).duration = frame.duration k
  duration_dyadic : ∀ k, frame.duration k = ((2 : ℝ) ^ generation k)⁻¹
  start_eq : ∀ k i, (change k i).start = ((block k i : ℕ) : ℝ) / (2 : ℝ) ^ generation k
  scale_eq : ∀ k i, (change k i).scale = N p (frame.sample k) ^ (-depth)
  coefficient_eq : ∀ k i, frame.coefficient k i = (change k i).trajectory
  incidence_eq : ∀ k i, frame.incidence k i = (change k i).incidence

namespace ScalarFrame

noncomputable section

variable {p q z : Code} {r s : ℝ}

def ofRefinement {b h : ℝ} (w : RefinementWitness p q r b h) (hp : Exact p) :
    ScalarFrame p q r where
  frame := OriginalFrame.ofRefinement w hp
  change k i :=
    { start := w.toRefinementData.start k i
      duration := w.toRefinementData.duration k
      center := w.center k i
      speed := w.speed k i
      width := w.width k i
      scale := N p (w.sample k) ^ (-r)
      polynomial := w.polynomial k i
      duration_pos := w.duration_pos k
      width_pos := w.width_pos k i
      scale_pos := Real.rpow_pos_of_pos (by linarith [hp.1.1 (w.sample k)]) _
      polynomial_degree := w.polynomial_degree k i }
  generation := w.T
  block := w.block
  duration_eq _ _ := rfl
  duration_dyadic _ := rfl
  start_eq _ _ := by simp only [RefinementData.start, RefinementData.duration, div_eq_mul_inv]
  scale_eq _ _ := rfl
  coefficient_eq _ _ := rfl
  incidence_eq _ _ := rfl

def refl (p : Code) (hp : Exact p) : ScalarFrame p p 0 where
  frame := OriginalFrame.refl p hp
  change _ _ := ScalarChange.refl
  generation _ := 0
  block _ _ := ⟨0, by norm_num⟩
  duration_eq _ _ := rfl
  duration_dyadic _ := by norm_num [OriginalFrame.refl]
  start_eq _ _ := by norm_num [ScalarChange.refl]
  scale_eq _ _ := by simp [ScalarChange.refl]
  coefficient_eq _ _ := ScalarChange.trajectory_refl.symm
  incidence_eq _ _ := ScalarChange.incidence_refl.symm

/-- Actual original-law composition remains a single scalar normalization;
the hidden depths add using the literal resolution identity. -/
def comp (parent : ScalarFrame p q r) (child : ScalarFrame q z s) (hp : Exact p) :
    ScalarFrame p z (r + s) where
  frame := parent.frame.comp child.frame
  change k i := (parent.change (child.frame.sample k) (child.frame.world k i)).comp
    (child.change k i)
  generation k := parent.generation (child.frame.sample k) + child.generation k
  block k i := Submission.Obl.k4_native_finite_terminal_atlas_lift.compositeBlock
    (parent.block (child.frame.sample k) (child.frame.world k i)) (child.block k i)
  duration_eq k i := by
    change (parent.change _ _).duration * (child.change k i).duration =
      parent.frame.duration _ * child.frame.duration k
    rw [parent.duration_eq, child.duration_eq]
  duration_dyadic k := by
    change parent.frame.duration _ * child.frame.duration k = _
    rw [parent.duration_dyadic, child.duration_dyadic]
    simp only [pow_add, mul_inv]
  start_eq k i := by
    change (parent.change _ _).start + (parent.change _ _).duration *
      (child.change k i).start = _
    rw [parent.start_eq, parent.duration_eq, parent.duration_dyadic, child.start_eq]
    rw [Submission.Obl.k4_native_finite_terminal_atlas_lift.compositeBlock_lower]
    ring
  scale_eq k i := by
    change (parent.change _ _).scale * (child.change k i).scale =
      N p (parent.frame.sample (child.frame.sample k)) ^ (-(r + s))
    rw [parent.scale_eq, child.scale_eq, parent.frame.resolution]
    rw [← Real.rpow_add (by linarith [hp.1.1 (parent.frame.sample (child.frame.sample k))])]
    congr 1
    ring
  coefficient_eq k i := by
    change (parent.frame.coefficient _ _).trans (child.frame.coefficient k i) = _
    rw [parent.coefficient_eq, child.coefficient_eq]
    exact (ScalarChange.trajectory_comp _ _).symm
  incidence_eq k i := by
    change (parent.frame.incidence _ _).trans (child.frame.incidence k i) = _
    rw [parent.incidence_eq, child.incidence_eq]
    exact (ScalarChange.incidence_comp _ _).symm

/-- Normalized unit time is exactly the actual original dyadic block. -/
theorem time_mem_iff (a : ScalarFrame p q r) (k : ℕ) (i : Fin (W q k)) (t : ℝ) :
    (t - (a.change k i).start) / (a.change k i).duration ∈ Set.Icc (0 : ℝ) 1 ↔
      t ∈ I (a.generation k) (a.block k i) := by
  have hq : 0 < (2 : ℝ) ^ a.generation k := by positivity
  rw [a.start_eq, a.duration_eq, a.duration_dyadic]
  change 0 ≤ (t - _) / _ ∧ (t - _) / _ ≤ 1 ↔ _ ≤ t ∧ t ≤ _
  rw [le_div_iff₀ (inv_pos.mpr hq), div_le_iff₀ (inv_pos.mpr hq)]
  simp only [zero_mul, one_mul]
  have hend : (((a.block k i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.generation k =
      ((a.block k i : ℕ) : ℝ) / (2 : ℝ) ^ a.generation k +
        ((2 : ℝ) ^ a.generation k)⁻¹ := by ring
  rw [hend]
  constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith

/-- Any later child block is the corresponding concatenated original
block, using the accepted dyadic concatenation identities. -/
theorem time_mem_childBlock_iff (a : ScalarFrame p q r) (k : ℕ) (i : Fin (W q k))
    (U : ℕ) (j : Fin (2 ^ U)) (t : ℝ) :
    (t - (a.change k i).start) / (a.change k i).duration ∈ I U j ↔
      t ∈ I (a.generation k + U)
        (Submission.Obl.k4_native_finite_terminal_atlas_lift.compositeBlock (a.block k i) j) := by
  have ht : ((a.block k i : ℕ) : ℝ) / (2 : ℝ) ^ a.generation k +
      ((t - (a.change k i).start) / (a.change k i).duration) /
        (2 : ℝ) ^ a.generation k = t := by
    rw [a.start_eq, a.duration_eq, a.duration_dyadic]
    field_simp
    ring
  have hc := Submission.Obl.k4_native_finite_terminal_atlas_lift.compositeBlock_interval
    (a.block k i) j ((t - (a.change k i).start) / (a.change k i).duration)
  rw [ht] at hc
  exact hc.symm

/-- A candidate at an additional child depth lifts to the sum of the
actual original depths, on the same original trajectory. -/
theorem lift_candidate_fit (a : ScalarFrame p q r) (hp : Exact p)
    (k : ℕ) (i : Fin (W q k)) (Q : MvPolynomial (Fin 2) ℝ)
    (l : ℕ × ScalarCoeff) (t gain error : ℝ)
    (hfit : |scalarX ((a.change k i).trajectory l).2
        ((t - (a.change k i).start) / (a.change k i).duration) -
      MvPolynomial.eval ![(t - (a.change k i).start) / (a.change k i).duration,
        scalarY ((a.change k i).trajectory l).2
          ((t - (a.change k i).start) / (a.change k i).duration)] Q| ≤
      N q k ^ (-gain) * error) :
    |scalarX l.2 t - MvPolynomial.eval ![t, scalarY l.2 t]
      ((a.change k i).liftPolynomial Q)| ≤
        N p (a.frame.sample k) ^ (-(r + gain)) * error := by
  rw [(a.change k i).abs_residual_lift, a.scale_eq]
  have h := mul_le_mul_of_nonneg_left hfit (a.change k i).scale_pos.le
  rw [a.scale_eq, a.frame.resolution] at h
  have hpow : N p (a.frame.sample k) ^ (-r) *
      N p (a.frame.sample k) ^ (-gain) =
      N p (a.frame.sample k) ^ (-(r + gain)) := by
    rw [← Real.rpow_add (by linarith [hp.1.1 (a.frame.sample k)])]
    congr 1
    ring
  simpa only [← mul_assoc, hpow] using h

/-- A whole-block child fit returns to its literal original dyadic block,
with an original quadratic predictor and the exact additive depth. -/
theorem lift_candidate_block_fit (a : ScalarFrame p q r) (hp : Exact p)
    (k : ℕ) (i : Fin (W q k)) (U : ℕ) (j : Fin (2 ^ U))
    (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q.totalDegree ≤ 2)
    (l : ℕ × ScalarCoeff) (gain error : ℝ)
    (hfit : ∀ τ ∈ I U j,
      |scalarX ((a.change k i).trajectory l).2 τ -
        MvPolynomial.eval ![τ, scalarY ((a.change k i).trajectory l).2 τ] Q| ≤
          N q k ^ (-gain) * error) :
    ∃ P : MvPolynomial (Fin 2) ℝ, P.totalDegree ≤ 2 ∧
      ∀ t ∈ I (a.generation k + U)
        (Submission.Obl.k4_native_finite_terminal_atlas_lift.compositeBlock (a.block k i) j),
        |scalarX l.2 t - MvPolynomial.eval ![t, scalarY l.2 t] P| ≤
          N p (a.frame.sample k) ^ (-(r + gain)) * error := by
  refine ⟨(a.change k i).liftPolynomial Q, (a.change k i).liftPolynomial_degree Q hQ, ?_⟩
  intro t ht
  apply a.lift_candidate_fit hp
  exact hfit _ ((a.time_mem_childBlock_iff k i U j t).2 ht)

end

end ScalarFrame

namespace PathNodes.GridPath

/-- The actual finite path has one original quadratic frame, with hidden
scale exactly N_original raised to minus the sum of its actual depths. -/
noncomputable def toScalarFrame {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets) (i : ℕ) :
    path.LayerWitnesses i →
      ScalarFrame (source.problem i) (path.finalFamily.problem i) (path.totalDepth i) :=
  match path with
  | .nil source _ => fun _ => ScalarFrame.refl (source.problem i) (source.angular i).1
  | .cons _ _ _ _ node tail => fun w =>
      (ScalarFrame.ofRefinement w.1 (source.angular i).1).comp
        (tail.toScalarFrame i w.2) (source.angular i).1

/-- The scalar description retains exactly the original-law frame already
constructed from the same individual layer witnesses. -/
theorem toScalarFrame_frame {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets) (i : ℕ)
    (w : path.LayerWitnesses i) :
    (path.toScalarFrame i w).frame = path.toOriginalFrame i w := by
  induction path with
  | nil => rfl
  | cons r rs hstart hr node tail ih =>
    change (OriginalFrame.ofRefinement w.1 _).comp (tail.toScalarFrame i w.2).frame =
      (OriginalFrame.ofRefinement w.1 _).comp (tail.toOriginalFrame i w.2)
    rw [ih w.2]

theorem eventually_scalarFrames {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets) :
    ∀ᶠ i in atTop, Nonempty
      (ScalarFrame (source.problem i) (path.finalFamily.problem i) (path.totalDepth i)) := by
  filter_upwards [path.eventually_allLayers] with i hi
  obtain ⟨w⟩ := path.nonempty_layerWitnesses i hi
  exact ⟨path.toScalarFrame i w⟩

end PathNodes.GridPath

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
