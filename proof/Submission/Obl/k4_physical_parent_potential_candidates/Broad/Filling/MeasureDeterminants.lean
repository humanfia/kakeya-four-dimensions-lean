-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Filling/MeasureDeterminants.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o106, branch x0352, commit dcdf5bd50e74;
-- source Submission/Obl/k4_isotropic_path_improvement/MeasureDeterminants.lean (session x0352).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Filling.MeasureCapture
import Submission.Lib.K4ContinuousKakeya.Continuous

/-!
Quantitative determinant success under an arbitrary finite direction law.
Finite capture supplies actual representatives, and the accepted determinant
perturbation estimate transfers every successful code box back to its sources.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad.Filling

open MeasureTheory Set

noncomputable section

open Classical in
/-- Independent source coding has exactly the product of its original
fiber weights, including on the set of good spanning code tuples. -/
theorem good_code_tuple_mass {Ω : Type*} [MeasurableSpace Ω] {d n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → Fin n) (hcode : Measurable code)
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (ρ : ℝ) :
    (∑ I : Fin d → Fin n, if Breadth.Good v ρ I then ∏ j, codeWeight μ code (I j) else 0) =
      (Measure.pi (fun _ : Fin d => μ)).real
        {T : Fin d → Ω | Breadth.Good v ρ (fun j => code (T j))} := by
  classical
  let χ : (Fin d → Ω) → (Fin d → Fin n) := fun T j => code (T j)
  let Q : Finset (Fin d → Fin n) := Finset.univ.filter (Breadth.Good v ρ)
  have hχ : Measurable χ := Measurable.of_eval fun j =>
    hcode.comp (measurable_pi_apply j)
  have hfiber (I : Fin d → Fin n) :
      (Measure.pi (fun _ : Fin d => μ)).real (χ ⁻¹' {I}) =
        ∏ j, codeWeight μ code (I j) := by
    have hset : χ ⁻¹' {I} = Set.univ.pi (fun j => code ⁻¹' {I j}) := by
      ext T
      simp only [mem_preimage, mem_singleton_iff, mem_pi, mem_univ, forall_const, χ]
      exact funext_iff
    rw [hset]
    simp only [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod, codeWeight]
  have hsum := sum_measureReal_preimage_singleton (μ := Measure.pi (fun _ : Fin d => μ)) Q
    (fun I _ => hχ (measurableSet_singleton I))
  have hset : χ ⁻¹' (Q : Set (Fin d → Fin n)) =
      {T : Fin d → Ω | Breadth.Good v ρ (fun j => code (T j))} := by
    ext T
    simp [Q, χ]
  rw [hset] at hsum
  rw [← hsum]
  simp only [Q, Finset.sum_filter, hfiber]

/-- A sufficiently accurate finite capture transfers its spanning-tuple
mass to a determinant event for the ACTUAL independent source samples. -/
theorem captured_determinant_success {Ω : Type*} [MeasurableSpace Ω] {d n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (e : Ω → EuclideanSpace ℝ (Fin d))
    (he : ∀ x, ‖e x‖ ≤ 1) (code : Ω → Fin n) (hcode : Measurable code) (rep : Fin n → Ω)
    (ρ ε c β : ℝ) (hc : 0 ≤ c) (hρε : 0 ≤ ρ - ε)
    (herr : ∀ x, dist (e x) (e (rep (code x))) ≤ ε)
    (hbroad : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ V < d →
      c * μ.real univ ≤ μ.real {x | ρ ≤ Metric.infDist (e x) (V : Set _)})
    (hmargin : β + (d.factorial * d : ℝ) * ε ≤ (ρ - ε) ^ d) :
    (c * μ.real univ) ^ d ≤ (Measure.pi (fun _ : Fin d => μ)).real
      {T : Fin d → Ω | β ≤ |(Matrix.of fun i j : Fin d => e (T i) j).det|} := by
  classical
  have hb := capture_breadth μ code hcode rep e univ (by simp) ρ ε c herr
    (by simpa only [mem_univ, true_and] using hbroad)
  simp only [Set.indicator_of_mem (Set.mem_univ _), mul_one] at hb
  have hgood := Breadth.good_weight (fun i => e (rep i)) (codeWeight μ code)
    (fun _ => measureReal_nonneg) (ρ - ε) c hc hb d le_rfl
  rw [sum_codeWeight μ code hcode, good_code_tuple_mass μ code hcode] at hgood
  refine hgood.trans (measureReal_mono ?_)
  intro T hT
  have hprod := Finset.prod_le_prod₀
    (fun _ (_ : _ ∈ (Finset.univ : Finset (Fin d))) => hρε)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hT i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hlower := hprod.trans (Breadth.abs_det_ge_prod_infDist d
    (fun i => e (rep (code (T i)))))
  have hperturb := Submission.Lib.K4ContinuousKakeya.abs_det_sub_le
    (fun i => e (T i)) (fun i => e (rep (code (T i)))) ε
    (fun i => he (T i)) (fun i => he (rep (code (T i))))
    (fun i => by simpa only [dist_eq_norm] using herr (T i))
  have htriangle := abs_sub_abs_le_abs_sub
    (Matrix.of fun i j : Fin d => e (rep (code (T i))) j).det
    (Matrix.of fun i j : Fin d => e (T i) j).det
  rw [abs_sub_comm] at htriangle
  change β ≤ _
  linarith

/-- Proper-subspace breadth gives a quantitative determinant-success
probability for arbitrary finite laws, with its original total mass. -/
theorem determinant_success_of_breadth {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (e : Ω → EuclideanSpace ℝ (Fin d))
    (he : Measurable e) (hbound : ∀ x, ‖e x‖ ≤ 1)
    (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hbroad : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ V < d →
      c * μ.real univ ≤ μ.real {x | ρ ≤ Metric.infDist (e x) (V : Set _)}) :
    (c * μ.real univ) ^ d ≤ (Measure.pi (fun _ : Fin d => μ)).real
      {T : Fin d → Ω | (ρ / 2) ^ d / 2 ≤ |(Matrix.of fun i j : Fin d => e (T i) j).det|} := by
  let A : ℝ := d.factorial * d
  let q : ℝ := (ρ / 2) ^ d
  let ε : ℝ := min (ρ / 2) (q / (2 * (A + 1)))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hq : 0 < q := pow_pos (by positivity) d
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεhalf : ε ≤ ρ / 2 := min_le_left _ _
  have hεq : ε ≤ q / (2 * (A + 1)) := min_le_right _ _
  have hεbound : A * ε ≤ q / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (A + 1))).mp hεq
    nlinarith
  have hρε : 0 ≤ ρ - ε := by linarith
  have hpower : q ≤ (ρ - ε) ^ d := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ ρ / 2) (by linarith) d
  obtain ⟨n, code, rep, hcode, _, herr, _⟩ := exists_bounded_vector_event_capture
    e he 1 hbound 0 (fun _ : Fin 0 => ∅) (by simp) ε hε
  apply captured_determinant_success μ e hbound code hcode rep ρ ε c (q / 2) hc hρε
    herr hbroad
  change q / 2 + A * ε ≤ _
  linarith

/-- Cell breadth gives determinant-success mass in the ORIGINAL independent
incidence law, with every sampled incidence lying in the same cell. -/
theorem determinant_success_in_cell {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω)
    (e : Ω → EuclideanSpace ℝ (Fin d)) (he : Measurable e)
    (hbound : ∀ x, ‖e x‖ ≤ 1) (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hbroad : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ V < d →
      c * μ.real S ≤ (μ.restrict S).real
        {x | ρ ≤ Metric.infDist (e x) (V : Set _)}) :
    (c * μ.real S) ^ d ≤ (Measure.pi (fun _ : Fin d => μ)).real
      {T : Fin d → Ω | (∀ i, T i ∈ S) ∧
        (ρ / 2) ^ d / 2 ≤ |(Matrix.of fun i j : Fin d => e (T i) j).det|} := by
  have htotal : (μ.restrict S).real univ = μ.real S := by simp [measureReal_def]
  have h := determinant_success_of_breadth (μ.restrict S) e he hbound ρ c hρ hc
    (by simpa only [htotal] using hbroad)
  rw [htotal] at h
  have hm : Measurable fun T : Fin d → Ω => (Matrix.of fun i j : Fin d => e (T i) j).det := by
    have hdet : Continuous (Matrix.det : Matrix (Fin d) (Fin d) ℝ → ℝ) :=
      continuous_id.matrix_det
    apply hdet.measurable.comp
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).measurable.comp
      (he.comp (measurable_pi_apply i))
  have hD : MeasurableSet {T : Fin d → Ω |
      (ρ / 2) ^ d / 2 ≤ |(Matrix.of fun i j : Fin d => e (T i) j).det|} :=
    measurableSet_le measurable_const hm.abs
  change _ ≤ ((Measure.pi (fun _ : Fin d => μ.restrict S)) _).toReal at h
  rw [← Measure.restrict_pi_pi, Measure.restrict_apply hD] at h
  have hset : {T : Fin d → Ω |
      (ρ / 2) ^ d / 2 ≤ |(Matrix.of fun i j : Fin d => e (T i) j).det|} ∩
        Set.univ.pi (fun _ : Fin d => S) =
      {T : Fin d → Ω | (∀ i, T i ∈ S) ∧
        (ρ / 2) ^ d / 2 ≤ |(Matrix.of fun i j : Fin d => e (T i) j).det|} := by
    ext T
    simp only [mem_inter_iff, mem_ofPred_eq, mem_pi, mem_univ, forall_const]
    exact and_comm
  rwa [hset] at h

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad.Filling
