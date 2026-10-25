-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Filling/MeasureCapture.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o106, branch x0352, commit dcdf5bd50e74;
-- source Submission/Obl/k4_isotropic_path_improvement/MeasureCapture.lean (session x0352).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Filling.BroadLineFamily
import Submission.Lib.K4ContinuousPlanks.Discretization
import Submission.Obl.k4_adapted_oscillation_tests.Glue

/-!
Finite capture of a continuous line law. A finite code records exact tube
membership at the tested cells and approximates only the direction. Its
weights are masses under the unchanged original measure.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad.Filling

open MeasureTheory Set
open scoped BigOperators
open Submission.Obl.k4_mk_grid_transfer

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

def codeWeight {n : ℕ} (μ : Measure Ω) (code : Ω → Fin n) (i : Fin n) : ℝ :=
  μ.real (code ⁻¹' {i})

theorem sum_codeWeight {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → Fin n) (hcode : Measurable code) :
    (∑ i, codeWeight μ code i) = μ.real univ := by
  simpa only [codeWeight, Finset.coe_univ, preimage_univ] using
    sum_measureReal_preimage_singleton (μ := μ) Finset.univ
      (fun i _ => hcode (measurableSet_singleton i))

theorem sum_codeWeight_predicate {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → Fin n) (hcode : Measurable code) (P : Fin n → Prop) [DecidablePred P] :
    (∑ i, if P i then codeWeight μ code i else 0) = μ.real {x | P (code x)} := by
  classical
  rw [← Finset.sum_filter]
  have h := sum_measureReal_preimage_singleton (μ := μ) (Finset.univ.filter P)
    (fun i _ => hcode (measurableSet_singleton i))
  have hset : code ⁻¹' (↑(Finset.univ.filter P) : Set (Fin n)) = {x | P (code x)} := by
    ext x
    simp
  rw [hset] at h
  exact h

/-- Exact event information in the code preserves its original measure. -/
theorem sum_codeWeight_indicator {n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → Fin n) (hcode : Measurable code) (rep : Fin n → Ω) (S : Set Ω)
    (hS : ∀ x, rep (code x) ∈ S ↔ x ∈ S) :
    (∑ i, codeWeight μ code i * S.indicator (fun _ => (1 : ℝ)) (rep i)) = μ.real S := by
  classical
  simp only [Set.indicator_apply, mul_ite, mul_one, mul_zero]
  rw [sum_codeWeight_predicate μ code hcode]
  congr 1
  ext x
  exact hS x

omit [MeasurableSpace Ω] in
/-- Direction error costs an additive amount in distance from every subspace. -/
theorem infDist_representative_lower {d : ℕ}
    (e : Ω → EuclideanSpace ℝ (Fin d)) {n : ℕ} (code : Ω → Fin n) (rep : Fin n → Ω)
    (ε : ℝ) (herr : ∀ x, dist (e x) (e (rep (code x))) ≤ ε)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (x : Ω) (ρ : ℝ)
    (hx : ρ ≤ Metric.infDist (e x) (V : Set _)) :
    ρ - ε ≤ Metric.infDist (e (rep (code x))) (V : Set _) := by
  have h := Metric.infDist_le_infDist_add_dist
    (x := e x) (y := e (rep (code x))) (s := (V : Set _))
  linarith [herr x]

/-- Breadth survives finite capture, with the original cell mass as denominator. -/
theorem capture_breadth {d n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → Fin n) (hcode : Measurable code) (rep : Fin n → Ω)
    (e : Ω → EuclideanSpace ℝ (Fin d)) (S : Set Ω)
    (hS : ∀ x, rep (code x) ∈ S ↔ x ∈ S)
    (ρ ε c : ℝ) (herr : ∀ x, dist (e x) (e (rep (code x))) ≤ ε)
    (hbroad : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ V < d →
      c * μ.real S ≤ μ.real {x | x ∈ S ∧ ρ ≤ Metric.infDist (e x) (V : Set _)}) :
    ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ V < d →
      c * (∑ i, codeWeight μ code i * S.indicator (fun _ => (1 : ℝ)) (rep i)) ≤
        ∑ i, if ρ - ε ≤ Metric.infDist (e (rep i)) (V : Set _) then
          codeWeight μ code i * S.indicator (fun _ => (1 : ℝ)) (rep i) else 0 := by
  classical
  intro V hV
  rw [sum_codeWeight_indicator μ code hcode rep S hS]
  refine (hbroad V hV).trans ?_
  have hsubset : {x | x ∈ S ∧ ρ ≤ Metric.infDist (e x) (V : Set _)} ⊆
      {x | rep (code x) ∈ S ∧ ρ - ε ≤ Metric.infDist (e (rep (code x))) (V : Set _)} := by
    intro x hx
    exact ⟨(hS x).mpr hx.1, infDist_representative_lower e code rep ε herr V x ρ hx.2⟩
  refine (measureReal_mono hsubset).trans_eq ?_
  rw [← sum_codeWeight_predicate μ code hcode
    (fun i => rep i ∈ S ∧ ρ - ε ≤ Metric.infDist (e (rep i)) (V : Set _))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Set.indicator_apply]
  split_ifs <;> simp_all

/-- A finite capture converts an arbitrary finite line law into the same
physical-cell support constraint as the finite-family theorem. -/
theorem captured_line_law_support_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (z : Fin m → Fin 4 → ℤ), Function.Injective z →
      ∀ (μ : Measure Ω) [IsFiniteMeasure μ]
        (a e : Ω → EuclideanSpace ℝ (Fin 4)), (∀ x, ‖e x‖ = 1) →
      ∀ (n : ℕ) (code : Ω → Fin n), Measurable code → ∀ rep : Fin n → Ω,
      ∀ ρ ε c : ℝ, 0 ≤ ρ - ε → 0 ≤ c →
      (∀ x, dist (e x) (e (rep (code x))) ≤ ε) →
      (∀ q x, latticePoint (z q) ∈ lineTube 3 (a (rep (code x))) (e (rep (code x))) ↔
        latticePoint (z q) ∈ lineTube 3 (a x) (e x)) →
      (∀ q : Fin m, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)), Module.finrank ℝ V < 4 →
        c * μ.real {x | latticePoint (z q) ∈ lineTube 3 (a x) (e x)} ≤
          μ.real {x | latticePoint (z q) ∈ lineTube 3 (a x) (e x) ∧
            ρ ≤ Metric.infDist (e x) (V : Set _)}) →
      (c * (ρ - ε)) ^ 4 *
        (∑ q : Fin m, μ.real {x | latticePoint (z q) ∈ lineTube 3 (a x) (e x)}) ^ 4 ≤
          (m : ℝ) * C ^ 3 * (μ.real univ) ^ 4 := by
  classical
  obtain ⟨C, hC, hfinite⟩ := broad_line_family_support_budget
  refine ⟨C, hC, ?_⟩
  intro m z hz μ hμ a e he n code hcode rep ρ ε c hρε hc herr hmem hbroad
  let S : Fin m → Set Ω := fun q => {x | latticePoint (z q) ∈ lineTube 3 (a x) (e x)}
  have hS (q : Fin m) : ∀ x, rep (code x) ∈ S q ↔ x ∈ S q := hmem q
  have hlocal (q : Fin m) :
      (∑ i, localLineWeight (fun i => a (rep i)) (fun i => e (rep i))
        (codeWeight μ code) (latticePoint (z q)) i) = μ.real (S q) := by
    convert sum_codeWeight_indicator μ code hcode rep (S q) (hS q) using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [localLineWeight, Set.indicator_apply, S, Set.mem_ofPred_eq]
  have hb (q : Fin m) := capture_breadth μ code hcode rep e (S q) (hS q)
    ρ ε c herr (hbroad q)
  have hb' (q : Fin m) : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)),
      Module.finrank ℝ V < 4 →
      c * (∑ i, localLineWeight (fun i => a (rep i)) (fun i => e (rep i))
        (codeWeight μ code) (latticePoint (z q)) i) ≤
      ∑ i, if ρ - ε ≤ Metric.infDist (e (rep i)) (V : Set _) then
        localLineWeight (fun i => a (rep i)) (fun i => e (rep i))
          (codeWeight μ code) (latticePoint (z q)) i else 0 := by
    simpa only [localLineWeight, S, Set.indicator_apply, Set.mem_ofPred_eq] using hb q
  have h := hfinite m z hz n (fun i => a (rep i)) (fun i => e (rep i)) (codeWeight μ code)
    (fun i => he (rep i)) (fun i => measureReal_nonneg) (ρ - ε) c hρε hc hb'
  simpa only [hlocal, sum_codeWeight μ code hcode] using h

/-- Capture finitely many exact events and approximate a bounded direction
map, using actual representatives from the original parameter space. -/
theorem exists_bounded_vector_event_capture {d : ℕ} (e : Ω → EuclideanSpace ℝ (Fin d))
    (he : Measurable e) (K : ℝ) (hbound : ∀ x, ‖e x‖ ≤ K)
    (m : ℕ) (S : Fin m → Set Ω) (hS : ∀ j, MeasurableSet (S j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ code : Ω → Fin n, ∃ rep : Fin n → Ω,
      Measurable code ∧ (∀ i, code (rep i) = i) ∧
      (∀ x, dist (e x) (e (rep (code x))) ≤ ε) ∧
      ∀ j x, rep (code x) ∈ S j ↔ x ∈ S j := by
  classical
  let flags : Ω → Fin m → Bool := fun x j => decide (x ∈ S j)
  have hflags : Measurable flags := by
    apply Measurable.of_eval
    intro j
    apply measurable_to_bool
    convert hS j using 1
    ext x
    simp [flags]
  let flagCode : SimpleFunc Ω (Fin m → Bool) :=
    ⟨flags, fun z => hflags (measurableSet_singleton z), Set.toFinite _⟩
  have he' : Measurable (fun x j => e x j) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).measurable.comp he
  have hcoord : ∀ x j, |e x j| ≤ K := by
    intro x j
    have h := PiLp.norm_apply_le (e x) j
    simp only [Real.norm_eq_abs] at h
    exact h.trans (hbound x)
  let dirCode := Submission.Lib.K4ContinuousPlanks.boundedFloorCode
    (fun x j => e x j) he' K hcoord (ε / ((d : ℝ) + 1)) (by positivity)
  obtain ⟨n, code, rep, hcode, hrep, hsame⟩ :=
    Submission.Lib.K4ContinuousPlanks.finite_code_representatives (dirCode.pair flagCode)
  refine ⟨n, code, rep, hcode, hrep, ?_, ?_⟩
  · intro x
    have hdir (j : Fin d) : ⌊e (rep (code x)) j / (ε / ((d : ℝ) + 1))⌋ = ⌊e x j / (ε / ((d : ℝ) + 1))⌋ := by
      exact congrFun (congrArg Prod.fst (hsame x)) j
    have hdiff (j : Fin d) : |e x j - e (rep (code x)) j| ≤ ε / ((d : ℝ) + 1) := by
      have h := Int.abs_sub_lt_one_of_floor_eq_floor (hdir j).symm
      rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < ε / ((d : ℝ) + 1))] at h
      exact ((div_lt_one (by positivity : 0 < ε / ((d : ℝ) + 1))).mp h).le
    have hnorm := Submission.Obl.k4_adapted_oscillation_tests.norm_apply_le_sum_abs
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) (fun i => by simp)
      (e x - e (rep (code x)))
    change ‖e x - e (rep (code x))‖ ≤ _ at hnorm
    rw [dist_eq_norm]
    refine hnorm.trans ?_
    calc
      ∑ j : Fin d, |(e x - e (rep (code x))) j| ≤ ∑ _j : Fin d, ε / ((d : ℝ) + 1) :=
        Finset.sum_le_sum (fun j _ => hdiff j)
      _ = (d : ℝ) * (ε / ((d : ℝ) + 1)) := by simp
      _ ≤ ε := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (d : ℝ) + 1)]
        nlinarith
  · intro j x
    have hh : decide (rep (code x) ∈ S j) = decide (x ∈ S j) :=
      congrFun (congrArg Prod.snd (hsame x)) j
    simpa only [decide_eq_decide] using hh

/-- Unit directions are a special case of bounded-vector capture. -/
theorem exists_direction_event_capture {d : ℕ} (e : Ω → EuclideanSpace ℝ (Fin d))
    (he : Measurable e) (hunit : ∀ x, ‖e x‖ = 1)
    (m : ℕ) (S : Fin m → Set Ω) (hS : ∀ j, MeasurableSet (S j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ code : Ω → Fin n, ∃ rep : Fin n → Ω,
      Measurable code ∧ (∀ i, code (rep i) = i) ∧
      (∀ x, dist (e x) (e (rep (code x))) ≤ ε) ∧
      ∀ j x, rep (code x) ∈ S j ↔ x ∈ S j :=
  exists_bounded_vector_event_capture e he 1 (fun x => (hunit x).le) m S hS ε hε

/-- The broad-cell support obstruction for an arbitrary finite line measure.
There is no finiteness or cardinality hypothesis on its line parameter space. -/
theorem line_law_support_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (z : Fin m → Fin 4 → ℤ), Function.Injective z →
      ∀ (μ : Measure Ω) [IsFiniteMeasure μ]
        (a e : Ω → EuclideanSpace ℝ (Fin 4)), Measurable e → (∀ x, ‖e x‖ = 1) →
      (∀ q : Fin m, MeasurableSet {x | latticePoint (z q) ∈ lineTube 3 (a x) (e x)}) →
      ∀ ρ c : ℝ, 0 < ρ → 0 ≤ c →
      (∀ q : Fin m, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)), Module.finrank ℝ V < 4 →
        c * μ.real {x | latticePoint (z q) ∈ lineTube 3 (a x) (e x)} ≤
          μ.real {x | latticePoint (z q) ∈ lineTube 3 (a x) (e x) ∧
            ρ ≤ Metric.infDist (e x) (V : Set _)}) →
      (c * ρ / 2) ^ 4 *
        (∑ q : Fin m, μ.real {x | latticePoint (z q) ∈ lineTube 3 (a x) (e x)}) ^ 4 ≤
          (m : ℝ) * C ^ 3 * (μ.real univ) ^ 4 := by
  obtain ⟨C, hC, hbudget⟩ := captured_line_law_support_budget (Ω := Ω)
  refine ⟨C, hC, ?_⟩
  intro m z hz μ hμ a e he hunit hsets ρ c hρ hc hbroad
  obtain ⟨n, code, rep, hcode, hrep, herr, hmem⟩ := exists_direction_event_capture e he hunit m
    (fun q => {x | latticePoint (z q) ∈ lineTube 3 (a x) (e x)}) hsets (ρ / 2) (by positivity)
  have h := hbudget m z hz μ a e hunit n code hcode rep ρ (ρ / 2) c
    (by linarith) hc herr hmem hbroad
  simpa only [show c * (ρ - ρ / 2) = c * ρ / 2 by ring] using h

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad.Filling
