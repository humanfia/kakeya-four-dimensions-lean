-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/CartesianAnchorSeparation.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/CartesianAnchorSeparation.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/CartesianAnchorSeparation.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.UniformAnchors
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.GridMass

/-!
Actual separated anchors on a finite real grid. The original root-session
sampling kernel is connected to the weighted Cartesian expectations used
by the original-mass target selection.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian.Cartesian

open MeasureTheory Set ProbabilityTheory

noncomputable section

def threeAxes (A : Type*) : (Fin 3 → A) ≃ A × A × A where
  toFun f := (f 0, f 1, f 2)
  invFun a := ![a.1, a.2.1, a.2.2]
  left_inv := by intro f; funext i; fin_cases i <;> rfl
  right_inv := by intro a; rfl

open Classical in
/-- A finite product law's event mass is its exact weighted Cartesian count. -/
theorem pi_three_axis_event_mean {X : Type*} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (k : ℕ)
    (P : (Fin k → X) × (Fin k → X) × (Fin k → X) → Prop) :
    (Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : Fin k => μ))).real
        {a | P (a 0, a 1, a 2)} =
      mean (jointWeight (tupleWeight (fun x => μ.real {x}))
        (jointWeight (tupleWeight (fun x => μ.real {x})) (tupleWeight (fun x => μ.real {x}))))
        (fun a => if P a then (1 : ℝ) else 0) := by
  classical
  let ν := Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : Fin k => μ))
  let F := Finset.univ.filter fun a : Fin 3 → Fin k → X => P (a 0, a 1, a 2)
  have hsum := original_code_table_mass ν id measurable_id F
  have hset : {a | id a ∈ F} = {a | P (a 0, a 1, a 2)} := by ext a; simp [F]
  rw [hset] at hsum
  rw [← hsum]
  simp only [F, Finset.sum_filter]
  have hweight (a : Fin 3 → Fin k → X) :
      ν.real {x | id x = a} =
        tupleWeight (fun x => μ.real {x}) (a 0) *
          (tupleWeight (fun x => μ.real {x}) (a 1) *
            tupleWeight (fun x => μ.real {x}) (a 2)) := by
    have hsing : {x | id x = a} = {a} := rfl
    rw [hsing]
    simp only [ν, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod, ENNReal.toReal_mul,
      Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, tupleWeight]
  simp_rw [hweight]
  unfold mean
  apply Fintype.sum_equiv (threeAxes (Fin k → X))
  intro a
  change (if P (a 0, a 1, a 2) then
      tupleWeight (fun x => μ.real {x}) (a 0) *
        (tupleWeight (fun x => μ.real {x}) (a 1) * tupleWeight (fun x => μ.real {x}) (a 2))
      else 0) =
    (tupleWeight (fun x => μ.real {x}) (a 0) *
      (tupleWeight (fun x => μ.real {x}) (a 1) * tupleWeight (fun x => μ.real {x}) (a 2))) *
        (if P (a 0, a 1, a 2) then 1 else 0)
  split_ifs <;> simp

def anchorsSeparated {X : Type*} (value : X → ℝ) (r : ℝ) {k : ℕ}
    (a : (Fin k → X) × (Fin k → X) × (Fin k → X)) : Prop :=
  ∀ axis : Fin 3, ∀ i j : Fin k, i ≠ j →
    r ≤ |value ((threeAxes (Fin k → X)).symm a axis i) -
      value ((threeAxes (Fin k → X)).symm a axis j)|

open Classical in
/-- A separated real grid supplies the exact bad-anchor expectation,
including its atom-size term. There is no abstract collision certificate. -/
theorem uniform_grid_bad_anchor_expectation (S : Finset ℝ) [Nonempty S]
    (k : ℕ) (ξ r : ℝ) (hξ : 0 < ξ) (hr : 0 ≤ r)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ξ ≤ dist x y) :
    mean (jointWeight (tupleWeight (k := k) (uniformWeight S))
      (jointWeight (tupleWeight (k := k) (uniformWeight S)) (tupleWeight (k := k) (uniformWeight S))))
      (fun a => if anchorsSeparated (fun x : S => (x : ℝ)) r a then (0 : ℝ) else 1) ≤
      3 * (k : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ)) := by
  classical
  let μ := (PMF.uniformOfFintype S).toMeasure
  have hsingle (x : S) : μ.real {x} = uniformWeight S x := by
    simp only [μ, measureReal_def, PMF.toMeasure_apply_singleton (PMF.uniformOfFintype S) x (measurableSet_singleton x),
      PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, uniformWeight, one_div]
  have heq := pi_three_axis_event_mean μ k
    (fun a => ¬ anchorsSeparated (fun x : S => (x : ℝ)) r a)
  have hbadset : {a : Fin 3 → Fin k → S |
      ¬ anchorsSeparated (fun x : S => (x : ℝ)) r (a 0, a 1, a 2)} =
      {a | ∃ axis i j, i ≠ j ∧ |(a axis i : ℝ) - (a axis j : ℝ)| < r} := by
    ext a
    have ha : (threeAxes (Fin k → S)).symm (a 0, a 1, a 2) = a :=
      (threeAxes (Fin k → S)).symm_apply_apply a
    simp only [anchorsSeparated, ha, not_forall, not_le, exists_prop, mem_ofPred_eq]
  rw [hbadset] at heq
  simp_rw [hsingle] at heq
  have hbound := uniform_finset_cartesian_close_pairs_measure_le
    (ι := Fin 3) (κ := Fin k) S ξ r hξ hr hsep
  have hrange : (Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : Fin k => μ))).real
      {a | ∃ axis i j, i ≠ j ∧ |(a axis i : ℝ) - (a axis j : ℝ)| < r} ≤
        3 * (k : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ)) := by
    have ht := ENNReal.toReal_mono (by finiteness) hbound
    simpa only [measureReal_def, Fintype.card_fin, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_ofNat,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * r / ξ + 1) / (S.card : ℝ)), μ] using ht
  rw [heq] at hrange
  convert hrange using 1
  apply congrArg (mean _)
  funext a
  by_cases ha : anchorsSeparated (fun x : S => (x : ℝ)) r a <;> simp [ha]

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian.Cartesian
