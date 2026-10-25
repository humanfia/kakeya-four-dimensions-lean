/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/PathBudgets.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

/-! Genuine full-assignment normalization budgets of scalar refinements.
Their lower bounds follow from retained original incidence mass; their upper
bounds follow from disjoint full assignments in each world and time block. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {p q : Code} {r b h : ℝ}

theorem originalSelected_univ (w : RefinementWitness p q r b h) (k : ℕ) :
    originalSelected w k univ =
      ∑ i, ENNReal.ofReal (ω p (w.sample k) (w.world k i)) *
        mu p (w.sample k) (w.world k i) (w.selected k i) := by
  simp only [originalSelected, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.map_apply
    (show Measurable (fun z : State => (w.world k i, z)) from
      measurable_const.prodMk measurable_id) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

theorem originalSelected_mass_lower (w : RefinementWitness p q r b h) (k : ℕ) :
    ENNReal.ofReal (N p (w.sample k) ^ (-w.loss k)) ≤ originalSelected w k univ := by
  classical
  have hmass := (w.charts k).2.2.2.2.2.2.2.2.2.2
  apply hmass.trans
  rw [originalSelected_univ]
  calc
    _ ≤ ∑ g, ENNReal.ofReal (ω p (w.sample k) g) *
        (∑ i ∈ Finset.univ.filter (fun i => w.world k i = g),
          mu p (w.sample k) g (w.selected k i)) := by
      apply Finset.sum_le_sum
      intro g _
      apply mul_le_mul' le_rfl
      have heq : {z : State | ∃ i, w.world k i = g ∧ z ∈ w.selected k i} =
          ⋃ i ∈ Finset.univ.filter (fun i => w.world k i = g), w.selected k i := by
        ext z
        simp
      rw [heq]
      exact measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [Finset.mul_sum]
      symm
      calc
        _ = ∑ g, ∑ i ∈ Finset.univ.filter (fun i => w.world k i = g),
            ENNReal.ofReal (ω p (w.sample k) (w.world k i)) *
              mu p (w.sample k) (w.world k i) (w.selected k i) :=
          (Finset.sum_fiberwise Finset.univ (w.world k) _).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro g _
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]

theorem selected_le_prior_budget (w : RefinementWitness p q r b h) (k : ℕ)
    (i : Fin (W q k)) :
    mu p (w.sample k) (w.world k i) (w.selected k i) ≤
      ENNReal.ofReal (w.toRefinementData.duration k) *
        ν p (w.sample k) (w.world k i) (w.assignment k i) := by
  have hsub : w.selected k i ⊆ w.assignment k i ×ˢ I (w.T k) (w.block k i) :=
    fun _ hz => ((w.charts k).2.2.2.2.2.1 i hz).2
  have hvolume : volume (I (w.T k) (w.block k i)) =
      ENNReal.ofReal (w.toRefinementData.duration k) := by
    change volume (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block
      (w.T k) (w.block k i)) = _
    rw [Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block_eq, Real.volume_Icc]
    simp only [add_sub_cancel_left, one_div]
    rfl
  calc
    _ ≤ ((ν p (w.sample k) (w.world k i)).prod volume) (w.selected k i) :=
      Measure.restrict_apply_le _ _
    _ ≤ ((ν p (w.sample k) (w.world k i)).prod volume)
        (w.assignment k i ×ˢ I (w.T k) (w.block k i)) := measure_mono hsub
    _ = _ := by rw [Measure.prod_prod, hvolume, mul_comm]

theorem ofReal_normalizer (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    ENNReal.ofReal (normalizer w k) =
      ∑ i, ENNReal.ofReal (ω p (w.sample k) (w.world k i)) *
        ENNReal.ofReal (w.toRefinementData.duration k) *
          ν p (w.sample k) (w.world k i) (w.assignment k i) := by
  have hw (i : Fin (W q k)) : 0 ≤ ω p (w.sample k) (w.world k i) :=
    (hp.2.1 (w.sample k)).2.1 _
  rw [normalizer, ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (mul_nonneg (hw i) (w.duration_pos k).le) ENNReal.toReal_nonneg)]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul (mul_nonneg (hw i) (w.duration_pos k).le),
    ENNReal.ofReal_mul (hw i), ENNReal.ofReal_toReal (w.assignment_mass_ne_top hp k i)]

theorem originalSelected_le_normalizer (w : RefinementWitness p q r b h)
    (hp : Exact p) (k : ℕ) :
    originalSelected w k univ ≤ ENNReal.ofReal (normalizer w k) := by
  rw [originalSelected_univ, ofReal_normalizer w hp k]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_assoc] using
    mul_le_mul' (a := ENNReal.ofReal (ω p (w.sample k) (w.world k i)))
      le_rfl (selected_le_prior_budget w k i)

/-- No success posterior enters this budget: the original full assigned
trajectory masses pay for the retained selected incidence mass. -/
theorem normalizer_lower (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    N p (w.sample k) ^ (-w.loss k) ≤ normalizer w k := by
  have hle := (originalSelected_mass_lower w k).trans (originalSelected_le_normalizer w hp k)
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (by linarith [hp.1.1 (w.sample k)]) _),
    ENNReal.toReal_ofReal (normalizer_pos w k).le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hle

theorem normalizer_le_one (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    normalizer w k ≤ 1 := by
  have hbudget := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget_ofReal
    (ν p (w.sample k)) (ω p (w.sample k)) (w.world k) (w.block k) (w.assignment k)
    (fun g => ((hp.2.1 (w.sample k)).2.2.2.1 g).1)
    (hp.2.1 (w.sample k)).2.1 (hp.2.1 (w.sample k)).2.2.1
    (fun i => ((w.charts k).2.2.2.1 i).1) (w.charts k).2.2.2.2.1
  have hcard : (Fintype.card (Fin (2 ^ w.T k)) : ℝ≥0∞) =
      ENNReal.ofReal ((2 : ℝ) ^ w.T k) := by simp
  have hle : ENNReal.ofReal (normalizer w k) ≤ 1 := by
    calc
      _ = ENNReal.ofReal (w.toRefinementData.duration k) *
          ∑ i, ENNReal.ofReal (ω p (w.sample k) (w.world k i)) *
            ν p (w.sample k) (w.world k i) (w.assignment k i) := by
        rw [ofReal_normalizer w hp k, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ac_rfl
      _ ≤ ENNReal.ofReal (w.toRefinementData.duration k) *
          (Fintype.card (Fin (2 ^ w.T k)) : ℝ≥0∞) := mul_le_mul' le_rfl hbudget
      _ = 1 := by
        rw [hcard, ← ENNReal.ofReal_mul (w.duration_pos k).le]
        simp [RefinementData.duration]
  simpa only [ENNReal.toReal_ofReal (normalizer_pos w k).le, ENNReal.toReal_one] using
    ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hle

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
