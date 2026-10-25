-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalVerticalCounts, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalVerticalCounts.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalVerticalCounts.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalVerticalCounts.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.AffinePhysicalSupport
import Submission.Lib.K4FinitePlankAtlases.DensityFloors


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Positive original joint-cell floors and the unchanged original
base ceiling count ALL scalar cells of the selected labelled family.
The finite support is constructed rather than assumed. -/
theorem original_vertical_count_from_floors {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (reference : Measure X) [IsFiniteMeasure reference]
    (base : X → Q) (hbase : Measurable base) (scalar : X → ℤ) (hscalar : Measurable scalar)
    (E : Set X) (floor cap : ℝ) (hfloor : 0 < floor) (hcap : 0 ≤ cap)
    (hFloor : ∀ z∈E, ENNReal.ofReal floor ≤
      reference {y | base y=base z ∧ scalar y=scalar z})
    (hCap : ∀ q, reference {y | base y=q} ≤ ENNReal.ofReal cap) (q : Q) :
    {j | ∃ z∈E, base z=q ∧ scalar z=j}.Finite ∧
      ({j | ∃ z∈E, base z=q ∧ scalar z=j}.ncard : ℝ) ≤ cap/floor := by
  classical
  let S : Set ℤ := {j | ∃ z∈E, base z=q ∧ scalar z=j}
  let μq := reference.restrict {y | base y=q}
  haveI : IsFiniteMeasure μq := by dsimp [μq]; infer_instance
  let cells := fun j : ℤ => {y | base y=q ∧ scalar y=j}
  have hMeas (j) : MeasurableSet (cells j) :=
    (hbase (measurableSet_singleton q)).inter
      (measurableSet_eq_fun hscalar measurable_const)
  have hSame (j) : μq (cells j)=reference (cells j) :=
    Measure.restrict_eq_self reference (fun _ hz => hz.1)
  have hTotal : μq.real univ ≤ cap := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hCap q)
    simpa only [measureReal_def,μq,Measure.restrict_apply_univ,ENNReal.toReal_ofReal hcap] using hh
  have hCount (F : Finset ℤ) (hF : (↑F : Set ℤ) ⊆ S) : (F.card : ℝ) ≤ cap/floor := by
    have hDisj : (↑F : Set ℤ).PairwiseDisjoint cells := by
      intro j hj j' hj' hne
      apply disjoint_left.mpr
      intro z hz hz'
      exact hne (hz.2.symm.trans hz'.2)
    have hMass (j) (hj : j∈F) : floor ≤ μq.real (cells j) := by
      obtain ⟨z,hz,hb,hs⟩ := hF hj
      have hh := hFloor z hz
      rw [hb,hs] at hh
      have hr := ENNReal.toReal_mono (measure_ne_top _ _) hh
      simpa only [measureReal_def,hSame j,ENNReal.toReal_ofReal hfloor.le] using hr
    have hh := Submission.Lib.K4FinitePlankAtlases.old_cell_count μq F cells hDisj
      (fun j _ => hMeas j) hfloor hMass
    exact hh.trans (div_le_div_of_nonneg_right hTotal hfloor.le)
  have hFinite := Submission.Obl.k4_scalar_initial_true_horizon.finite_of_uniform_finset_card_bound
    S (cap/floor) hCount
  refine ⟨hFinite,?_⟩
  rw [Set.ncard_eq_toFinset_card _ hFinite]
  exact hCount _ (by simp)

theorem original_fine_state_eq_iff_base_scalar {Λ : Type*}
    (c : Λ → Fin 7 → ℝ) (p : ℝ) (z z' : Λ × ℝ) :
    originalFineState c p z=originalFineState c p z' ↔
      originalBaseCode c p z=originalBaseCode c p z' ∧
        ⌊zx (c z.1) z.2/p⌋=⌊zx (c z'.1) z'.2/p⌋ := by
  constructor
  · intro h
    refine ⟨?_,congrFun h 1⟩
    funext j
    fin_cases j
    · exact congrFun h 0
    · exact congrFun h 2
    · exact congrFun h 3
  · rintro ⟨hb,hx⟩
    funext j
    fin_cases j
    · exact congrFun hb 0
    · exact hx
    · exact congrFun hb 1
    · exact congrFun hb 2

/-- Genuine old physical-cell floors and old base caps imply the
vertical p^(-d) support count used by coefficient cleanup. All measures
are the unchanged reference law, even after arbitrary label deletion. -/
theorem original_vertical_physical_count {Λ : Type*} [MeasurableSpace Λ]
    (reference : Measure (Λ × ℝ)) [IsFiniteMeasure reference]
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c) (E : Set (Λ × ℝ))
    (p Kfloor Kbase d : ℝ) (hp : 0 < p) (hKfloor : 0 < Kfloor) (hKbase : 0 ≤ Kbase)
    (hFloor : ∀ z∈E, ENNReal.ofReal (p^(3+d)/Kfloor) ≤
      reference ((originalFineState c p) ⁻¹' {originalFineState c p z}))
    (hCap : ∀ q, reference {z | originalBaseCode c p z=q} ≤ ENNReal.ofReal (Kbase*p^3)) :
    ∀ q, (originalScalarFiber E c p q).Finite ∧
      ((originalScalarFiber E c p q).ncard : ℝ) ≤ (Kbase*Kfloor)*p^(-d) := by
  have hb : Measurable (originalBaseCode c p) := by
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j
    · change Measurable (fun z : Λ × ℝ => (⌊z.2/p⌋ : ℤ))
      fun_prop
    · change Measurable (fun z : Λ × ℝ => (⌊(c z.1 3+c z.1 4*z.2)/p⌋ : ℤ))
      fun_prop
    · change Measurable (fun z : Λ × ℝ => (⌊(c z.1 5+c z.1 6*z.2)/p⌋ : ℤ))
      fun_prop
  have hs : Measurable (fun z : Λ × ℝ => (⌊zx (c z.1) z.2/p⌋ : ℤ)) := by
    unfold zx
    fun_prop
  have hFloor' (z : Λ × ℝ) (hz : z∈E) : ENNReal.ofReal (p^(3+d)/Kfloor) ≤
      reference {y | originalBaseCode c p y=originalBaseCode c p z ∧
        ⌊zx (c y.1) y.2/p⌋=⌊zx (c z.1) z.2/p⌋} := by
    have heq : (originalFineState c p) ⁻¹' {originalFineState c p z} =
        {y | originalBaseCode c p y=originalBaseCode c p z ∧
          ⌊zx (c y.1) y.2/p⌋=⌊zx (c z.1) z.2/p⌋} := by
      ext y
      exact original_fine_state_eq_iff_base_scalar c p y z
    rw [←heq]
    exact hFloor z hz
  intro q
  have hh := original_vertical_count_from_floors reference (originalBaseCode c p) hb
    (fun z => ⌊zx (c z.1) z.2/p⌋) hs E (p^(3+d)/Kfloor) (Kbase*p^3)
    (by positivity) (by positivity) hFloor' hCap q
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  rw [Real.rpow_add hp]
  norm_num only [Real.rpow_ofNat] 
  rw [Real.rpow_neg hp.le]
  field_simp [(Real.rpow_pos_of_pos hp d).ne',hp.ne',hKfloor.ne']

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
