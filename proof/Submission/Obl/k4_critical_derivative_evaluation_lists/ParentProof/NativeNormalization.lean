/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, NativeNormalization.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.OriginalMass
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.ContinuousNormalization
import Submission.Obl.k4_scalar_initial_true_horizon.Basic

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set
open scoped ENNReal

def physicalTimeMap {α : Type*} (t₀ H : ℝ) (p : α × ℝ) : α × ℝ :=
  (p.1, t₀ + H * p.2)

theorem measurable_physicalTimeMap {α : Type*} [MeasurableSpace α] (t₀ H : ℝ) :
    Measurable (physicalTimeMap (α := α) t₀ H) :=
  measurable_fst.prodMk ((measurable_snd.const_mul H).const_add t₀)

theorem physicalTimeMap_unitTimeMap {α : Type*} (t₀ H : ℝ) (hH : H ≠ 0) (p : α × ℝ) :
    physicalTimeMap t₀ H (unitTimeMap t₀ H p) = p := by
  apply Prod.ext
  · rfl
  · dsimp [physicalTimeMap, unitTimeMap]
    field_simp
    ring

theorem normalized_ae_of_original
    {α : Type*} [MeasurableSpace α] (σ : Measure (α × ℝ)) (t₀ H W : ℝ)
    (P : α × ℝ → Prop) (hP : MeasurableSet {p | P p})
    (h : ∀ᵐ p ∂σ, P (unitTimeMap t₀ H p)) :
    ∀ᵐ p ∂(ENNReal.ofReal W⁻¹ • σ.map (unitTimeMap t₀ H)), P p := by
  exact Measure.ae_smul_measure
    ((ae_map_iff (measurable_unitTimeMap t₀ H).aemeasurable hP).mpr h) _

/-- A mass floor in original reference units becomes the same relative
floor on the actual normalized continuous law. -/
theorem original_normalized_mass_lower
    {α : Type*} [MeasurableSpace α] (σ : Measure (α × ℝ))
    (t₀ H W θ : ℝ) (hW : 0 < W) (hmass : ENNReal.ofReal (W * θ) ≤ σ univ) :
    ENNReal.ofReal θ ≤
      (ENNReal.ofReal W⁻¹ • σ.map (unitTimeMap t₀ H)) univ := by
  rw [original_continuous_normalized_apply σ t₀ H W univ MeasurableSet.univ, preimage_univ]
  have heq : ENNReal.ofReal W⁻¹ * ENNReal.ofReal (W * θ) = ENNReal.ofReal θ := by
    rw [ENNReal.ofReal_mul hW.le, ENNReal.ofReal_inv_of_pos hW, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simpa using hW) ENNReal.ofReal_ne_top, one_mul]
  rw [← heq]
  exact mul_le_mul_of_nonneg_left hmass zero_le

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

def leftTime (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : ℝ :=
  ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s

def horizontalOrigin (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : ℝ :=
  cfg.c k s i 0 + cfg.leftTime k s i * cfg.c k s i 1

def truePrior (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : Measure α :=
  (cfg.ν k (cfg.A k s i))⁻¹ • (cfg.ν k).restrict (cfg.A k s i)

theorem leftTime_mem (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    cfg.leftTime k s i ∈ I (cfg.T k s) (cfg.j k s i) := by
  refine ⟨le_rfl, ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

theorem true_block_eq (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    I (cfg.T k s) (cfg.j k s i) =
      Icc (cfg.leftTime k s i) (cfg.leftTime k s i + cfg.timeLength k s) := by
  unfold I leftTime timeLength
  congr 1
  ring

theorem leftTime_abs_le_one (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    |cfg.leftTime k s i| ≤ 1 := by
  have ht := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) (cfg.leftTime_mem k s i)
  simpa only [abs_of_nonneg ht.1] using ht.2

theorem AssignmentLevel.horizontalOrigin_bound (_h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    |cfg.horizontalOrigin k s i| ≤ 2 * cfg.K k := by
  unfold horizontalOrigin
  calc
    _ ≤ |cfg.c k s i 0| + |cfg.leftTime k s i * cfg.c k s i 1| := abs_add_le _ _
    _ ≤ cfg.K k + cfg.K k := by
      apply add_le_add (a.coefficient_bound i 0)
      rw [abs_mul]
      exact (mul_le_mul (cfg.leftTime_abs_le_one k s i) (a.coefficient_bound i 1)
        (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = _ := by ring

theorem AssignmentLevel.prior_probability (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    IsProbabilityMeasure (cfg.truePrior k s i) := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hH : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hν : cfg.ν k (cfg.A k s i) ≠ 0 := by
    intro hz
    have hh := (a.critical_prior_bounds h i).1
    simp only [measureReal_def, hz, ENNReal.toReal_zero] at hh
    have hp : 0 < cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2 := by positivity
    linarith
  refine ⟨?_⟩
  simp only [truePrior, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hν (measure_ne_top _ _)

/-- Restriction to the fitted subset is dominated by the product law of the
ORIGINAL full assignment, before either measure is normalized. -/
theorem AssignmentLevel.restricted_original_domination (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s))
    (σ : Measure (α × ℝ))
    (hσ : σ ≤ (cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))) :
    σ ≤ ENNReal.ofReal (cfg.K k) • (((cfg.ν k).restrict (cfg.A k s i)).prod volume) := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hsub : cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i) ⊆ cfg.A k s i ×ˢ univ :=
    Set.prod_mono (a.fitted_subset i) (subset_univ _)
  have hρμ := (h.basic k).2.2.2.2.1
  have hμdom := (h.basic k).2.2.2.1
  have hh := hσ.trans (Measure.restrict_mono hsub (hρμ.trans hμdom))
  rw [Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ] at hh
  exact hh

/-- The actual normalized incidence law has the normalized SAME full prior
and costs only the original density factor K. -/
theorem AssignmentLevel.normalized_original_domination (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s))
    (σ : Measure (α × ℝ))
    (hσ : σ ≤ (cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))) :
    (ENNReal.ofReal (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i))⁻¹ •
      σ.map (unitTimeMap (cfg.leftTime k s i) (cfg.timeLength k s))) ≤
      ENNReal.ofReal (cfg.K k) • ((cfg.truePrior k s i).prod volume) := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hH : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hνreal : 0 < (cfg.ν k).real (cfg.A k s i) :=
    (by positivity : 0 < cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2).trans_le
      (a.critical_prior_bounds h i).1
  have hW : 0 < cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i) := mul_pos hH hνreal
  have hν : ((cfg.ν k).restrict (cfg.A k s i)) univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    exact ne_of_gt (ENNReal.toReal_pos_iff.mp hνreal).1
  have hh := original_continuous_normalized_domination
    ((cfg.ν k).restrict (cfg.A k s i)) σ (cfg.leftTime k s i) (cfg.timeLength k s)
    (cfg.K k) (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i)) hH hK.le hW hν
    (a.restricted_original_domination h i σ hσ)
  have heq : cfg.K k * cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i) /
      (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i)) = cfg.K k := by
    field_simp
  simpa only [measureReal_restrict_apply_univ, Measure.restrict_apply_univ, heq, truePrior] using hh

/-- Clipping affects only arms outside the original assignment or outside
its conull native velocity bound. -/
def goodArms (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : Set α :=
  cfg.A k s i ∩ {l | |cfg.b k l 3| ≤ cfg.K k}

def clippedIntercept (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : α → ℝ := by
  classical
  exact (cfg.goodArms k s i).indicator (fun l =>
    (cfg.b k l 0 + cfg.leftTime k s i * cfg.b k l 3 - cfg.horizontalOrigin k s i) / cfg.timeLength k s)

def clippedVelocity (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : α → ℝ := by
  classical
  exact (cfg.goodArms k s i).indicator (fun l => cfg.b k l 3)

theorem AssignmentLevel.measurableSet_goodArms (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    MeasurableSet (cfg.goodArms k s i) :=
  (a.measurable i).inter (measurableSet_le (((measurable_pi_apply 3).comp (h.basic k).1).abs) measurable_const)

theorem AssignmentLevel.clipped_measurable (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    Measurable (cfg.clippedIntercept k s i) ∧ Measurable (cfg.clippedVelocity k s i) := by
  classical
  have hb := (h.basic k).1
  constructor
  · unfold clippedIntercept
    apply Measurable.indicator _ (a.measurableSet_goodArms h i)
    fun_prop
  · unfold clippedVelocity
    exact ((measurable_pi_apply 3).comp hb).indicator (a.measurableSet_goodArms h i)

theorem clipped_coordinates_of_mem (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (l : α) (hl : l ∈ cfg.goodArms k s i) :
    cfg.clippedIntercept k s i l =
      (cfg.b k l 0 + cfg.leftTime k s i * cfg.b k l 3 - cfg.horizontalOrigin k s i) / cfg.timeLength k s ∧
    cfg.clippedVelocity k s i l = cfg.b k l 3 := by
  classical
  exact ⟨Set.indicator_of_mem hl _, Set.indicator_of_mem hl _⟩

theorem AssignmentLevel.clipped_bound (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (l : α) :
    |cfg.clippedIntercept k s i l| + |cfg.clippedVelocity k s i l| ≤ 2 * cfg.K k := by
  classical
  have hK : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
  by_cases hl : l ∈ cfg.goodArms k s i
  · have hc := cfg.clipped_coordinates_of_mem k s i l hl
    rw [hc.1, hc.2]
    have hH : 0 < cfg.timeLength k s := by unfold timeLength; positivity
    have hgeo := (a.geometry i l hl.1 (cfg.leftTime k s i) (cfg.leftTime_mem k s i)).1
    have hβ : |(cfg.b k l 0 + cfg.leftTime k s i * cfg.b k l 3 - cfg.horizontalOrigin k s i) /
        cfg.timeLength k s| ≤ cfg.K k := by
      rw [abs_div, abs_of_pos hH]
      apply (div_le_iff₀ hH).mpr
      convert hgeo using 1
      simp only [x, Matrix.cons_val_one, Matrix.cons_val_zero, horizontalOrigin]
      congr 1
      ring
    exact (add_le_add hβ (show |cfg.b k l 3| ≤ cfg.K k from hl.2)).trans_eq (by ring)
  · simp only [clippedIntercept, clippedVelocity, Set.indicator_of_notMem hl, abs_zero, add_zero]
    positivity

/-- All arms seen by any original retained law are unchanged by clipping. -/
theorem AssignmentLevel.ae_goodArms (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (σ : Measure (α × ℝ))
    (hσ : σ ≤ (cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))) :
    ∀ᵐ p ∂σ, p.1 ∈ cfg.goodArms k s i := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  let νA := (cfg.ν k).restrict (cfg.A k s i)
  have hAC : σ ≪ νA.prod (volume : Measure ℝ) :=
    Measure.absolutelyContinuous_of_le_smul (a.restricted_original_domination h i σ hσ)
  have hνA : ∀ᵐ l ∂νA, l ∈ cfg.A k s i := ae_restrict_mem (a.measurable i)
  have hprodA : ∀ᵐ p ∂νA.prod (volume : Measure ℝ), p.1 ∈ cfg.A k s i := by
    apply (Measure.ae_prod_iff_ae_ae ((a.measurable i).preimage measurable_fst)).mpr
    exact hνA.mono (fun l hl => Filter.Eventually.of_forall (fun _ => hl))
  obtain ⟨hb, _, _, _, _, _, _, _, hprior, _⟩ := h.basic k
  have hνv : ∀ᵐ l ∂cfg.ν k, |cfg.b k l 3| ≤ cfg.K k := hprior.mono (fun l hl => by
    linarith [abs_nonneg (cfg.b k l 0), abs_nonneg (cfg.b k l 1), abs_nonneg (cfg.b k l 4)])
  have hνAv : ∀ᵐ l ∂νA, |cfg.b k l 3| ≤ cfg.K k :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le hνv
  have hprodv : ∀ᵐ p ∂νA.prod (volume : Measure ℝ), |cfg.b k p.1 3| ≤ cfg.K k := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
      (((measurable_pi_apply 3).comp hb).comp measurable_fst).abs measurable_const)).mpr
    exact hνAv.mono (fun l hl => Filter.Eventually.of_forall (fun _ => hl))
  have hσA : ∀ᵐ p ∂σ, p.1 ∈ cfg.A k s i := hAC.ae_le hprodA
  have hσv : ∀ᵐ p ∂σ, |cfg.b k p.1 3| ≤ cfg.K k := hAC.ae_le hprodv
  exact hσA.and hσv

theorem AssignmentLevel.clipped_coordinates_ae (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (σ : Measure (α × ℝ))
    (hσ : σ ≤ (cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))) :
    ∀ᵐ p ∂σ,
      cfg.clippedIntercept k s i p.1 =
        (cfg.b k p.1 0 + cfg.leftTime k s i * cfg.b k p.1 3 - cfg.horizontalOrigin k s i) / cfg.timeLength k s ∧
      cfg.clippedVelocity k s i p.1 = cfg.b k p.1 3 :=
  (a.ae_goodArms h i σ hσ).mono (fun p hp => cfg.clipped_coordinates_of_mem k s i p.1 hp)

/-- Every retained original law has the exact closed true time-block support. -/
theorem original_block_support (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (σ : Measure (α × ℝ))
    (hσ : σ ≤ (cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))) :
    σ (univ ×ˢ Icc (cfg.leftTime k s i) (cfg.leftTime k s i + cfg.timeLength k s))ᶜ = 0 := by
  apply nonpos_iff_eq_zero.mp
  calc
    _ ≤ ((cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)))
        (univ ×ˢ Icc (cfg.leftTime k s i) (cfg.leftTime k s i + cfg.timeLength k s))ᶜ := hσ _
    _ = 0 := by
      rw [Measure.restrict_apply (MeasurableSet.univ.prod measurableSet_Icc).compl]
      have heq : (univ ×ˢ Icc (cfg.leftTime k s i) (cfg.leftTime k s i + cfg.timeLength k s))ᶜ ∩
          (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) = ∅ := by
        ext p
        simp only [cfg.true_block_eq k s i, mem_inter_iff, mem_compl_iff, mem_prod,
          mem_univ, true_and, mem_empty_iff_false]
        tauto
      rw [heq, measure_empty]

theorem normalized_block_support (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (σ : Measure (α × ℝ))
    (hσ : σ ≤ (cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))) :
    (ENNReal.ofReal (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i))⁻¹ •
      σ.map (unitTimeMap (cfg.leftTime k s i) (cfg.timeLength k s)))
      (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
  apply original_continuous_normalized_support σ (cfg.leftTime k s i) (cfg.timeLength k s)
    (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i)) (by unfold timeLength; positivity)
  exact cfg.original_block_support k s i σ hσ

/-- The native velocity and contact defect bounds pass to every retained
original law without changing either reference or prior. -/
theorem AssignmentLevel.retained_native_bounds (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (σ : Measure (α × ℝ))
    (hσ : σ ≤ (cfg.ρ k).restrict (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))) :
    ∀ᵐ p ∂σ, |cfg.b k p.1 3| ≤ 4 * cfg.K k ∧
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ (4 * cfg.K k) * cfg.N k ^ (-cfg.e₀) := by
  have hσμ : σ ≤ cfg.μ k := hσ.trans
    (Measure.restrict_le_self.trans (h.basic k).2.2.2.2.1)
  have hdef : ∀ᵐ p ∂σ, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) :=
    hσμ.absolutelyContinuous.ae_le (a.horizontal_equation i)
  have hgood := a.ae_goodArms h i σ hσ
  filter_upwards [hdef, hgood] with p hp hg
  constructor
  · exact (show |cfg.b k p.1 3| ≤ cfg.K k from hg.2).trans (by linarith [h.subpower.1 k])
  · exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg (by linarith [h.scale k]) _)
      (by linarith [h.subpower.1 k]))

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
