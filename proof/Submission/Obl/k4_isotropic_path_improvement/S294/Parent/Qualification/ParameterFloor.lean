-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ParameterFloor, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ParameterFloor.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ParameterFloor.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ParameterFloor.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_scalar_coefficient_clustering
import Submission.Obl.k4_plank_estimate

/-!
Deleting light coefficient blocks. The mass defining a light block is always
its mass under the original prior. Scalar clustering is applied only to the
restriction to the union of such blocks; no new saturation is asserted there.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open MeasureTheory
open Submission.Obl.k4_scalar_coefficient_clustering

noncomputable section

/-- Coefficient blocks whose ORIGINAL prior mass is below `H`. Auxiliary
trajectory labels are retained by the coefficient map `a`. -/
def lightCoefficientBlocks {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (a : α → EuclideanSpace ℝ (Fin 3)) (p : ℝ) (H : ENNReal) : Set α :=
  {l | ν {l' | coefficientCode p (a l') = coefficientCode p (a l)} < H}

theorem measurableSet_lightCoefficientBlocks {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {a : α → EuclideanSpace ℝ (Fin 3)} (ha : Measurable a)
    (p : ℝ) (H : ENNReal) : MeasurableSet (lightCoefficientBlocks ν a p H) := by
  let Q : Set (Fin 3 → ℤ) := {q | ν {l | coefficientCode p (a l) = q} < H}
  exact ((measurable_coefficientCode p).comp ha) ((Set.to_countable Q).measurableSet)

/-- The restriction to light blocks has no heavy coefficient fiber. -/
theorem lightCoefficientBlocks_fiber_lt {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {a : α → EuclideanSpace ℝ (Fin 3)} (ha : Measurable a)
    (p : ℝ) {H : ENNReal} (hH : 0 < H) (q : Fin 3 → ℤ) :
    (ν.restrict (lightCoefficientBlocks ν a p H))
      {l | coefficientCode p (a l) = q} < H := by
  classical
  by_cases hq : ν {l | coefficientCode p (a l) = q} < H
  · exact lt_of_le_of_lt (Measure.restrict_le_self _) hq
  · have hnull : {l | coefficientCode p (a l) = q} ∩
        lightCoefficientBlocks ν a p H = ∅ := by
      ext l
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hl, hb⟩
      exact hq (by simpa only [lightCoefficientBlocks, Set.mem_ofPred_eq, hl] using hb)
    have hm : MeasurableSet {l | coefficientCode p (a l) = q} :=
      ((measurable_coefficientCode p).comp ha) (measurableSet_singleton q)
    rw [Measure.restrict_apply hm, hnull, measure_empty]
    exact hH

/-- Scalar clustering removes light coefficient blocks at a power-small
occupation cost. All masses in the definition of the removed blocks use
the unchanged prior `ν`; the estimate is for its original product measure. -/
theorem coefficient_floor_cleanup (d c ε : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α]
        (ν : Measure α) (a : α → EuclideanSpace ℝ (Fin 3))
        (E : Set (α × ℝ)) (F : Finset (ℤ × ℤ)),
        Measurable a → MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 →
        (∀ l, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ ENNReal.ofReal (N ^ η) →
        (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d) →
        (∀ l t, (l, t) ∈ E →
          (⌊t / (N ^ (-c))⌋,
            ⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / (N ^ (-c))⌋) ∈ F) →
        (∀ b r, N ^ (-c) ≤ r →
          ν {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ η * r ^ d)) →
        (ν.prod volume) (E ∩ (lightCoefficientBlocks ν a (N ^ (-c))
          (ENNReal.ofReal (N ^ (-c * d - ε))) ×ˢ Set.univ)) <
          ENNReal.ofReal (N ^ (-η)) := by
  obtain ⟨η, hη, N₀, hN₀, hcluster⟩ := Submission.k4_scalar_coefficient_clustering
    Submission.k4_plank_estimate d c ε hd hd1 hc hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α mα ν a E F ha hE hunit hcoeff hν hsize hsupport hcap
  let _ : IsFiniteMeasure ν := ⟨hν.trans_lt ENNReal.ofReal_lt_top⟩
  let B := lightCoefficientBlocks ν a (N ^ (-c)) (ENNReal.ofReal (N ^ (-c * d - ε)))
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hN₀.trans hN)
  have hH : 0 < ENNReal.ofReal (N ^ (-c * d - ε)) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hNpos _)
  have hνB : (ν.restrict B) Set.univ ≤ ENNReal.ofReal (N ^ η) :=
    (Measure.restrict_le_self _).trans hν
  have hcapB : ∀ b r, N ^ (-c) ≤ r →
      (ν.restrict B) {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ η * r ^ d) := by
    intro b r hr
    exact (Measure.restrict_le_self _).trans (hcap b r hr)
  have hprod : ((ν.restrict B).prod volume) E =
      (ν.prod volume) (E ∩ (B ×ˢ Set.univ)) := by
    rw [Measure.restrict_prod_eq_prod_univ B, Measure.restrict_apply hE]
  by_contra hsmall
  have hlarge : ENNReal.ofReal (N ^ (-η)) ≤ ((ν.restrict B).prod volume) E := by
    rw [hprod]
    exact le_of_not_gt hsmall
  obtain ⟨q, hq⟩ := hcluster N hN α (ν.restrict B) a E F ha hE hunit
    hcoeff hνB hlarge hsize hsupport hcapB
  have hsub : {l | (∀ j, ⌊a l j / (N ^ (-c))⌋ = q j) ∧
      ENNReal.ofReal (N ^ (-ε)) ≤ volume {t : ℝ | (l, t) ∈ E}} ⊆
        {l | coefficientCode (N ^ (-c)) (a l) = q} := by
    rintro l ⟨hl, -⟩
    exact funext hl
  exact (not_le_of_gt (lightCoefficientBlocks_fiber_lt ν ha (N ^ (-c)) hH q))
    (hq.trans (measure_mono hsub))

/-- Scaling for an application of clustering does not change which
ORIGINAL coefficient masses define the removed blocks. -/
theorem lightCoefficientBlocks_scaled {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (a : α → EuclideanSpace ℝ (Fin 3)) (p : ℝ)
    (s H : ENNReal) (hs : s ≠ 0) (hst : s ≠ ⊤) :
    lightCoefficientBlocks (s⁻¹ • ν) a p H = lightCoefficientBlocks ν a p (s * H) := by
  ext l
  simp only [lightCoefficientBlocks, Set.mem_ofPred_eq, Measure.smul_apply, smul_eq_mul]
  let v := ν {l' | coefficientCode p (a l') = coefficientCode p (a l)}
  change s⁻¹ * v < H ↔ v < s * H
  constructor
  · intro h
    have hh := ENNReal.mul_lt_mul_left hs hst h
    have heq : (s⁻¹ * v) * s = v := by
      rw [mul_comm _ s, ← mul_assoc, ENNReal.mul_inv_cancel hs hst, one_mul]
    simpa only [heq, mul_comm H s] using hh
  · intro h
    have hinv : s⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hst
    have hinvt : s⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hs
    have hh := ENNReal.mul_lt_mul_left hinv hinvt h
    have heq : (s * H) * s⁻¹ = H := by
      rw [mul_comm _ s⁻¹, ← mul_assoc, ENNReal.inv_mul_cancel hs hst, one_mul]
    simpa only [heq, mul_comm v s⁻¹] using hh

/-- The cleanup estimate for an affine-bin prior of arbitrary positive
mass scale `s`. Neither its occupation nor its coefficient floors are
renormalized in the conclusion. -/
theorem coefficient_floor_cleanup_scaled (d c ε : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α]
        (ν : Measure α) (a : α → EuclideanSpace ℝ (Fin 3))
        (E : Set (α × ℝ)) (F : Finset (ℤ × ℤ)) (s : ENNReal),
        s ≠ 0 → s ≠ ⊤ → Measurable a → MeasurableSet E →
        E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 →
        (∀ l, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ s * ENNReal.ofReal (N ^ η) →
        (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d) →
        (∀ l t, (l, t) ∈ E →
          (⌊t / (N ^ (-c))⌋,
            ⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / (N ^ (-c))⌋) ∈ F) →
        (∀ b r, N ^ (-c) ≤ r →
          ν {l | a l ∈ Metric.ball b r} ≤ s * ENNReal.ofReal (N ^ η * r ^ d)) →
        (ν.prod volume) (E ∩ (lightCoefficientBlocks ν a (N ^ (-c))
          (s * ENNReal.ofReal (N ^ (-c * d - ε))) ×ˢ Set.univ)) <
          s * ENNReal.ofReal (N ^ (-η)) := by
  obtain ⟨η, hη, N₀, hN₀, hclean⟩ := coefficient_floor_cleanup d c ε hd hd1 hc hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α mα ν a E F s hs hst ha hE hunit hcoeff hν hsize hsupport hcap
  have hν' : (s⁻¹ • ν) Set.univ ≤ ENNReal.ofReal (N ^ η) := by
    simpa only [Measure.smul_apply, smul_eq_mul] using
      (ENNReal.inv_mul_le_iff hs hst).mpr hν
  have hcap' : ∀ b r, N ^ (-c) ≤ r →
      (s⁻¹ • ν) {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ η * r ^ d) := by
    intro b r hr
    simpa only [Measure.smul_apply, smul_eq_mul] using
      (ENNReal.inv_mul_le_iff hs hst).mpr (hcap b r hr)
  have h := hclean N hN α (s⁻¹ • ν) a E F ha hE hunit hcoeff hν' hsize hsupport hcap'
  rw [lightCoefficientBlocks_scaled ν a _ s _ hs hst,
    Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul] at h
  have hh := ENNReal.mul_lt_mul_left hs hst h
  have heq (v : ENNReal) : (s⁻¹ * v) * s = v := by
    rw [mul_comm _ s, ← mul_assoc, ENNReal.mul_inv_cancel hs hst, one_mul]
  simpa only [heq, mul_comm _ s] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
