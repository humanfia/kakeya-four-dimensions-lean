/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockPreparation.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockPreparation.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCellMass

/-! Delete light time blocks without changing any trajectory prior. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open scoped BigOperators

theorem prepare_original_time_blocks {Λ ι : Type*} [MeasurableSpace Λ]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ]
    {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (code : ℝ → ι) (hcode : Measurable code) {H τ : ℝ} (hH : 0 ≤ H) (hτ : 0 ≤ τ)
    (hpartition : (Fintype.card ι : ℝ) * H ≤ 1)
    (hcellcap : ∀ i, μ.real (E ∩ (fun p => code p.2) ⁻¹' {i}) ≤ H) :
    ∃ (J : Finset ι) (U : Set ℝ), U = code ⁻¹' (J : Set ι) ∧ MeasurableSet U ∧
      μ.real E ≤ μ.real (E ∩ (univ ×ˢ U)) + τ ∧
      (∀ i ∈ J, τ * H ≤ μ.real ((E ∩ (univ ×ˢ U)) ∩ (fun p => code p.2) ⁻¹' {i})) ∧
      μ.real (E ∩ (univ ×ˢ U)) ≤ (J.card : ℝ) * H := by
  classical
  let m : ι → ℝ := fun i => μ.real (E ∩ (fun p => code p.2) ⁻¹' {i})
  let J := Finset.univ.filter (fun i => τ * H ≤ m i)
  let B := Finset.univ.filter (fun i => ¬τ * H ≤ m i)
  let U : Set ℝ := code ⁻¹' (J : Set ι)
  let R : Set (Λ × ℝ) := E ∩ (univ ×ˢ U)
  have hUm : MeasurableSet U := hcode J.finite_toSet.measurableSet
  have hRm : MeasurableSet R := hE.inter (MeasurableSet.univ.prod hUm)
  have hpaircode : Measurable (fun p : Λ × ℝ => code p.2) := hcode.comp measurable_snd
  have hsum : ∑ i, m i = μ.real E :=
    sum_original_code_masses μ hE hpaircode Finset.univ (fun _ _ => Finset.mem_univ _)
  have hcell i (hi : i ∈ J) : R ∩ (fun p => code p.2) ⁻¹' {i} =
      E ∩ (fun p => code p.2) ⁻¹' {i} := by
    ext p
    constructor
    · exact fun hp => ⟨hp.1.1, hp.2⟩
    · intro hp
      refine ⟨⟨hp.1, mem_univ _, ?_⟩, hp.2⟩
      change code p.2 ∈ J
      rw [show code p.2 = i from hp.2]
      exact hi
  have hret : μ.real R = ∑ i ∈ J, m i := by
    have h := sum_original_code_masses μ hRm hpaircode J (fun p hp => hp.2.2)
    rw [← h]
    exact Finset.sum_congr rfl (fun i hi => congrArg μ.real (hcell i hi))
  have hsplit : (∑ i ∈ J, m i) + (∑ i ∈ B, m i) = ∑ i, m i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hbad : ∑ i ∈ B, m i ≤ τ := by
    calc
      _ ≤ ∑ _i ∈ B, τ * H := Finset.sum_le_sum (fun i hi => (not_le.mp (Finset.mem_filter.mp hi).2).le)
      _ = τ * ((B.card : ℝ) * H) := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ τ * ((Fintype.card ι : ℝ) * H) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ B)) hH) hτ
      _ ≤ τ := by nlinarith
  refine ⟨J, U, rfl, hUm, ?_, ?_, ?_⟩
  · change μ.real E ≤ μ.real R + τ
    rw [hret, ← hsum]
    linarith
  · intro i hi
    rw [hcell i hi]
    exact (Finset.mem_filter.mp hi).2
  · change μ.real R ≤ (J.card : ℝ) * H
    rw [hret]
    calc
      _ ≤ ∑ _i ∈ J, H := Finset.sum_le_sum (fun i _ => hcellcap i)
      _ = _ := by simp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
