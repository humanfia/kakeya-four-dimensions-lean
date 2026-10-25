/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarManyGroups.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarManyGroups.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCellMass
import Mathlib.Tactic.FieldSimp

/-! Aggregate all substantial original groups without paying their number. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open scoped BigOperators

theorem original_mass_from_many_good_cells {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] {E : Set Ω} (hE : MeasurableSet E)
    {code : Ω → ι} (hcode : Measurable code) (J : Finset ι)
    (hcover : ∀ x ∈ E, code x ∈ J) (R : ι → Set Ω)
    (hRm : ∀ b ∈ J, MeasurableSet (R b))
    (hRsub : ∀ b ∈ J, R b ⊆ E ∩ code ⁻¹' {b})
    {C c η ρ : ℝ} (hC : 0 < C) (hc : 0 < c) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hcap : ∀ b ∈ J, μ.real (E ∩ code ⁻¹' {b}) ≤ C * c)
    (hselect : ∀ b ∈ J, η * c ≤ μ.real (E ∩ code ⁻¹' {b}) → ρ * c ≤ μ.real (R b)) :
    (ρ / C) * (μ.real E - η * c * (J.card : ℝ)) ≤ μ.real (⋃ b ∈ J, R b) := by
  have hratio : 0 ≤ ρ / C := div_nonneg hρ hC.le
  have hdisj : PairwiseDisjoint (J : Set ι) R := by
    intro b hb b' hb' hne
    apply disjoint_left.mpr
    intro x hx hx'
    exact hne ((hRsub b hb hx).2.symm.trans (hRsub b' hb' hx').2)
  have hmassR : μ.real (⋃ b ∈ J, R b) = ∑ b ∈ J, μ.real (R b) :=
    measureReal_biUnion_finset hdisj hRm
  have hcell b (hb : b ∈ J) :
      (ρ / C) * μ.real (E ∩ code ⁻¹' {b}) ≤
        (ρ / C) * (η * c) + μ.real (R b) := by
    by_cases hgood : η * c ≤ μ.real (E ∩ code ⁻¹' {b})
    · have hbound := mul_le_mul_of_nonneg_left (hcap b hb) hratio
      have he : (ρ / C) * (C * c) = ρ * c := by field_simp
      rw [he] at hbound
      exact (hbound.trans (hselect b hb hgood)).trans
        (le_add_of_nonneg_left (mul_nonneg hratio (mul_nonneg hη hc.le)))
    · have hh := mul_le_mul_of_nonneg_left (not_le.mp hgood).le hratio
      exact hh.trans (by linarith [show 0 ≤ μ.real (R b) from measureReal_nonneg])
  have hsum := Finset.sum_le_sum hcell
  rw [← Finset.mul_sum, sum_original_code_masses μ hE hcode J hcover,
    Finset.sum_add_distrib] at hsum
  have hconst : (∑ _b ∈ J, (ρ / C) * (η * c)) =
      (ρ / C) * (η * c * (J.card : ℝ)) := by simp; ring
  rw [hconst, ← hmassR] at hsum
  nlinarith

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
