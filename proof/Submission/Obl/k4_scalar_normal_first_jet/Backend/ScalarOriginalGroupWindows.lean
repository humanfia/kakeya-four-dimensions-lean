/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarOriginalGroupWindows.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarOriginalGroupWindows.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarManyGroups
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGroupLeftMass
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Choose

/-! Select all substantial original anchor groups and sum their unchanged masses. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem exists_original_group_window_restriction {Λ Θ : Type*}
    [MeasurableSpace Λ] [MeasurableSpace Θ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (μ : Measure Θ) [IsProbabilityMeasure μ]
    (Aanchor : Set Λ) {E : Set (Λ × Θ)} (hE : MeasurableSet E)
    (hEA : E ⊆ Aanchor ×ˢ univ) (code : Λ → ℤ) (hcode : Measurable code)
    (slope : Λ → ℝ) (hslope : Measurable slope) (J : Finset ℤ)
    (hcover : ∀ q ∈ E, code q.1 ∈ J) {c C B ρ radius : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hB : 0 < B) (hρ : 0 ≤ ρ)
    (hcard : (J.card : ℝ) ≤ C / c)
    (hcap : ∀ b ∈ J, (ν.prod μ).real (E ∩ ((code ⁻¹' {b}) ×ˢ univ)) ≤ C * c)
    (hselect : ∀ b ∈ J,
      c / B ≤ (ν.prod μ).real (E ∩ ((code ⁻¹' {b}) ×ˢ univ)) →
      ∃ center : ℝ, ρ < ((scalarGroupPrior (ν.restrict Aanchor) code b c).prod μ).real
        ((E ∩ ((code ⁻¹' {b}) ×ˢ univ)) ∩
          ({l | |slope l - center| ≤ radius} ×ˢ univ))) :
    ∃ (center : ℤ → ℝ) (A : Set Λ), MeasurableSet A ∧
      (∀ l ∈ A, code l ∈ J ∧ |slope l - center (code l)| ≤ radius) ∧
      (ρ / C) * ((ν.prod μ).real E - C / B) ≤ (ν.prod μ).real (E ∩ (A ×ˢ univ)) := by
  classical
  let cell : ℤ → Set (Λ × Θ) := fun b => E ∩ ((code ⁻¹' {b}) ×ˢ univ)
  have hcellEq b : E ∩ (fun q : Λ × Θ => code q.1) ⁻¹' {b} = cell b := by
    ext q
    simp only [cell, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_prod, mem_univ, and_true]
  let Good := J.filter (fun b => c / B ≤ (ν.prod μ).real (cell b))
  have hgood b (hb : b ∈ Good) : ∃ center : ℝ,
      ρ < ((scalarGroupPrior (ν.restrict Aanchor) code b c).prod μ).real
        (cell b ∩ ({l | |slope l - center| ≤ radius} ×ˢ univ)) :=
    hselect b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2
  choose! center hcenter using hgood
  let W : ℤ → Set Λ := fun b => {l | code l = b ∧ |slope l - center b| ≤ radius}
  let A : Set Λ := ⋃ b ∈ Good, W b
  let R : ℤ → Set (Λ × Θ) := fun b => if b ∈ Good then E ∩ (W b ×ˢ univ) else ∅
  have hW b : MeasurableSet (W b) := by
    have hinterval : {l | |slope l - center b| ≤ radius} =
        (fun l => slope l - center b) ⁻¹' Icc (-radius) radius := by
      ext l
      change |slope l - center b| ≤ radius ↔ -radius ≤ slope l - center b ∧ slope l - center b ≤ radius
      exact abs_le
    have hwindow : MeasurableSet {l | |slope l - center b| ≤ radius} := by
      rw [hinterval]
      exact (hslope.sub_const (center b)) measurableSet_Icc
    exact (hcode (MeasurableSet.singleton b)).inter
      hwindow
  have hAm : MeasurableSet A := Good.measurableSet_biUnion (fun b _ => hW b)
  have hRm b (_hb : b ∈ J) : MeasurableSet (R b) := by
    dsimp only [R]
    split_ifs
    · exact hE.inter ((hW b).prod MeasurableSet.univ)
    · exact MeasurableSet.empty
  have hRsub b (_hb : b ∈ J) : R b ⊆ E ∩ (fun q : Λ × Θ => code q.1) ⁻¹' {b} := by
    intro q hq
    dsimp only [R] at hq
    split_ifs at hq with hb
    · exact ⟨hq.1, hq.2.1.1⟩
    · exact False.elim hq
  have hRselect b (hb : b ∈ J)
      (hmass : B⁻¹ * c ≤ (ν.prod μ).real (E ∩ (fun q : Λ × Θ => code q.1) ⁻¹' {b})) :
      ρ * c ≤ (ν.prod μ).real (R b) := by
    have hthreshold : c / B = B⁻¹ * c := by ring
    have hbgood : b ∈ Good := Finset.mem_filter.mpr ⟨hb, by rw [hthreshold]; exact hcellEq b ▸ hmass⟩
    have hRset : R b = cell b ∩ ({l | |slope l - center b| ≤ radius} ×ˢ univ) := by
      rw [show R b = E ∩ (W b ×ˢ univ) from by simp only [R, if_pos hbgood]]
      ext q
      simp only [W, cell, mem_inter_iff, mem_prod, mem_univ, mem_preimage, mem_singleton_iff,
        mem_setOf_eq, and_true]
      tauto
    have hleft := original_scalar_group_left_mass μ ν Aanchor code b hc (hRm b hb)
      (fun q hq => ⟨⟨(hEA (hRsub b hb hq).1).1, (hRsub b hb hq).2⟩, mem_univ _⟩)
    have hh := hcenter b hbgood
    rw [← hRset, hleft] at hh
    exact ((lt_div_iff₀ hc).mp hh).le
  have hRmass := original_mass_from_many_good_cells (ν.prod μ) hE
    (hcode.comp measurable_fst) J hcover R hRm hRsub hC hc (inv_nonneg.mpr hB.le) hρ
    (fun b hb => by
      change (ν.prod μ).real (E ∩ (fun q : Λ × Θ => code q.1) ⁻¹' {b}) ≤ C * c
      rw [hcellEq b]
      exact hcap b hb) hRselect
  have hlight : B⁻¹ * c * (J.card : ℝ) ≤ C / B := by
    have hh := mul_le_mul_of_nonneg_left ((le_div_iff₀ hc).mp hcard) (inv_nonneg.mpr hB.le)
    convert hh using 1 <;> ring
  have hReq : (⋃ b ∈ J, R b) = E ∩ (A ×ˢ univ) := by
    ext q
    constructor
    · intro hq
      have hx : ∃ b ∈ J, q ∈ R b := by simpa only [mem_iUnion, exists_prop] using hq
      obtain ⟨b, hb, hqb⟩ := hx
      dsimp only [R] at hqb
      split_ifs at hqb with hgood
      · exact ⟨hqb.1, mem_biUnion hgood hqb.2.1, mem_univ _⟩
      · exact False.elim hqb
    · intro hq
      have hx : ∃ b ∈ Good, q.1 ∈ W b := by simpa only [A, mem_iUnion, exists_prop] using hq.2.1
      obtain ⟨b, hb, hqb⟩ := hx
      exact mem_biUnion (Finset.mem_filter.mp hb).1 (by
        simp only [R, if_pos hb]
        exact ⟨hq.1, hqb, mem_univ _⟩)
  refine ⟨center, A, hAm, ?_, ?_⟩
  · intro l hl
    have hx : ∃ b ∈ Good, l ∈ W b := by simpa only [A, mem_iUnion, exists_prop] using hl
    obtain ⟨b, hb, hlb⟩ := hx
    exact ⟨hlb.1.symm ▸ (Finset.mem_filter.mp hb).1, by simpa only [hlb.1] using hlb.2⟩
  · rw [← hReq]
    exact (mul_le_mul_of_nonneg_left (by linarith : (ν.prod μ).real E - C / B ≤
      (ν.prod μ).real E - B⁻¹ * c * (J.card : ℝ)) (div_nonneg hρ hC.le)).trans hRmass

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
