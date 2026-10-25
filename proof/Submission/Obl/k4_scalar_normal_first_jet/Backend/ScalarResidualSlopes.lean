/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarResidualSlopes.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarResidualSlopes.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarSlopeDuration
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAffineCollisions
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarADCollisions
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCollisionCellCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridGeometry

/-! Residual-slope concentration from actual original collisions. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

/-- Quantitative close/far collision contradiction for the first-jet
residual. All cell floors, incidence caps and collision masses use the
unchanged original trajectory prior. -/
theorem exists_original_heavy_residual_slope {Λ ι : Type*}
    [MeasurableSpace Λ] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ ≤ volume)
    (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Λ × ℝ)} (hE : MeasurableSet E) {A : Set Λ} (hA : MeasurableSet A)
    (hEsub : E ⊆ A ×ˢ Icc (0 : ℝ) 1)
    {F : ℝ × Λ → ℝ} (hF : Measurable F) (a slope : Λ → ℝ) (hslope : Measurable slope)
    {code : Λ → ι} (hcode : Measurable code) (J : Finset ι)
    (hcover : ∀ l ∈ A, code l ∈ J)
    {p d Cs R left C Δ D m τ η err : ℝ}
    (hp : 0 < p) (hpR : p ≤ R) (hCs : 0 ≤ Cs) (hC : 0 ≤ C)
    (hΔ : 0 < Δ) (hm : 0 < m) (hτ : 0 < τ) (hη : 0 ≤ η) (herr : 0 ≤ err)
    (S : ℝ → Set ℝ) (hS : ∀ t, IntervalAD p d Cs (S t))
    (hsupport : ∀ l t, (l, t) ∈ E → F (t, l) ∈ S t ∩ Icc left (left + R))
    (hfit : ∀ l t, (l, t) ∈ E → |F (t, l) - (a l + slope l * t)| ≤ err)
    (hlong : ∀ l ∈ A, ENNReal.ofReal τ ≤ volume (Prod.mk l ⁻¹' E))
    (hfloor : ∀ j ∈ J, (A ∩ code ⁻¹' {j}).Nonempty → m ≤ ν.real (A ∩ code ⁻¹' {j}))
    (hspread : ∀ l ∈ A, ∀ l' ∈ A, code l = code l' → |slope l - slope l'| ≤ D)
    (hjoint : ∀ t j, j ∈ J → ∀ b : ℤ,
      ν.real {l | (l, t) ∈ E ∧ code l = j ∧ (⌊F (t, l) / p⌋ : ℤ) = b} ≤ C)
    (hgap : (3 * (Cs * (R / p) ^ d)) *
      (((η / τ) / m * C) * ν.real univ +
        (2 * (p + 2 * err) / Δ) * (ν.real univ) ^ 2) <
      ((μ.prod ν).real {q : ℝ × Λ | (q.2, q.1) ∈ E}) ^ 2) :
    ∃ c : ℝ, η < (ν.prod volume).real
      (E ∩ ({l | l ∈ A ∧ |slope l - c| ≤ Δ + D} ×ˢ univ)) := by
  classical
  by_contra hn
  push Not at hn
  let E' : Set (ℝ × Λ) := Prod.swap ⁻¹' E
  have hE' : MeasurableSet E' := hE.preimage measurable_swap
  let Y : ℝ × Λ → ℤ := fun q => ⌊F q / p⌋
  have hY : Measurable Y := Int.measurable_floor.comp (hF.div_const p)
  let Coll : Set (ℝ × (Λ × Λ)) :=
    {q | (q.1, q.2.1) ∈ E' ∧ (q.1, q.2.2) ∈ E' ∧ Y (q.1, q.2.1) = Y (q.1, q.2.2)}
  have hleft : Measurable (fun q : ℝ × (Λ × Λ) => (q.1, q.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hright : Measurable (fun q : ℝ × (Λ × Λ) => (q.1, q.2.2)) :=
    measurable_fst.prodMk measurable_snd.snd
  have hColl : MeasurableSet Coll := (hE'.preimage hleft).inter
    ((hE'.preimage hright).inter (measurableSet_eq_fun (hY.comp hleft) (hY.comp hright)))
  let Near : Set (ℝ × (Λ × Λ)) := Coll ∩ {q | |slope q.2.1 - slope q.2.2| ≤ Δ}
  have hNear : MeasurableSet Near := hColl.inter (measurableSet_le
    ((hslope.comp measurable_snd.fst).sub (hslope.comp measurable_snd.snd)).abs measurable_const)
  let Far := Coll \ Near
  have hFar : MeasurableSet Far := hColl.diff hNear
  have hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun q hq => ⟨mem_univ _, (hEsub hq).2⟩
  let Q : ℝ := (η / τ) / m * C
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hsecond : ∀ t l, ν.real ((fun l' => (t, (l, l'))) ⁻¹' Near) ≤ Q := by
    intro t l
    let Z : Set Λ := (fun l' => (t, (l, l'))) ⁻¹' Near
    have hZ : ∀ l' ∈ Z, l' ∈ A ∧ code l' ∈ J ∧ |slope l' - slope l| ≤ Δ := by
      intro l' hl'
      have hE₂ : (l', t) ∈ E := hl'.1.2.1
      have hA₂ := (hEsub hE₂).1
      have hclose : |slope l - slope l'| ≤ Δ := hl'.2
      exact ⟨hA₂, hcover l' hA₂, by simpa only [abs_sub_comm] using hclose⟩
    have hout : ∀ j ∈ J, ν.real (Z ∩ code ⁻¹' {j}) ≤ C := by
      intro j hj
      have hsub : Z ∩ code ⁻¹' {j} ⊆
          {l' | (l', t) ∈ E ∧ code l' = j ∧ (⌊F (t, l') / p⌋ : ℤ) = ⌊F (t, l) / p⌋} := by
        intro l' hl'
        exact ⟨hl'.1.1.2.1, hl'.2, hl'.1.1.2.2.symm⟩
      exact (measureReal_mono hsub).trans (hjoint t j hj _)
    exact original_near_slope_output_cap_of_incidence ν hE hunit hA hcode J hslope hm hτ hC
      hlong hfloor hspread (hn (slope l)) Z hZ hout
  have hnearTime : ∀ t, (ν.prod ν).real (Prod.mk t ⁻¹' Near) ≤ Q * ν.real univ := by
    intro t
    exact original_spacetime_cell_cap ν ν (measurable_prodMk_left hNear) MeasurableSet.univ
      (fun q _ => ⟨mem_univ _, mem_univ _⟩) hQ (fun l _ => hsecond t l)
  have hnear : (μ.prod (ν.prod ν)).real Near ≤ Q * ν.real univ := by
    have h := original_spacetime_cell_cap μ (ν.prod ν) hNear MeasurableSet.univ
      (fun q _ => ⟨mem_univ _, mem_univ _⟩) (mul_nonneg hQ measureReal_nonneg)
      (fun t _ => hnearTime t)
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h
  have hfar : (μ.prod (ν.prod ν)).real Far ≤
      (2 * (p + 2 * err) / Δ) * (ν.real univ) ^ 2 := by
    apply original_far_slope_collision_cap μ hμ ν hFar (fun t l => F (t, l)) a slope hp.le herr hΔ
    intro q hq
    have hc : q ∈ Coll := hq.1
    have hnot : ¬ |slope q.2.1 - slope q.2.2| ≤ Δ := fun h => hq.2 ⟨hc, h⟩
    exact ⟨(lt_of_not_ge hnot).le, hfit _ _ hc.1, hfit _ _ hc.2.1,
      same_mesh_cell_close hp hc.2.2⟩
  have htotal : (μ.prod (ν.prod ν)).real Coll ≤ Q * ν.real univ +
      (2 * (p + 2 * err) / Δ) * (ν.real univ) ^ 2 := by
    have heq : Coll = Near ∪ Far := by
      ext q
      constructor
      · intro hq
        by_cases hn : q ∈ Near
        · exact Or.inl hn
        · exact Or.inr ⟨hq, hn⟩
      · intro hq
        exact hq.elim (fun hn => hn.1) (fun hf => hf.1)
    calc
      _ = (μ.prod (ν.prod ν)).real (Near ∪ Far) := congrArg _ heq
      _ ≤ (μ.prod (ν.prod ν)).real Near + (μ.prod (ν.prod ν)).real Far := measureReal_union_le _ _
      _ ≤ _ := add_le_add hnear hfar
  have hmean : (∫ t, (ν.prod ν).real (Prod.mk t ⁻¹' Coll) ∂μ) =
      (μ.prod (ν.prod ν)).real Coll := by
    unfold Measure.real
    rw [integral_toReal (measurable_measure_prodMk_left hColl).aemeasurable
      (Filter.Eventually.of_forall fun t => measure_lt_top (ν.prod ν) _), Measure.prod_apply hColl]
  have hlower := original_intervalAD_collision_lower μ ν hE' hF hp hpR S hS
    (fun t l hl => hsupport l t hl)
  change ((μ.prod ν).real E') ^ 2 ≤ (3 * (Cs * (R / p) ^ d)) *
    (∫ t, (ν.prod ν).real (Prod.mk t ⁻¹' Coll) ∂μ) at hlower
  rw [hmean] at hlower
  have hR : 0 ≤ R := hp.le.trans hpR
  have hB : 0 ≤ 3 * (Cs * (R / p) ^ d) := by positivity
  have hbound := hlower.trans (mul_le_mul_of_nonneg_left htotal hB)
  exact (not_lt_of_ge hbound) hgap

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
