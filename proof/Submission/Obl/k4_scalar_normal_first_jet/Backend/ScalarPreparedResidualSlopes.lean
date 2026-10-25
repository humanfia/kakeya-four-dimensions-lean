/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarPreparedResidualSlopes.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarPreparedResidualSlopes.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarResidualSlopes
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLongCells
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUnitTime

/-! Residual-slope concentration including its original-law preparation. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

/-- The duration and cell floors used by the collision contradiction are
constructed here. Their complete cost is charged to the original event. -/
theorem exists_heavy_residual_slope_of_original_data {Λ ι : Type*}
    [MeasurableSpace Λ] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Λ × ℝ)} (hE : MeasurableSet E) {A₀ : Set Λ}
    (hEsub : E ⊆ A₀ ×ˢ Icc (0 : ℝ) 1)
    {F : ℝ × Λ → ℝ} (hF : Measurable F) (a slope : Λ → ℝ) (hslope : Measurable slope)
    {code : Λ → ι} (hcode : Measurable code) (J : Finset ι)
    (hcover : ∀ l t, (l, t) ∈ E → code l ∈ J)
    {p d Cs R left C Δ D m τ η err δ : ℝ}
    (hp : 0 < p) (hpR : p ≤ R) (hCs : 0 ≤ Cs) (hC : 0 ≤ C)
    (hΔ : 0 < Δ) (hm : 0 < m) (hτ : 0 < τ) (hη : 0 ≤ η) (herr : 0 ≤ err) (hδ : 0 < δ)
    (S : ℝ → Set ℝ) (hS : ∀ t, IntervalAD p d Cs (S t))
    (hsupport : ∀ l t, (l, t) ∈ E → F (t, l) ∈ S t ∩ Icc left (left + R))
    (hfit : ∀ l t, (l, t) ∈ E → |F (t, l) - (a l + slope l * t)| ≤ err)
    (hspread : ∀ l ∈ A₀, ∀ l' ∈ A₀, code l = code l' → |slope l - slope l'| ≤ D)
    (hjoint : ∀ t j, j ∈ J → ∀ b : ℤ,
      ν.real {l | (l, t) ∈ E ∧ code l = j ∧ (⌊F (t, l) / p⌋ : ℤ) = b} ≤ C)
    (hmass : δ ≤ (ν.prod volume).real E)
    (hbudget : τ * ν.real univ + m * (J.card : ℝ) ≤ δ / 2)
    (hgap : (3 * (Cs * (R / p) ^ d)) *
      (((η / τ) / m * C) * ν.real univ +
        (2 * (p + 2 * err) / Δ) * (ν.real univ) ^ 2) < (δ / 2) ^ 2) :
    ∃ c : ℝ, η < (ν.prod volume).real
      (E ∩ ({l | |slope l - c| ≤ Δ + D} ×ˢ univ)) := by
  classical
  letI : IsProbabilityMeasure scalarUnitTime := scalarUnitTime_probability
  have hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun q hq => ⟨mem_univ _, (hEsub hq).2⟩
  obtain ⟨A, hA, hAdata, hAfloor, hloss⟩ := prepare_long_original_cells ν hE hunit hcode J hcover
    (m := ENNReal.ofReal m) (ENNReal.ofReal_pos.mpr hτ)
  let E₂ := E ∩ (A ×ˢ univ)
  have hE₂ : MeasurableSet E₂ := hE.inter (hA.prod MeasurableSet.univ)
  have hunit₂ : E₂ ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun q hq => hunit hq.1
  have hA₀ : A ⊆ A₀ := by
    intro l hl
    have hpos : 0 < volume (Prod.mk l ⁻¹' E) :=
      (ENNReal.ofReal_pos.mpr hτ).trans_le (hAdata l hl).2
    obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero (ne_of_gt hpos)
    exact (hEsub ht).1
  have hcost : ENNReal.ofReal τ * ν univ + ENNReal.ofReal m * (J.card : ENNReal) ≤
      ENNReal.ofReal (δ / 2) := by
    calc
      _ = ENNReal.ofReal (τ * ν.real univ) + ENNReal.ofReal (m * (J.card : ℝ)) := by
        simp only [Measure.real, ENNReal.ofReal_mul hτ.le, ENNReal.ofReal_mul hm.le,
          ENNReal.ofReal_toReal (measure_ne_top ν _), ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (τ * ν.real univ + m * (J.card : ℝ)) :=
        (ENNReal.ofReal_add (mul_nonneg hτ.le measureReal_nonneg)
          (mul_nonneg hm.le (Nat.cast_nonneg _))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbudget
  have hmass₂ : ENNReal.ofReal (δ / 2) ≤ (ν.prod volume) E₂ := by
    have htotal : ENNReal.ofReal δ ≤ (ν.prod volume) E₂ + ENNReal.ofReal (δ / 2) := by
      calc
        _ ≤ (ν.prod volume) E := ENNReal.ofReal_le_of_le_toReal hmass
        _ ≤ (ν.prod volume) E₂ + (ENNReal.ofReal τ * ν univ + ENNReal.ofReal m * J.card) :=
          by simpa only [add_assoc] using hloss
        _ ≤ _ := add_le_add le_rfl hcost
    have hsplit : ENNReal.ofReal δ = ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    rw [hsplit] at htotal
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top htotal
  have hmass₂real : δ / 2 ≤ (scalarUnitTime.prod ν).real (Prod.swap ⁻¹' E₂) := by
    rw [original_unit_time_swap_real ν hE₂ hunit₂]
    exact (ENNReal.ofReal_le_iff_le_toReal (original_unit_incidence_ne_top ν hE₂ hunit₂)).mp hmass₂
  have hsquare : (δ / 2) ^ 2 ≤ ((scalarUnitTime.prod ν).real (Prod.swap ⁻¹' E₂)) ^ 2 :=
    (sq_le_sq₀ (by positivity) measureReal_nonneg).mpr hmass₂real
  have hlong₂ : ∀ l ∈ A, ENNReal.ofReal τ ≤ volume (Prod.mk l ⁻¹' E₂) := by
    intro l hl
    have he : Prod.mk l ⁻¹' E₂ = Prod.mk l ⁻¹' E := by
      ext t
      simp only [E₂, mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true, hl, and_true]
    rw [he]
    exact (hAdata l hl).2
  have hfloor₂ : ∀ j ∈ J, (A ∩ code ⁻¹' {j}).Nonempty → m ≤ ν.real (A ∩ code ⁻¹' {j}) := by
    intro j hj hn
    rcases hAfloor j hj with he | hf
    · exact (hn.ne_empty he).elim
    · exact ((ENNReal.ofReal_lt_iff_lt_toReal hm.le (measure_ne_top ν _)).mp hf).le
  have hjoint₂ : ∀ t j, j ∈ J → ∀ b : ℤ,
      ν.real {l | (l, t) ∈ E₂ ∧ code l = j ∧ (⌊F (t, l) / p⌋ : ℤ) = b} ≤ C := by
    intro t j hj b
    have hsub : {l | (l, t) ∈ E₂ ∧ code l = j ∧ (⌊F (t, l) / p⌋ : ℤ) = b} ⊆
        {l | (l, t) ∈ E ∧ code l = j ∧ (⌊F (t, l) / p⌋ : ℤ) = b} :=
      fun l hl => ⟨hl.1.1, hl.2⟩
    exact (measureReal_mono hsub).trans (hjoint t j hj b)
  obtain ⟨c, hc⟩ := exists_original_heavy_residual_slope scalarUnitTime scalarUnitTime_le_volume ν
    hE₂ hA (fun q hq => ⟨hq.2.1, (hunit₂ hq).2⟩) hF a slope hslope hcode J
    (fun l hl => (hAdata l hl).1) hp hpR hCs hC hΔ hm hτ hη herr S hS
    (fun l t ht => hsupport l t ht.1) (fun l t ht => hfit l t ht.1) hlong₂ hfloor₂
    (fun l hl l' hl' he => hspread l (hA₀ hl) l' (hA₀ hl') he) hjoint₂ (hgap.trans_le hsquare)
  have hnew : MeasurableSet (E ∩ ({l | |slope l - c| ≤ Δ + D} ×ˢ univ)) :=
    hE.inter ((measurableSet_le (hslope.sub_const c).abs measurable_const).prod MeasurableSet.univ)
  refine ⟨c, hc.trans_le (measureReal_mono ?_ (original_unit_incidence_ne_top ν hnew ?_))⟩
  · intro q hq
    exact ⟨hq.1.1, hq.2.1.2, mem_univ _⟩
  · intro q hq
    exact hunit hq.1

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
