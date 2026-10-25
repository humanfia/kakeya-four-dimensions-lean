/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/RecordSupport.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.Atoms
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.IntegerWindows
import Submission.Obl.k4_native_grid_profile_extension.Labels

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

abbrev Record (J : ℕ) := Fin J × (ℤ × ℤ × ℤ)
abbrev Canonical := Base × (ℤ × ℤ)
abbrev canonicalReference : Measure Canonical := volume.prod Measure.count

abbrev baseRectangle (A B : Set ℝ) : Set Base := {v | v 0 ∈ A ∧ v 1 ∈ B}

theorem measurable_baseRectangle {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) : MeasurableSet (baseRectangle A B) :=
  (hA.preimage (measurable_pi_apply 0)).inter (hB.preimage (measurable_pi_apply 1))

theorem volume_baseRectangle {A B : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    volume (baseRectangle A B) = volume A * volume B := by
  have h := Measure.map_apply (μ := (volume : Measure Base))
    (MeasurableEquiv.finTwoArrow : Base ≃ᵐ ℝ × ℝ).measurable (hA.prod hB)
  rw [(volume_preserving_finTwoArrow ℝ).map_eq, Measure.volume_eq_prod, Measure.prod_prod] at h
  exact h.symm

abbrev recordBase {J : ℕ} (σ R : ℝ) (c : Record J) : Set Base :=
  baseRectangle (cell J c.1)
    (Icc (σ * (c.2.1 : ℝ) - (R + 1) * σ) (σ * (c.2.1 : ℝ) + (R + 1) * σ))

abbrev recordSupport {J : ℕ} (σ ρ q R : ℝ) (c : Record J) : Set Canonical :=
  recordBase σ R c ×ˢ (integerWindow 1 (c.2.2.1 : ℝ) (R + 2) ×ˢ
    integerWindow ρ (q * (c.2.2.2 : ℝ)) (3 * q))

theorem measurable_recordSupport {J : ℕ} (σ ρ q R : ℝ) (c : Record J) :
    MeasurableSet (recordSupport σ ρ q R c) := by
  have hw (a b r : ℝ) : MeasurableSet (integerWindow a b r) :=
    measurableSet_le (by fun_prop) measurable_const
  exact (measurable_baseRectangle measurableSet_Ico measurableSet_Icc).prod
    ((hw _ _ _).prod (hw _ _ _))

/-- The reference volume of a record support has the expected noisy cell size.
The factor `q / ρ` counts the fine velocity bins lying in one coarse noise bin. -/
theorem recordSupport_volume {J : ℕ} (hJ : 0 < J) {σ ρ q R : ℝ}
    (hσ : 0 < σ) (hρ : 0 < ρ) (hq : ρ ≤ q) (hR : 0 ≤ R) (c : Record J) :
    canonicalReference (recordSupport σ ρ q R c) ≤
      ENNReal.ofReal (52 * (R + 1) * (8 * R + 18) * σ / (J : ℝ) * (q / ρ)) := by
  have hq0 : 0 < q := hρ.trans_le hq
  have hqratio : 1 ≤ q / ρ := (le_div_iff₀ hρ).mpr (by simpa using hq)
  have hh := integerWindow_count_le (c := (c.2.2.1 : ℝ)) (a := 1)
    (by norm_num) (show 0 ≤ R + 2 by linarith)
  have hv := integerWindow_count_le (c := q * (c.2.2.2 : ℝ)) hρ
    (show 0 ≤ 3 * q by positivity)
  have hv' : Measure.count (integerWindow ρ (q * (c.2.2.2 : ℝ)) (3 * q)) ≤
      ENNReal.ofReal (26 * (q / ρ)) := by
    refine hv.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      8 * (3 * q) / ρ + 2 = 24 * (q / ρ) + 2 := by ring
      _ ≤ 26 * (q / ρ) := by linarith
  rw [recordSupport, canonicalReference,
    ← Submission.Obl.k4_native_grid_profile_extension.count_prod_eq,
    Measure.prod_prod, Measure.prod_prod, volume_baseRectangle measurableSet_Ico measurableSet_Icc,
    cell_volume hJ, Real.volume_Icc]
  have hwidth : σ * (c.2.1 : ℝ) + (R + 1) * σ -
      (σ * (c.2.1 : ℝ) - (R + 1) * σ) = 2 * (R + 1) * σ := by ring
  rw [hwidth]
  have hh' : Measure.count (integerWindow 1 (c.2.2.1 : ℝ) (R + 2)) ≤
      ENNReal.ofReal (8 * R + 18) := by convert hh using 1 <;> ring
  calc
    _ ≤ (ENNReal.ofReal ((J : ℝ)⁻¹) * ENNReal.ofReal (2 * (R + 1) * σ)) *
        (ENNReal.ofReal (8 * R + 18) * ENNReal.ofReal (26 * (q / ρ))) := by
      exact mul_le_mul' le_rfl (mul_le_mul' hh' hv')
    _ = _ := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg J)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * R + 18),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (J : ℝ)⁻¹ * (2 * (R + 1) * σ))]
      congr 1
      ring

/-- Distinct time-cell records at one time inject into their three integer
coordinates. This reduces overlap counting to three scalar windows. -/
theorem record_card_le_product {J : ℕ} (hJ : 0 < J) (t : ℝ)
    (W : Finset (Record J)) {A B C : Set ℤ} (hA : A.Finite) (hB : B.Finite) (hC : C.Finite)
    (ht : ∀ c ∈ W, t ∈ cell J c.1)
    (hcoord : ∀ c ∈ W, c.2.1 ∈ A ∧ c.2.2.1 ∈ B ∧ c.2.2.2 ∈ C) :
    W.card ≤ hA.toFinset.card * (hB.toFinset.card * hC.toFinset.card) := by
  classical
  let L := hA.toFinset ×ˢ (hB.toFinset ×ˢ hC.toFinset)
  have hmap : ∀ c ∈ W, c.2 ∈ L := by
    intro c hc
    simpa only [L, Finset.mem_product, Set.Finite.mem_toFinset] using hcoord c hc
  have hinj : Set.InjOn (fun c : Record J => c.2) (W : Set (Record J)) := by
    intro c hc d hd hcd
    have htime : c.1 = d.1 := by
      by_contra hne
      exact (Set.disjoint_left.mp (cell_disjoint hJ hne)) (ht c hc) (ht d hd)
    exact Prod.ext htime hcd
  simpa only [L, Finset.card_product] using Finset.card_le_card_of_injOn _ hmap hinj

/-- Integer record coordinates meeting a fixed observation form a polynomial
size list, independently of the fine slope depth. -/
theorem recordSupport_overlap {J : ℕ} (hJ : 0 < J) {σ ρ q R : ℝ}
    (hσ : 0 < σ) (hρ : 0 < ρ) (hq : 0 < q) (hR : 0 ≤ R)
    (W : Finset (Record J)) (p : Canonical)
    (hW : ∀ c ∈ W, p ∈ recordSupport σ ρ q R c) :
    (W.card : ℝ) ≤ 26 * (8 * R + 10) * (8 * R + 18) := by
  classical
  by_cases hne : W.Nonempty
  · obtain ⟨c₀, hc₀⟩ := hne
    have ht₀ := (hW c₀ hc₀).1.1
    let A := integerWindow σ (p.1 1) ((R + 1) * σ)
    let B := integerWindow 1 (p.2.1 : ℝ) (R + 2)
    let C := integerWindow q (ρ * (p.2.2 : ℝ)) (3 * q)
    obtain ⟨hAf, hAc⟩ := integerWindow_finite_card (c := p.1 1) hσ
      (show 0 ≤ (R + 1) * σ by positivity)
    obtain ⟨hBf, hBc⟩ := integerWindow_finite_card (c := (p.2.1 : ℝ))
      (a := 1) (by norm_num) (show 0 ≤ R + 2 by linarith)
    obtain ⟨hCf, hCc⟩ := integerWindow_finite_card (c := ρ * (p.2.2 : ℝ)) hq
      (show 0 ≤ 3 * q by positivity)
    let L : Finset (ℤ × ℤ × ℤ) := hAf.toFinset ×ˢ (hBf.toFinset ×ˢ hCf.toFinset)
    have hmap : ∀ c ∈ W, c.2 ∈ L := by
      intro c hc
      have hp := hW c hc
      simp only [L, Finset.mem_product, Set.Finite.mem_toFinset]
      constructor
      · change |σ * (c.2.1 : ℝ) - p.1 1| ≤ (R + 1) * σ
        rw [abs_sub_comm]
        exact abs_le.mpr ⟨by linarith [hp.1.2.1], by linarith [hp.1.2.2]⟩
      · constructor
        · change |1 * (c.2.2.1 : ℝ) - (p.2.1 : ℝ)| ≤ R + 2
          simpa only [integerWindow, mem_ofPred_eq, one_mul, abs_sub_comm] using hp.2.1
        · change |q * (c.2.2.2 : ℝ) - ρ * (p.2.2 : ℝ)| ≤ 3 * q
          simpa only [integerWindow, mem_ofPred_eq, abs_sub_comm] using hp.2.2
    have hinj : Set.InjOn (fun c : Record J => c.2) (W : Set (Record J)) := by
      intro c hc d hd hcd
      have htime : c.1 = d.1 := by
        by_contra hne
        exact (Set.disjoint_left.mp (cell_disjoint hJ hne)) (hW c hc).1.1 (hW d hd).1.1
      exact Prod.ext htime hcd
    have hcard : W.card ≤ L.card := Finset.card_le_card_of_injOn _ hmap hinj
    have ha : (hAf.toFinset.card : ℝ) ≤ 8 * R + 10 := by
      rw [← Set.ncard_eq_toFinset_card _ hAf]
      refine hAc.trans_eq ?_
      field_simp [hσ.ne', hq.ne']
      ring
    have hb : (hBf.toFinset.card : ℝ) ≤ 8 * R + 18 := by
      rw [← Set.ncard_eq_toFinset_card _ hBf]
      convert hBc using 1 <;> ring
    have hc : (hCf.toFinset.card : ℝ) ≤ 26 := by
      rw [← Set.ncard_eq_toFinset_card _ hCf]
      refine hCc.trans_eq ?_
      field_simp [hσ.ne', hq.ne']
      ring
    calc
      _ ≤ (L.card : ℝ) := by exact_mod_cast hcard
      _ = (hAf.toFinset.card : ℝ) * ((hBf.toFinset.card : ℝ) * (hCf.toFinset.card : ℝ)) := by
        simp only [L, Finset.card_product, Nat.cast_mul]
      _ ≤ (8 * R + 10) * ((8 * R + 18) * 26) := by gcongr
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
