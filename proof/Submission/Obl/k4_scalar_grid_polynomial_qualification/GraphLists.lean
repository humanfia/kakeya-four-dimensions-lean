import Submission.Obl.k4_scalar_grid_polynomial_qualification.GraphSelection
import Submission.Obl.k4_scalar_grid_polynomial_qualification.SpatialCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

noncomputable section

def positiveRowValues {X Q : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure X) (key : X → Q) (f : X → Fin n → ℝ) (s : ℝ) (q : Q) : Set (Fin n → ℤ) :=
  {v | μ {p | key p = q ∧ cell s (f p) = v} ≠ 0}

/-- Every positive row bin is in the explicit bounded integer box. -/
theorem positiveRowValues_subset_cube {X Q : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure X) (key : X → Q) (f : X → Fin n → ℝ)
    {s H : ℝ} (hs : 0 < s) (hbound : ∀ᵐ p ∂μ, ∀ j, |f p j| ≤ H) (q : Q) :
    positiveRowValues μ key f s q ⊆ (↑(cubeIndices s (2 * H) (fun _ : Fin n => -H)) : Set (Fin n → ℤ)) := by
  classical
  intro v hv
  have hnull : μ ({p | ∀ j, |f p j| ≤ H})ᶜ = 0 := by
    have heq : ({p | ∀ j, |f p j| ≤ H} : Set X)ᶜ = {p | ¬∀ j, |f p j| ≤ H} := by
      ext p
      simp only [mem_compl_iff, mem_ofPred_eq]
    rw [heq]
    exact ae_iff.mp hbound
  have hpos : μ ({p | key p = q ∧ cell s (f p) = v} ∩ {p | ∀ j, |f p j| ≤ H}) ≠ 0 := by
    rw [measure_inter_conull hnull]
    exact hv
  obtain ⟨p, hp, hpb⟩ := nonempty_of_measure_ne_zero hpos
  apply Fintype.mem_piFinset.mpr
  intro j
  have hj : ⌊f p j / s⌋ = v j := congr_fun hp.2 j
  change v j ∈ Finset.Icc ⌊-H / s⌋ ⌊(-H + 2 * H) / s⌋
  rw [show -H + 2 * H = H by ring, ← hj]
  have hbj := abs_le.mp (hpb j)
  exact Finset.mem_Icc.mpr
    ⟨Int.floor_mono (div_le_div_of_nonneg_right hbj.1 hs.le),
      Int.floor_mono (div_le_div_of_nonneg_right hbj.2 hs.le)⟩

/-- Boundedness proves finiteness of the actual positive-mass row list,
so the frozen `ncard` bound is applied to a finite set. -/
theorem finite_positiveRowValues {X Q : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure X) (key : X → Q) (f : X → Fin n → ℝ)
    {s H : ℝ} (hs : 0 < s) (hbound : ∀ᵐ p ∂μ, ∀ j, |f p j| ≤ H) (q : Q) :
    (positiveRowValues μ key f s q).Finite :=
  (Finset.finite_toSet _).subset (positiveRowValues_subset_cube μ key f hs hbound q)

/-- The coarsest row reading needs only boundedness, without a graph-list
hypothesis at exponent zero. -/
theorem original_row_count_of_bound {X Q : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure X) (key : X → Q) (f : X → Fin n → ℝ)
    {s H : ℝ} (hs : 0 < s) (hH : 0 ≤ H)
    (hbound : ∀ᵐ p ∂μ, ∀ j, |f p j| ≤ H) (q : Q) :
    ((positiveRowValues μ key f s q).ncard : ℝ) ≤ (2 * H / s + 2) ^ n := by
  have hsub := positiveRowValues_subset_cube μ key f hs hbound q
  have hc : (positiveRowValues μ key f s q).ncard ≤
      (cubeIndices s (2 * H) (fun _ : Fin n => -H)).card := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  have he : ((positiveRowValues μ key f s q).ncard : ENNReal) ≤
      ENNReal.ofReal ((2 * H / s + 2) ^ n) :=
    (Nat.cast_le.mpr hc).trans (card_cubeIndices hs (by positivity) _)
  have hr := ENNReal.toReal_mono (by finiteness) he
  simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * H / s + 2) ^ n)] using hr

/-- Read the frozen positive-mass count as a genuine finite row list. -/
theorem exists_original_row_list {X Q : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure X) (key : X → Q) (f : X → Fin n → ℝ)
    {s H : ℝ} (hs : 0 < s) (hbound : ∀ᵐ p ∂μ, ∀ j, |f p j| ≤ H) (q : Q)
    (hcount : ((positiveRowValues μ key f s q).ncard : ℝ) ≤ H) :
    ∃ F : Finset (Fin n → ℤ), F.card ≤ ⌈H⌉₊ ∧
      ∀ v, μ {p | key p = q ∧ cell s (f p) = v} ≠ 0 → v ∈ F := by
  classical
  have hfin := finite_positiveRowValues μ key f hs hbound q
  refine ⟨hfin.toFinset, ?_, fun v hv => hfin.mem_toFinset.mpr hv⟩
  rw [Set.ncard_eq_toFinset_card _ hfin] at hcount
  exact_mod_cast hcount.trans (Nat.le_ceil H)

/-- The common positive record core turns all the selected lists into
pointwise lists on one conull set of original incidences. -/
theorem row_list_on_positive_core {X Q I : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure X) (key : I → X → Q) (f : X → Fin n → ℝ) (s : I → ℝ)
    (F : I → Q → Finset (Fin n → ℤ))
    (hF : ∀ i q v, μ {p | key i p = q ∧ cell (s i) (f p) = v} ≠ 0 → v ∈ F i q)
    (p : X)
    (hp : p ∈ positiveRecordCore μ (fun i p => (key i p, cell (s i) (f p)))) :
    ∀ i, cell (s i) (f p) ∈ F i (key i p) := by
  intro i
  apply hF i (key i p) (cell (s i) (f p))
  have h := hp i
  simpa only [Set.preimage, mem_singleton_iff, Prod.mk.injEq] using h

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification
