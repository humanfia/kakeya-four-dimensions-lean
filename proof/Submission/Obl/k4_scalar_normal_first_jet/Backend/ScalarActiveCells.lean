/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarActiveCells.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarActiveCells.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.Pruning

/-! Selecting substantial active time cells before taking a planar graph
quadrant. All original labels at the selected times can then be restored. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open scoped ENNReal

theorem prepare_active_parameter_cells {Θ Λ ι : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Λ] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Θ) (ν : Measure Λ) [SFinite ν]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) {code : Θ → ι} (hcode : Measurable code)
    (K : Finset ι) (hcover : ∀ θ l, (θ, l) ∈ E → code θ ∈ K)
    (Q ell : ENNReal) (hcap : ∀ θ, ν (Prod.mk θ ⁻¹' E) ≤ Q) :
    ∃ U : Set Θ, MeasurableSet U ∧ U ⊆ {θ | 0 < ν (Prod.mk θ ⁻¹' E)} ∧
      (∀ θ ∈ U, code θ ∈ K) ∧
      (∀ k ∈ K, U ∩ code ⁻¹' {k} = ∅ ∨ ell < μ (U ∩ code ⁻¹' {k})) ∧
      (μ.prod ν) E ≤ (μ.prod ν) (E ∩ (U ×ˢ univ)) + Q * (ell * (K.card : ENNReal)) := by
  classical
  let s : Θ → ENNReal := fun θ => ν (Prod.mk θ ⁻¹' E)
  let A : Set Θ := {θ | 0 < s θ}
  have hs : Measurable s := measurable_measure_prodMk_left hE
  have hA : MeasurableSet A := measurableSet_lt measurable_const hs
  obtain ⟨U, hU, hsub, hloss, hfloor⟩ := exists_measurable_current_floor_pruning μ
    (fun k : K => code ⁻¹' {k.val}) (fun _ => ell)
    (fun k => hcode (MeasurableSet.singleton k.val)) hA
  have hUK : ∀ θ ∈ U, code θ ∈ K := by
    intro θ hθ
    have hpos := hsub hθ
    have hne : (Prod.mk θ ⁻¹' E).Nonempty := nonempty_of_measure_ne_zero (ne_of_gt hpos)
    obtain ⟨l, hl⟩ := hne
    exact hcover θ l hl
  have hLoss : μ (A \ U) ≤ ell * (K.card : ENNReal) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul, mul_comm] using hloss
  have hmeq : (μ.prod ν) (E ∩ (U ×ˢ univ)) = ∫⁻ θ, U.indicator s θ ∂μ := by
    rw [Measure.prod_apply (hE.inter (hU.prod MeasurableSet.univ))]
    apply lintegral_congr
    intro θ
    by_cases hθ : θ ∈ U
    · have heq : Prod.mk θ ⁻¹' (E ∩ (U ×ˢ univ)) = Prod.mk θ ⁻¹' E := by
        ext l
        simp [hθ]
      simp only [heq, indicator_of_mem hθ]
      rfl
    · have heq : Prod.mk θ ⁻¹' (E ∩ (U ×ˢ univ)) = ∅ := by
        ext l
        simp [hθ]
      simp only [heq, measure_empty, indicator_of_notMem hθ]
  have hpoint θ : s θ ≤ U.indicator s θ + (A \ U).indicator (fun _ => Q) θ := by
    by_cases hθU : θ ∈ U
    · simp only [indicator_of_mem hθU]
      exact le_add_of_nonneg_right zero_le
    · by_cases hθA : θ ∈ A
      · simp only [indicator_of_notMem hθU, indicator_of_mem (show θ ∈ A \ U from ⟨hθA, hθU⟩), zero_add]
        exact hcap θ
      · have hz : s θ = 0 := le_antisymm (not_lt.mp hθA) zero_le
        simp only [hz, zero_le]
  have hmass : (μ.prod ν) E ≤ (μ.prod ν) (E ∩ (U ×ˢ univ)) + Q * μ (A \ U) := by
    calc
      _ = ∫⁻ θ, s θ ∂μ := Measure.prod_apply hE
      _ ≤ ∫⁻ θ, U.indicator s θ + (A \ U).indicator (fun _ => Q) θ ∂μ := lintegral_mono hpoint
      _ = (∫⁻ θ, U.indicator s θ ∂μ) + ∫⁻ θ, (A \ U).indicator (fun _ => Q) θ ∂μ :=
        lintegral_add_left (hs.indicator hU) _
      _ = _ := by rw [← hmeq, lintegral_indicator_const (hA.diff hU) Q]
  refine ⟨U, hU, hsub, hUK, ?_, ?_⟩
  · intro k hk
    exact hfloor ⟨k, hk⟩
  · exact hmass.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hLoss zero_le))

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
