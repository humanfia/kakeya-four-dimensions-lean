/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarLongCells.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarLongCells.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.Pruning
import Submission.Obl.k4_initial_horizon_bound.Duration

/-! Preparing long original trajectories and heavy tangential cells. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_initial_horizon_bound
open scoped ENNReal

/-- Both deletions keep or discard an entire trajectory. Thus the original
duration floor survives the later original-prior cell pruning. -/
theorem prepare_long_original_cells {Λ ι : Type*}
    [MeasurableSpace Λ] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure Λ) [IsFiniteMeasure ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {code : Λ → ι} (hcode : Measurable code) (K : Finset ι)
    (hcover : ∀ l t, (l, t) ∈ E → code l ∈ K)
    {τ m : ENNReal} (hτ : 0 < τ) :
    ∃ A : Set Λ, MeasurableSet A ∧
      (∀ l ∈ A, code l ∈ K ∧ τ ≤ volume (Prod.mk l ⁻¹' E)) ∧
      (∀ k ∈ K, A ∩ code ⁻¹' {k} = ∅ ∨ m < ν (A ∩ code ⁻¹' {k})) ∧
      (ν.prod volume) E ≤ (ν.prod volume) (E ∩ (A ×ˢ univ)) +
        τ * ν univ + m * (K.card : ENNReal) := by
  classical
  let A₁ : Set Λ := {l | τ ≤ incidenceDuration E l}
  have hA₁ : MeasurableSet A₁ := measurableSet_le measurable_const (measurable_incidenceDuration hE)
  obtain ⟨A, hA, hsub, hloss, hfloor⟩ := exists_measurable_current_floor_pruning ν
    (fun k : K => code ⁻¹' {k.val}) (fun _ => m)
    (fun k => hcode (MeasurableSet.singleton k.val)) hA₁
  have hLoss : ν (A₁ \ A) ≤ m * (K.card : ENNReal) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_comm] using hloss
  let W := ν.withDensity (incidenceDuration E)
  have hWdiff : W (A₁ \ A) ≤ ν (A₁ \ A) := by
    rw [withDensity_apply _ (hA₁.diff hA)]
    calc
      _ ≤ ∫⁻ _l in A₁ \ A, (1 : ENNReal) ∂ν :=
        setLIntegral_mono' (hA₁.diff hA) (fun l _ => incidenceDuration_le_one hunit l)
      _ = ν (A₁ \ A) := by simp
  have hWshort : W A₁ᶜ ≤ τ * ν univ := by
    have h := short_duration_mass_le ν hE τ
    simpa only [W, A₁, compl_setOf, not_le] using h
  have hmass : W univ ≤ W A + τ * ν univ + m * (K.card : ENNReal) := by
    have hcov : univ ⊆ (A ∪ (A₁ \ A)) ∪ A₁ᶜ := by
      intro l _
      by_cases hl₁ : l ∈ A₁
      · by_cases hl : l ∈ A
        · exact Or.inl (Or.inl hl)
        · exact Or.inl (Or.inr ⟨hl₁, hl⟩)
      · exact Or.inr hl₁
    calc
      _ ≤ W ((A ∪ (A₁ \ A)) ∪ A₁ᶜ) := measure_mono hcov
      _ ≤ W (A ∪ (A₁ \ A)) + W A₁ᶜ := measure_union_le _ _
      _ ≤ (W A + W (A₁ \ A)) + W A₁ᶜ := add_le_add (measure_union_le _ _) le_rfl
      _ ≤ (W A + m * (K.card : ENNReal)) + τ * ν univ :=
        add_le_add (add_le_add le_rfl (hWdiff.trans hLoss)) hWshort
      _ = _ := by ac_rfl
  have hWuniv : W univ = (ν.prod volume) E := by
    simpa only [univ_prod_univ, inter_univ] using
      duration_withDensity_apply ν hE MeasurableSet.univ
  have hWA : W A = (ν.prod volume) (E ∩ (A ×ˢ univ)) := duration_withDensity_apply ν hE hA
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · intro l hl
    have hdur : τ ≤ volume (Prod.mk l ⁻¹' E) := hsub hl
    have hpos : 0 < volume (Prod.mk l ⁻¹' E) := hτ.trans_le hdur
    obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero (ne_of_gt hpos)
    exact ⟨hcover l t ht, hdur⟩
  · intro k hk
    exact hfloor ⟨k, hk⟩
  · rwa [hWuniv, hWA] at hmass

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
