/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarTimeRecovery.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarTimeRecovery.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Recovering original labels after a common time fit

A temporary scalar group is used only to find fitting times. The conclusions
below restore all original labels at those times and use their instantaneous
mass floor. The trajectory prior is fixed throughout.
-/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set MeasureTheory
open scoped ENNReal

/-- An instantaneous floor pays for retaining all the original labels on a
measurable set of fitting times. The measure is the original prior times time. -/
theorem incidence_mass_of_time_floor {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] {E : Set (α × ℝ)} (hE : MeasurableSet E)
    {U : Set ℝ} (hU : MeasurableSet U) (τ : ℝ≥0∞)
    (hfloor : ∀ t ∈ U, τ ≤ ν {l | (l, t) ∈ E}) :
    τ * volume U ≤ (ν.prod volume) (E ∩ (univ ×ˢ U)) := by
  rw [Measure.prod_apply_symm (hE.inter
    ((MeasurableSet.univ : MeasurableSet (univ : Set α)).prod hU))]
  rw [← lintegral_indicator_const hU τ]
  apply lintegral_mono
  intro t
  by_cases ht : t ∈ U
  · rw [Set.indicator_of_mem ht]
    change τ ≤ ν ((fun x : α => (x, t)) ⁻¹' (E ∩ (univ ×ˢ U)))
    have hsect : (fun x : α => (x, t)) ⁻¹' (E ∩ (univ ×ˢ U)) = {l | (l, t) ∈ E} := by
      ext l
      simp [ht]
    rw [hsect]
    exact hfloor t ht
  · simp [ht]

/-- A common time restriction restores every original label. Its mass is
paid for by the original instantaneous floor and the disjoint active lengths. -/
theorem original_active_time_union {α ι : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (K : Finset ι) (V : ι → Set ℝ) {ell τ : ℝ} (hτ : 0 ≤ τ)
    (hVm : ∀ k ∈ K, MeasurableSet (V k))
    (hdisj : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (V i) (V j))
    (hlength : ∀ k ∈ K, ENNReal.ofReal ell ≤ volume (V k))
    (hfloor : ∀ k ∈ K, ∀ u ∈ V k, ENNReal.ofReal τ ≤ ν {l | (l, u) ∈ E}) :
    ∃ U : Set ℝ, U = ⋃ k ∈ K, V k ∧ MeasurableSet U ∧
      ENNReal.ofReal ((K.card : ℝ) * ell) ≤ volume U ∧
      ENNReal.ofReal (τ * (K.card : ℝ) * ell) ≤ (ν.prod volume) (E ∩ (univ ×ˢ U)) := by
  classical
  let U : Set ℝ := ⋃ k ∈ K, V k
  have hUm : MeasurableSet U :=
    K.measurableSet_biUnion (fun k hk => hVm k hk)
  have hlengthU : ENNReal.ofReal ((K.card : ℝ) * ell) ≤ volume U := by
    change ENNReal.ofReal ((K.card : ℝ) * ell) ≤ volume (⋃ k ∈ K, V k)
    rw [measure_biUnion_finset hdisj hVm]
    calc
      ENNReal.ofReal ((K.card : ℝ) * ell) = ∑ _k ∈ K, ENNReal.ofReal ell := by
        simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
      _ ≤ ∑ k ∈ K, volume (V k) := Finset.sum_le_sum fun k hk => hlength k hk
  have hinst : ∀ u ∈ U, ENNReal.ofReal τ ≤ ν {l | (l, u) ∈ E} := by
    intro u hu
    obtain ⟨k, hk, huk⟩ := mem_iUnion₂.mp hu
    exact hfloor k hk u huk
  have hmass : ENNReal.ofReal (τ * (K.card : ℝ) * ell) ≤
      (ν.prod volume) (E ∩ (univ ×ˢ U)) := by
    calc
      ENNReal.ofReal (τ * (K.card : ℝ) * ell) =
          ENNReal.ofReal τ * ENNReal.ofReal ((K.card : ℝ) * ell) := by
        rw [← ENNReal.ofReal_mul hτ]
        congr 1
        ring
      _ ≤ ENNReal.ofReal τ * volume U := mul_le_mul_right hlengthU _
      _ ≤ (ν.prod volume) (E ∩ (univ ×ˢ U)) := incidence_mass_of_time_floor ν hE hUm _ hinst
  exact ⟨U, rfl, hUm, hlengthU, hmass⟩

/-- Many disjoint active pieces of time cells carry a common affine fit and
original incidence mass. Only the active subsets of the cells are restored. -/
theorem active_cell_fit_recovery {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (K : Finset ℤ) (V : ℤ → Set ℝ) (t : ℤ → ℝ) (f : ℝ → ℝ)
    (a v ell τ δ A err : ℝ) (_hell : 0 ≤ ell) (hτ : 0 ≤ τ)
    (hVm : ∀ k ∈ K, MeasurableSet (V k))
    (hdisj : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (V i) (V j))
    (hlength : ∀ k ∈ K, ENNReal.ofReal ell ≤ volume (V k))
    (hfloor : ∀ k ∈ K, ∀ u ∈ V k, ENNReal.ofReal τ ≤ ν {l | (l, u) ∈ E})
    (hanchor : ∀ k ∈ K, |f (t k) - (a + v * t k)| ≤ err)
    (hnear : ∀ k ∈ K, ∀ u ∈ V k, |u - t k| ≤ δ ∧ |f u - f (t k)| ≤ A * δ) :
    ∃ U : Set ℝ, U = ⋃ k ∈ K, V k ∧ MeasurableSet U ∧
      ENNReal.ofReal ((K.card : ℝ) * ell) ≤ volume U ∧
      ENNReal.ofReal (τ * (K.card : ℝ) * ell) ≤
        (ν.prod volume) (E ∩ (univ ×ˢ U)) ∧
      ∀ u ∈ U, |f u - (a + v * u)| ≤ err + (A + |v|) * δ := by
  obtain ⟨U, hUeq, hUm, hlengthU, hmass⟩ :=
    original_active_time_union ν hE K V hτ hVm hdisj hlength hfloor
  refine ⟨U, hUeq, hUm, hlengthU, hmass, ?_⟩
  intro u hu
  rw [hUeq] at hu
  obtain ⟨k, hk, huk⟩ := mem_iUnion₂.mp hu
  obtain ⟨ht, hft⟩ := hnear k hk u huk
  have hvt : |v * (t k - u)| ≤ |v| * δ := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  calc
    |f u - (a + v * u)| =
        |(f u - f (t k)) + (f (t k) - (a + v * t k)) + v * (t k - u)| := by
      congr 1
      ring
    _ ≤ |f u - f (t k)| + |f (t k) - (a + v * t k)| + |v * (t k - u)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ err + (A + |v|) * δ := by linarith [hanchor k hk]

/-- Removing all labels at times with small instantaneous mass costs at most
the chosen threshold. The retained time set is common to every trajectory. -/
theorem prepare_time_floor {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (hEs : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (τ : ℝ) :
    ∃ S : Set ℝ, MeasurableSet S ∧ S ⊆ Icc (0 : ℝ) 1 ∧
      (∀ t ∈ S, ENNReal.ofReal τ ≤ ν {l | (l, t) ∈ E}) ∧
      (ν.prod volume) E ≤ (ν.prod volume) (E ∩ (univ ×ˢ S)) + ENNReal.ofReal τ := by
  classical
  let m : ℝ → ℝ≥0∞ := fun t => ν ((fun l : α => (l, t)) ⁻¹' E)
  have hmm : Measurable m := measurable_measure_prodMk_right hE
  let S : Set ℝ := Icc (0 : ℝ) 1 ∩ {t | ENNReal.ofReal τ ≤ m t}
  have hSm : MeasurableSet S := measurableSet_Icc.inter
    (measurableSet_le measurable_const hmm)
  have hprodSm : MeasurableSet ((univ : Set α) ×ˢ S) := MeasurableSet.univ.prod hSm
  let B : Set (α × ℝ) := E \ (univ ×ˢ S)
  have hBm : MeasurableSet B := hE.diff hprodSm
  have hpoint : ∀ t : ℝ, ν ((fun l : α => (l, t)) ⁻¹' B) ≤
      (Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal τ) t := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht]
      by_cases hmt : ENNReal.ofReal τ ≤ m t
      · have he : (fun l : α => (l, t)) ⁻¹' B = ∅ := by
          ext l
          simp only [B, mem_preimage, mem_sdiff, mem_prod, mem_univ,
            S, mem_inter_iff, mem_ofPred_eq, ht, hmt, and_self, not_true_eq_false,
            and_false, mem_empty_iff_false]
        rw [he, measure_empty]
        exact bot_le
      · exact (measure_mono (Set.preimage_mono (sdiff_subset : B ⊆ E))).trans
          (le_of_lt (lt_of_not_ge hmt))
    · rw [Set.indicator_of_notMem ht]
      have he : (fun l : α => (l, t)) ⁻¹' B = ∅ := by
        ext l
        constructor
        · intro hl
          exact (ht (hEs hl.1).2).elim
        · exact False.elim
      rw [he, measure_empty]
  have hbad : (ν.prod volume) B ≤ ENNReal.ofReal τ := by
    rw [Measure.prod_apply_symm hBm]
    calc
      _ ≤ ∫⁻ t : ℝ, (Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal τ) t :=
        lintegral_mono hpoint
      _ = ENNReal.ofReal τ := by
        rw [lintegral_indicator_const measurableSet_Icc]
        simp
  refine ⟨S, hSm, inter_subset_left, fun t ht => ht.2, ?_⟩
  calc
    (ν.prod volume) E = (ν.prod volume) (E ∩ (univ ×ˢ S)) + (ν.prod volume) B :=
      (measure_inter_add_sdiff E hprodSm).symm
    _ ≤ _ := add_le_add le_rfl hbad

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
