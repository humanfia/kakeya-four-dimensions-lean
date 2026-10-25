/- Adapted within this LOT tree from o190/x0630, commit adb2f45f4ccde121d91c5954051b6c45263cd6de,
Submission/Obl/k4_pair_bin_atlas_assembly/TimeFreezing.lean. Existing provenance comments are retained below. -/
import Mathlib
import Submission.Obl.k4_paired_full_time_binning.TimeSelection

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

open MeasureTheory Set
open scoped ENNReal

def pairSection {X : Type} (H : Set (X × (ℝ × ℝ))) (t : ℝ) : Set (X × ℝ) :=
  {p | (p.1, (t, p.2)) ∈ H}

theorem measurableSet_pairSection {X : Type} [MeasurableSpace X]
    {H : Set (X × (ℝ × ℝ))} (hH : MeasurableSet H) (t : ℝ) :
    MeasurableSet (pairSection H t) := hH.preimage (by fun_prop)

theorem measurable_pairSection_mass {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {H : Set (X × (ℝ × ℝ))}
    (hH : MeasurableSet H) :
    Measurable (fun t => (ν.prod volume) (pairSection H t)) := by
  have hh : MeasurableSet {p : ℝ × (X × ℝ) | (p.2.1, (p.1, p.2.2)) ∈ H} :=
    hH.preimage (by fun_prop)
  exact measurable_measure_prodMk_left hh

/-- Freeze a common source time for a finite collection of original pair laws
on one block. The reciprocal block length is exactly the original pairing
normalization. -/
theorem exists_frozen_pair_time {X : Type} {ι : Type*}
    [MeasurableSpace X] [Fintype ι]
    (ν : ι → Measure X) [∀ i, SFinite (ν i)]
    (H : ι → Set (X × (ℝ × ℝ))) (hH : ∀ i, MeasurableSet (H i))
    (hfinite : ∀ i, (ν i |>.prod (volume.prod volume)) (H i) ≠ ∞)
    (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≠ ∞)
    (I : Set ℝ) (hI : MeasurableSet I) (hI0 : volume I ≠ 0) (hItop : volume I ≠ ∞)
    (hsupp : ∀ i p, p ∈ H i → p.2.1 ∈ I) :
    ∃ t ∈ I, (volume I)⁻¹ * (∑ i, w i * (ν i |>.prod (volume.prod volume)) (H i)) ≤
      ∑ i, w i * ((ν i).prod volume) (pairSection (H i) t) := by
  classical
  let π : Measure ℝ := ProbabilityTheory.cond volume I
  letI : IsProbabilityMeasure π :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hI0 hItop
  let mass : ℝ → ℝ≥0∞ :=
    fun t => ∑ i, w i * ((ν i).prod volume) (pairSection (H i) t)
  have hm (i : ι) := measurable_pairSection_mass (ν i) (hH i)
  have havg : (∫⁻ t, mass t) =
      ∑ i, w i * (ν i |>.prod (volume.prod volume)) (H i) := by
    dsimp only [mass]
    rw [lintegral_finsetSum Finset.univ (fun i _ => (hm i).const_mul (w i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [lintegral_const_mul _ (hm i)]
    congr 1
    exact (Submission.Obl.k4_paired_full_time_binning.pair_fubini (ν i) (hH i)).symm
  have hs (t : ℝ) (ht : t ∉ I) : mass t = 0 := by
    dsimp only [mass]
    apply Finset.sum_eq_zero
    intro i _
    have hh : pairSection (H i) t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact ht (hsupp i (p.1, (t, p.2)) hp)
    rw [hh, measure_empty, mul_zero]
  have hind : I.indicator mass = mass := by
    funext t
    by_cases ht : t ∈ I
    · exact indicator_of_mem ht _
    · rw [indicator_of_notMem ht, hs t ht]
  have havgπ : (∫⁻ t, mass t ∂π) =
      (volume I)⁻¹ * (∑ i, w i * (ν i |>.prod (volume.prod volume)) (H i)) := by
    dsimp only [π]
    rw [ProbabilityTheory.cond, lintegral_smul_measure,
      ← lintegral_indicator hI, hind, havg]
    rfl
  have hf : (∫⁻ t, mass t ∂π) ≠ ∞ := by
    rw [havgπ]
    apply ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hI0)
    exact ENNReal.sum_ne_top.mpr fun i _ => ENNReal.mul_ne_top (hw i) (hfinite i)
  have hnull : π Iᶜ = 0 := by
    dsimp only [π]
    rw [ProbabilityTheory.cond_apply hI]
    simp
  obtain ⟨t, ht, htmass⟩ := exists_notMem_null_lintegral_le hf hnull
  refine ⟨t, by simpa using ht, ?_⟩
  rwa [havgπ] at htmass

/-- Source times are shared by every source with the same world/block
label, so disjoint source sections remain disjoint after freezing. -/
theorem exists_frozen_labeled_pair_times {X : Type} {ι Γ : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype Γ]
    (ν : ι → Measure X) [∀ i, SFinite (ν i)]
    (H : ι → Set (X × (ℝ × ℝ))) (hH : ∀ i, MeasurableSet (H i))
    (hfinite : ∀ i, (ν i |>.prod (volume.prod volume)) (H i) ≠ ∞)
    (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≠ ∞)
    (label : ι → Γ) (I : Γ → Set ℝ)
    (hI : ∀ g, MeasurableSet (I g))
    (hI0 : ∀ g, volume (I g) ≠ 0) (hItop : ∀ g, volume (I g) ≠ ∞)
    (hsupp : ∀ i p, p ∈ H i → p.2.1 ∈ I (label i)) :
    ∃ t : Γ → ℝ, (∀ g, t g ∈ I g) ∧
      (∑ i, (volume (I (label i)))⁻¹ *
        (w i * (ν i |>.prod (volume.prod volume)) (H i))) ≤
      ∑ i, w i * ((ν i).prod volume) (pairSection (H i) (t (label i))) := by
  classical
  let Hg : Γ → ι → Set (X × (ℝ × ℝ)) :=
    fun g i => if label i = g then H i else ∅
  have hHg (g : Γ) (i : ι) : MeasurableSet (Hg g i) := by
    dsimp only [Hg]
    split_ifs
    · exact hH i
    · exact MeasurableSet.empty
  have hfin (g : Γ) (i : ι) : (ν i |>.prod (volume.prod volume)) (Hg g i) ≠ ∞ := by
    dsimp only [Hg]
    split_ifs
    · exact hfinite i
    · simp
  have hsup (g : Γ) (i : ι) (p : X × (ℝ × ℝ)) (hp : p ∈ Hg g i) : p.2.1 ∈ I g := by
    dsimp only [Hg] at hp
    split_ifs at hp with hh
    · rw [← hh]
      exact hsupp i p hp
    · exact hp.elim
  choose t ht hm using fun g => exists_frozen_pair_time ν (Hg g) (hHg g)
    (hfin g) w hw (I g) (hI g) (hI0 g) (hItop g) (hsup g)
  refine ⟨t, ht, ?_⟩
  have hsec (g : Γ) (i : ι) (v : ℝ) : pairSection (Hg g i) v =
      if label i = g then pairSection (H i) v else ∅ := by
    dsimp only [Hg]
    split_ifs
    · rfl
    · ext p; simp [pairSection]
  calc
    _ = ∑ g, (volume (I g))⁻¹ *
        (∑ i, w i * (ν i |>.prod (volume.prod volume)) (Hg g i)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp [Hg, apply_ite]
    _ ≤ ∑ g, ∑ i, w i * ((ν i).prod volume) (pairSection (Hg g i) (t g)) :=
      Finset.sum_le_sum fun g _ => hm g
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [hsec]
      simp [apply_ite]

/-- The normalization of a dyadic source-time slice is exactly `2 ^ T`.
All worlds and frames with the same time index use the same frozen time. -/
theorem exists_frozen_dyadic_pair_times {X : Type} {ι : Type*}
    [MeasurableSpace X] [Fintype ι]
    (ν : ι → Measure X) [∀ i, SFinite (ν i)]
    (H : ι → Set (X × (ℝ × ℝ))) (hH : ∀ i, MeasurableSet (H i))
    (hfinite : ∀ i, (ν i |>.prod (volume.prod volume)) (H i) ≠ ∞)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (T : ℕ) (j : ι → Fin (2 ^ T))
    (hsupp : ∀ i p, p ∈ H i → p.2.1 ∈
      Icc ((j i : ℝ) / (2 : ℝ) ^ T) (((j i : ℝ) + 1) / (2 : ℝ) ^ T)) :
    ∃ t : Fin (2 ^ T) → ℝ,
      (∀ b : Fin (2 ^ T), t b ∈ Icc ((b : ℝ) / (2 : ℝ) ^ T) (((b : ℝ) + 1) / (2 : ℝ) ^ T)) ∧
      (∑ i, ENNReal.ofReal (w i * (2 : ℝ) ^ T) *
        (ν i |>.prod (volume.prod volume)) (H i)) ≤
      ∑ i, ENNReal.ofReal (w i) * ((ν i).prod volume) (pairSection (H i) (t (j i))) := by
  let q : ℝ := 2 ^ T
  have hq : 0 < q := by dsimp [q]; positivity
  let I : Fin (2 ^ T) → Set ℝ := fun b => Icc ((b : ℝ) / q) (((b : ℝ) + 1) / q)
  have hvol (b : Fin (2 ^ T)) : volume (I b) = ENNReal.ofReal q⁻¹ := by
    dsimp only [I]
    rw [Real.volume_Icc]
    congr 1
    ring
  have hnormalize (b : Fin (2 ^ T)) : (volume (I b))⁻¹ = ENNReal.ofReal q := by
    rw [hvol, ENNReal.ofReal_inv_of_pos hq, inv_inv]
  obtain ⟨t, ht, hm⟩ := exists_frozen_labeled_pair_times ν H hH hfinite
    (fun i => ENNReal.ofReal (w i)) (fun _ => ENNReal.ofReal_ne_top) j I
    (fun _ => measurableSet_Icc)
    (fun b => by rw [hvol]; exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hq))
    (fun b => by rw [hvol]; exact ENNReal.ofReal_ne_top) hsupp
  refine ⟨t, ht, ?_⟩
  simp_rw [hnormalize] at hm
  calc
    _ = ∑ i, ENNReal.ofReal q *
        (ENNReal.ofReal (w i) * (ν i |>.prod (volume.prod volume)) (H i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.ofReal_mul (hw i)]
      dsimp only [q]
      ac_rfl
    _ ≤ _ := hm

end Submission.Obl.k4_matched_pair_representative_realization.Selection
