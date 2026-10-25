-- Adapted from this LOT tree, o114, session x0680, commit 8cc890dd,
-- Submission/Obl/k4_terminal_representative_atlas/Preparation/FiniteCaps.lean.
import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Set Filter
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- Finitely many fixed-depth exceptional bounds have one positive decay
exponent, by the accepted power-small addition theorem. -/
theorem powerSmall_finset_sum {ι : Type*} {N : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) (R : Finset ι) (f : ι → ℕ → ENNReal)
    (hf : ∀ i ∈ R, IsPowerSmall N (f i)) :
    IsPowerSmall N (fun k => ∑ i ∈ R, f i k) := by
  classical
  revert hf
  induction R using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, by norm_num, Eventually.of_forall (fun k => by simp)⟩
  | @insert i R hi ih =>
      intro hf
      have hrest := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i R)).add hN hrest

/-- A simultaneous measurable mask with the exact finite union bound under
the original measures and weights, before any asymptotic estimates. -/
theorem finite_good_mask_bound {ι Γ Ω : Type*} [Fintype Γ] [MeasurableSpace Ω]
    (R : Finset ι) (μ : Γ → Measure Ω) (w : Γ → ENNReal) (bad : ι → Γ → Set Ω)
    (hbadm : ∀ i ∈ R, ∀ γ, MeasurableSet (bad i γ)) :
    ∃ Good : Γ → Set Ω,
      (∀ γ, MeasurableSet (Good γ)) ∧
      (∀ γ z, z ∈ Good γ → ∀ i ∈ R, z ∉ bad i γ) ∧
      (∑ γ, w γ * μ γ (Good γ)ᶜ) ≤ ∑ i ∈ R, ∑ γ, w γ * μ γ (bad i γ) := by
  classical
  let U (γ : Γ) : Set Ω := ⋃ i ∈ R, bad i γ
  refine ⟨fun γ => (U γ)ᶜ, ?_, ?_, ?_⟩
  · intro γ
    exact (R.measurableSet_biUnion (fun i hi => hbadm i hi γ)).compl
  · intro γ z hz i hi hzi
    exact hz (mem_iUnion₂.mpr ⟨i, hi, hzi⟩)
  · simp only [compl_compl]
    calc (∑ γ, w γ * μ γ (U γ)) ≤ ∑ γ, w γ * ∑ i ∈ R, μ γ (bad i γ) := by
          apply Finset.sum_le_sum
          intro γ _
          exact mul_le_mul' le_rfl (measure_biUnion_finset_le R (fun i => bad i γ))
      _ = ∑ i ∈ R, ∑ γ, w γ * μ γ (bad i γ) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm

/-- Delete all the fixed-depth cap failures at once, under the original world
weights. The mask is measurable and its weighted exceptional mass still has a
fixed positive power of decay. No prior is conditioned or renormalized. -/
theorem finite_good_mask_powerSmall {ι : Type*} {N : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) (R : Finset ι)
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)] (W : ℕ → ℕ)
    (μ : (k : ℕ) → Fin (W k) → Measure (Ω k))
    (w : (k : ℕ) → Fin (W k) → ENNReal)
    (bad : ι → (k : ℕ) → Fin (W k) → Set (Ω k))
    (hbadm : ∀ i ∈ R, ∀ k γ, MeasurableSet (bad i k γ))
    (hbad : ∀ i ∈ R,
      IsPowerSmall N (fun k => ∑ γ, w k γ * μ k γ (bad i k γ))) :
    ∃ Good : (k : ℕ) → Fin (W k) → Set (Ω k),
      (∀ k γ, MeasurableSet (Good k γ)) ∧
      (∀ k γ z, z ∈ Good k γ → ∀ i ∈ R, z ∉ bad i k γ) ∧
      IsPowerSmall N (fun k => ∑ γ, w k γ * μ k γ (Good k γ)ᶜ) := by
  classical
  have hex (k : ℕ) := finite_good_mask_bound R (μ k) (w k) (fun i => bad i k)
    (fun i hi γ => hbadm i hi k γ)
  choose Good hGm hGc hmass using hex
  refine ⟨Good, hGm, hGc, ?_⟩
  exact (powerSmall_finset_sum hN R
    (fun i k => ∑ γ, w k γ * μ k γ (bad i k γ)) hbad).mono
      (Eventually.of_forall hmass)

/-- Impose an almost-everywhere condition pointwise on a measurable submask.
The discarded mass is exactly unchanged, even when the condition itself is not
known to be measurable. -/
theorem ae_good_submask {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Good : Set Ω) (hGood : MeasurableSet Good) (P : Ω → Prop) (hP : ∀ᵐ z ∂μ, P z) :
    ∃ F : Set Ω, F ⊆ Good ∧ MeasurableSet F ∧ (∀ z ∈ F, P z) ∧ μ Fᶜ = μ Goodᶜ := by
  let Bad := toMeasurable μ {z | ¬ P z}
  have hBad : MeasurableSet Bad := measurableSet_toMeasurable _ _
  have hnull : μ Bad = 0 := by
    rw [show Bad = toMeasurable μ {z | ¬ P z} from rfl, measure_toMeasurable]
    exact ae_iff.mp hP
  refine ⟨Good \ Bad, sdiff_subset, hGood.diff hBad, ?_, ?_⟩
  · intro z hz
    by_contra hn
    exact hz.2 (subset_toMeasurable μ {z | ¬ P z} hn)
  · rw [compl_sdiff]
    apply le_antisymm
    · simpa only [hnull, zero_add] using (measure_union_le Bad Goodᶜ :
        μ (Bad ∪ Goodᶜ) ≤ μ Bad + μ Goodᶜ)
    · exact measure_mono subset_union_right

end Submission.Obl.k4_homogeneous_native_pair_preparation
