import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.CommonMasks

/-! A finite menu of actual original-coordinate views shares one final
probability and one mask. Bad events are charged before choosing a window. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set Filter
open scoped ENNReal Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable section

theorem powerSmall_finset_sum {α : Type*} {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    (s : Finset α) (a : α → ℕ → ℝ≥0∞)
    (ha : ∀ i ∈ s, IsPowerSmall N (a i)) :
    IsPowerSmall N (fun k => ∑ i ∈ s, a i k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, Eventually.of_forall fun k => by simp⟩
  | insert i s his ih =>
    have h₁ := ha i (Finset.mem_insert_self _ _)
    have h₂ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert his] using h₁.add hN h₂

variable {α : Type*} [Fintype α] {z : Code}
  (p : α → Code) (view : (i : α) → RefinementChain (p i) z)
  (bad : (i : α) → (k : ℕ) → Set (Fin (W (p i) ((view i).sample k)) × State))

def viewsBad (k : ℕ) : Set (Fin (W z k) × State) :=
  ⋃ i, (view i).pullback k ⁻¹' bad i k

theorem measurableSet_viewsBad
    (hmeas : ∀ i k, MeasurableSet (bad i k)) (k : ℕ) :
    MeasurableSet (viewsBad p view bad k) :=
  MeasurableSet.iUnion fun i => (hmeas i k).preimage ((view i).measurable_pullback k)

/-- Every original exception is pulled back through its own literal
suffix, with all masses measured on the same final probability. -/
theorem viewsBad_powerSmall (hz : Exact z)
    (hmeas : ∀ i k, MeasurableSet (bad i k))
    (hsmall : ∀ i, IsPowerSmall (N z)
      (fun k => worldMixture (p i) ((view i).sample k) (bad i k))) :
    IsPowerSmall (N z) (fun k => normalizedWorldMixture z k (viewsBad p view bad k)) := by
  have hi (i : α) : IsPowerSmall (N z)
      (fun k => normalizedWorldMixture z k ((view i).pullback k ⁻¹' bad i k)) := by
    apply (Submission.Obl.k4_dyadic_crop_typicality.powerSmall_mul_subpower
      (fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hz.1.1 k))
      ((view i).referenceFactor_subpower hz) (hsmall i)).mono
    exact Eventually.of_forall fun k =>
      (view i).common_preimage_le hz k (hmeas i k) _ le_rfl
  apply (powerSmall_finset_sum hz.1.2.1 Finset.univ _ (fun i _ => hi i)).mono
  exact Eventually.of_forall fun k => measure_iUnion_fintype_le _ _

def viewsMask (k : ℕ) : Set (Fin (W z k) × State) := (viewsBad p view bad k)ᶜ

theorem measurableSet_viewsMask (hmeas : ∀ i k, MeasurableSet (bad i k)) (k : ℕ) :
    MeasurableSet (viewsMask p view bad k) := (measurableSet_viewsBad p view bad hmeas k).compl

/-- A fixed finite menu of power-small original exceptions leaves at
least half of the common probability, before selecting any window. -/
theorem eventually_viewsMask_mass_half (hz : Exact z)
    (hmeas : ∀ i k, MeasurableSet (bad i k))
    (hsmall : ∀ i, IsPowerSmall (N z)
      (fun k => worldMixture (p i) ((view i).sample k) (bad i k))) :
    ∀ᶠ k in atTop, ENNReal.ofReal (1 / 2 : ℝ) ≤
      normalizedWorldMixture z k (viewsMask p view bad k) := by
  obtain ⟨c, hc, hbound⟩ := viewsBad_powerSmall p view bad hz hmeas hsmall
  have ht : ∀ᶠ k in atTop, N z k ^ (-c) ≤ (1 / 2 : ℝ) :=
    ((tendsto_rpow_neg_atTop hc).comp hz.1.2.1).eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hbound, ht] with k hk hpow
  letI := normalizedWorldMixture_isProbability hz k
  have hbad : normalizedWorldMixture z k (viewsBad p view bad k) ≤
      ENNReal.ofReal (1 / 2 : ℝ) := hk.trans (ENNReal.ofReal_le_ofReal hpow)
  apply Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
    (1 : ℝ≥0∞) _ _ 1 (by norm_num) (by norm_num) ?_ hbad
  rw [viewsMask, add_comm, measure_add_measure_compl (measurableSet_viewsBad p view bad hmeas k)]
  simp

/-- The one common mask removes the prescribed original event in every
view; later dominated laws inherit all these null events. -/
theorem restrict_viewsMask_null (hmeas : ∀ i k, MeasurableSet (bad i k)) (i : α) (k : ℕ) :
    ((normalizedWorldMixture z k).restrict (viewsMask p view bad k))
      ((view i).pullback k ⁻¹' bad i k) = 0 := by
  rw [Measure.restrict_apply ((hmeas i k).preimage ((view i).measurable_pullback k))]
  have heq : (view i).pullback k ⁻¹' bad i k ∩ viewsMask p view bad k = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro u ⟨hu, hmask⟩
    exact hmask (Set.mem_iUnion.mpr ⟨i, hu⟩)
  rw [heq, measure_empty]

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
