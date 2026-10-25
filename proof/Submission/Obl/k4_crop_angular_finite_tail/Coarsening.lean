/- Adapted from this LOT tree, obligation o091, session x0299, commit 918e44ebabf26b3b2fd56f3cccbf12b4ac1bac6e,
Submission/Obl/k4_dyadic_crop_typicality/Coarsening.lean. Transfer.lean in that branch was written by session x0302 (9db252b). -/

import Submission.Obl.k4_crop_angular_finite_tail.Observations
import Submission.Obl.k4_native_grid_profile_extension.CountedRefinement
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace Submission.Obl.k4_crop_angular_finite_tail

def coarseningFiber (d : ℕ) (v : VelocityBin) : Finset VelocityBin :=
  Fintype.piFinset (fun j => Finset.Ico ((2 : ℤ)^d * v j) ((2 : ℤ)^d * (v j + 1)))

lemma mem_coarseningFiber (d : ℕ) (v w : VelocityBin) :
    w ∈ coarseningFiber d v ↔ (fun j => w j / (2 : ℤ)^d) = v := by
  simp only [coarseningFiber, Fintype.mem_piFinset, Finset.mem_Ico, funext_iff]
  apply forall_congr'
  intro j
  have hm : 0 < (2 : ℤ)^d := by positivity
  constructor
  · intro h
    apply le_antisymm
    · have h' : w j / (2 : ℤ)^d < v j + 1 := by
        rw [Int.ediv_lt_iff_lt_mul hm]
        simpa only [mul_comm] using h.2
      omega
    · rw [Int.le_ediv_iff_mul_le hm]
      simpa only [mul_comm] using h.1
  · intro h
    constructor
    · have h' := (Int.le_ediv_iff_mul_le hm).mp h.ge
      simpa only [mul_comm] using h'
    · have h' := (Int.ediv_lt_iff_lt_mul hm).mp (show w j / (2 : ℤ)^d < v j + 1 by omega)
      simpa only [mul_comm] using h'

lemma card_coarseningFiber (d : ℕ) (v : VelocityBin) :
    (coarseningFiber d v).card = (2^d)^2 := by
  simp only [coarseningFiber, Fintype.card_piFinset, Int.card_Ico]
  have h (j : Fin 2) : ((2 : ℤ)^d * (v j + 1) - (2 : ℤ)^d * v j).toNat = 2^d := by
    rw [show (2 : ℤ)^d * (v j + 1) - (2 : ℤ)^d * v j = (2 : ℤ)^d by ring]
    norm_cast
  simp only [h]
  simp

lemma map_coarsen_count (d : ℕ) :
    (Measure.count : Measure VelocityBin).map (fun w j => w j / (2 : ℤ)^d) =
      (((2^d)^2 : ℕ) : ENNReal) • (Measure.count : Measure VelocityBin) := by
  apply Measure.ext_of_singleton
  intro v
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : (fun w : VelocityBin => fun j => w j / (2 : ℤ)^d) ⁻¹' {v} =
      (coarseningFiber d v : Set VelocityBin) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe, mem_coarseningFiber]
  rw [he, Measure.count_apply_finset, card_coarseningFiber]
  simp

lemma count_coarsening_fiber (d : ℕ) (v : VelocityBin) :
    Measure.count {w : VelocityBin | (fun j => w j / (2 : ℤ)^d) = v} =
      (((2^d)^2 : ℕ) : ENNReal) := by
  have he : {w : VelocityBin | (fun j => w j / (2 : ℤ)^d) = v} =
      (coarseningFiber d v : Set VelocityBin) := by
    ext w
    exact (mem_coarseningFiber d v w).symm
  rw [he, Measure.count_apply_finset, card_coarseningFiber]

lemma count_coarsening_fiber_le_four {d : ℕ} (hd : d ≤ 1) (v : VelocityBin) :
    Measure.count {w : VelocityBin | (fun j => w j / (2 : ℤ)^d) = v} ≤
      (4 : ENNReal) := by
  rw [count_coarsening_fiber]
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> norm_num

lemma map_coarsen_reference (d : ℕ) :
    Submission.Obl.k4_profile_density_bounds.reference.map (coarsenObservation d) =
      (((2^d)^2 : ℕ) : ENNReal) • Submission.Obl.k4_profile_density_bounds.reference := by
  change (baseReference.prod Measure.count).map
      (Prod.map (id : BaseObservation → BaseObservation)
        (fun w : VelocityBin => fun j => w j / (2 : ℤ)^d)) = _
  rw [← Measure.map_prod_map baseReference Measure.count measurable_id
      (measurable_of_countable _), Measure.map_id, map_coarsen_count, Measure.prod_smul_right]
  rfl

lemma map_coarsen_withDensity (d : ℕ) (g : Observation → ENNReal) (hg : Measurable g) :
    (Submission.Obl.k4_profile_density_bounds.reference.withDensity g).map (coarsenObservation d) =
      Submission.Obl.k4_profile_density_bounds.reference.withDensity
        (Submission.Obl.k4_native_grid_profile_extension.fiberDensity
          (fun w : VelocityBin => fun j => w j / (2 : ℤ)^d) g) := by
  change ((baseReference.prod Measure.count).withDensity g).map
    (fun z => (z.1, fun j => z.2 j / (2 : ℤ)^d)) = _
  exact Submission.Obl.k4_native_grid_profile_extension.map_labels_withDensity baseReference
    (fun w : VelocityBin => fun j => w j / (2 : ℤ)^d) g hg

/-- The coarsened density has the same density window as the fine density,
apart from a fourfold low-ratio loss in its upper tail. -/
lemma coarsening_tail_bound {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (Q : A → Observation) (hQ : Measurable Q)
    {d : ℕ} (hd : d ≤ 1) (H K : Observation → ENNReal)
    (hH : Measurable H) (hK : Measurable K)
    (hFine : μ.map Q = Submission.Obl.k4_profile_density_bounds.reference.withDensity H)
    (hCoarse : μ.map (coarsenObservation d ∘ Q) =
      Submission.Obl.k4_profile_density_bounds.reference.withDensity K)
    (δ lo hi : ENNReal) :
    μ {p | K (coarsenObservation d (Q p)) < lo ∨
      hi < δ * K (coarsenObservation d (Q p))} ≤
      μ {p | H (Q p) < lo ∨ hi < H (Q p)} + δ * 4 * μ univ := by
  let h : VelocityBin → VelocityBin := fun w j => w j / (2 : ℤ)^d
  have hm : μ.map (fun p => ((Q p).1, h (Q p).2)) =
      (baseReference.prod Measure.count).withDensity K := hCoarse
  have hf : μ.map Q = (baseReference.prod Measure.count).withDensity H := hFine
  have hmono := Submission.Obl.k4_native_grid_profile_extension.observation_refinement_density_le
    μ baseReference Q hQ h K H hK hH hm hf
  have htail := Submission.Obl.k4_native_grid_profile_extension.observation_refinement_low_density_mass
    μ baseReference Q hQ h δ 4 (count_coarsening_fiber_le_four hd) K H hK hH hm hf
  have hsub : ∀ᵐ p ∂μ,
      p ∈ {p | K (coarsenObservation d (Q p)) < lo ∨
        hi < δ * K (coarsenObservation d (Q p))} →
      p ∈ {p | H (Q p) < lo ∨ hi < H (Q p)} ∪
        {p | H (Q p) < δ * K (coarsenObservation d (Q p))} := by
    filter_upwards [hmono] with p hp hbad
    change H (Q p) ≤ K (coarsenObservation d (Q p)) at hp
    rcases hbad with hlow | hhigh
    · exact Or.inl (Or.inl (hp.trans_lt hlow))
    · by_cases hb : hi < H (Q p)
      · exact Or.inl (Or.inr hb)
      · exact Or.inr ((not_lt.mp hb).trans_lt hhigh)
  calc
    _ ≤ μ ({p | H (Q p) < lo ∨ hi < H (Q p)} ∪
        {p | H (Q p) < δ * K (coarsenObservation d (Q p))}) := measure_mono_ae hsub
    _ ≤ μ {p | H (Q p) < lo ∨ hi < H (Q p)} +
        μ {p | H (Q p) < δ * K (coarsenObservation d (Q p))} := measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl htail

end Submission.Obl.k4_crop_angular_finite_tail
