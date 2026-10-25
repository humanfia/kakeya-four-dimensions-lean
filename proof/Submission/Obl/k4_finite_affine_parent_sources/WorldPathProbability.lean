-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit 37b81a6e.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/WorldPathProbability.lean.
import Submission.Obl.k4_paired_test_normalization.TaggedPairs
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal

/-! The one fixed probability on the weighted original terminal path. World
tags retain the unchanged original laws and their exact weight factors. -/

namespace Submission.Obl.k4_finite_affine_parent_sources.WorldPath

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal
open Submission.Obl.k4_paired_test_normalization

variable {Γ α : Type*} [Fintype Γ] [MeasurableSpace Γ]
  [MeasurableSingletonClass Γ] [MeasurableSpace α]

def original (ν : Γ → Measure α) (ω : Γ → ℝ) (H : Γ → Set (α × ℝ)) :
    Measure (Γ × (α × ℝ)) :=
  taggedPairMeasure (fun γ => ((ν γ).prod volume).restrict (H γ)) ω

theorem original_mass (ν : Γ → Measure α) (ω : Γ → ℝ) (H : Γ → Set (α × ℝ)) :
    original ν ω H univ = ∑ γ, ENNReal.ofReal (ω γ) * (ν γ).prod volume (H γ) := by
  rw [original, taggedPairMeasure_apply _ _ MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply_univ]

/-- The original weighted terminal law is a subprobability. No inverse
world weight or number of path labels is paid. -/
theorem original_mass_le_one (ν : Γ → Measure α) [∀ γ, IsProbabilityMeasure (ν γ)]
    (ω : Γ → ℝ) (hω : ∀ γ, 0 ≤ ω γ) (hω1 : ∑ γ, ω γ = 1)
    (H : Γ → Set (α × ℝ)) (hH : ∀ γ, H γ ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    original ν ω H univ ≤ 1 := by
  have hunit (γ : Γ) : (ν γ).prod volume (Set.univ ×ˢ Icc (0 : ℝ) 1) = 1 := by
    rw [Measure.prod_prod]
    simp
  rw [original_mass]
  calc
    _ ≤ ∑ γ, ENNReal.ofReal (ω γ) * 1 :=
      sum_le_sum fun γ _ => mul_le_mul' le_rfl ((measure_mono (hH γ)).trans_eq (hunit γ))
    _ = ENNReal.ofReal (∑ γ, ω γ) := by
      simp only [mul_one, ENNReal.ofReal_sum_of_nonneg (fun γ _ => hω γ)]
    _ = 1 := by rw [hω1]; norm_num

def probability (ν : Γ → Measure α) (ω : Γ → ℝ) (H : Γ → Set (α × ℝ)) :
    Measure (Γ × (α × ℝ)) :=
  (original ν ω H univ)⁻¹ • original ν ω H

theorem original_finite (ν : Γ → Measure α) [∀ γ, IsProbabilityMeasure (ν γ)]
    (ω : Γ → ℝ) (hω : ∀ γ, 0 ≤ ω γ) (hω1 : ∑ γ, ω γ = 1)
    (H : Γ → Set (α × ℝ)) (hH : ∀ γ, H γ ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    IsFiniteMeasure (original ν ω H) :=
  ⟨lt_of_le_of_lt (original_mass_le_one ν ω hω hω1 H hH) (by simp)⟩

/-- A positive original weighted path is normalized once. Every later
event keeps the same original world law and its original world weight. -/
theorem probability_spec (ν : Γ → Measure α) [∀ γ, IsProbabilityMeasure (ν γ)]
    (ω : Γ → ℝ) (hω : ∀ γ, 0 ≤ ω γ) (hω1 : ∑ γ, ω γ = 1)
    (H : Γ → Set (α × ℝ)) (hH : ∀ γ, H γ ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hpositive : original ν ω H univ ≠ 0) :
    IsProbabilityMeasure (probability ν ω H) ∧
      ∀ γ (A : Set (α × ℝ)), MeasurableSet A →
        probability ν ω H ({γ} ×ˢ A) =
          (original ν ω H univ)⁻¹ * ENNReal.ofReal (ω γ) *
            (ν γ).prod volume (A ∩ H γ) := by
  have hfinite : original ν ω H univ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (original_mass_le_one ν ω hω hω1 H hH)
  constructor
  · rw [isProbabilityMeasure_iff, probability, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hpositive hfinite
  · intro γ A hA
    rw [probability, Measure.smul_apply, smul_eq_mul,
      original, taggedPairMeasure_slice _ _ γ hA, Measure.restrict_apply hA]
    ring

/-- The original inverse-slack mass floor pays for this one normalization.
The bound uses the weighted path mass, independently of the number or
individual weights of its worlds. -/
theorem probability_le_original
    (ν : Γ → Measure α) [∀ γ, IsProbabilityMeasure (ν γ)]
    (ω : Γ → ℝ) (hω : ∀ γ, 0 ≤ ω γ) (hω1 : ∑ γ, ω γ = 1)
    (H : Γ → Set (α × ℝ)) (hH : ∀ γ, H γ ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (κ : ℝ) (hκ : 0 < κ)
    (hfloor : ENNReal.ofReal κ⁻¹ ≤ original ν ω H univ) :
    probability ν ω H ≤ ENNReal.ofReal κ • original ν ω H := by
  have : IsFiniteMeasure (original ν ω H) := original_finite ν ω hω hω1 H hH
  have hpositive : original ν ω H univ ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos.mpr (inv_pos.mpr hκ)).trans_le hfloor)
  have hM : 0 < (original ν ω H).real univ :=
    ENNReal.toReal_pos hpositive (measure_ne_top _ _)
  have hreal : κ⁻¹ ≤ (original ν ω H).real univ := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) hfloor
    simpa only [measureReal_def, ENNReal.toReal_ofReal (inv_nonneg.mpr hκ.le)] using hh
  have hinv : ((original ν ω H).real univ)⁻¹ ≤ κ :=
    (inv_le_comm₀ hM hκ).mpr hreal
  have hscalar : (original ν ω H univ)⁻¹ ≤ ENNReal.ofReal κ := by
    have heq : ENNReal.ofReal (((original ν ω H).real univ)⁻¹) =
        (original ν ω H univ)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hM, measureReal_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [← heq]
    exact ENNReal.ofReal_le_ofReal hinv
  apply Measure.le_iff.mpr
  intro U hU
  simp only [probability, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' hscalar le_rfl

/-- The accepted half-open accounting identity gives the exact total of a
frozen path level. Closed chart endpoints cost no incidence mass. -/
theorem level_original_mass
    {ι : Type*} [Fintype ι]
    (ν : Γ → Measure α) (ω : Γ → ℝ)
    (i T : ℕ) (lev : ι → ℕ) (world : ι → Γ) (j : ι → ℕ)
    (A : ι → Set α) (F : ι → Set (α × ℝ))
    (hFm : ∀ b, lev b = i → MeasurableSet (F b))
    (hF : ∀ b, lev b = i → ∀ p ∈ F b,
      p.1 ∈ A b ∧ p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T)
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T))
    (hA : ∀ b b', lev b = i → lev b' = i → b ≠ b' → world b = world b' →
      j b = j b' → Disjoint (A b) (A b')) :
    original ν ω (Submission.Obl.k4_quadratic_finite_greedy_cover.levelMask
      i T lev world j F) univ =
      ∑ b, if lev b = i then ENNReal.ofReal (ω (world b)) *
        (ν (world b)).prod volume (F b) else 0 := by
  rw [original_mass]
  exact Submission.Obl.k4_quadratic_finite_greedy_cover.levelMask_mass ν
    (fun γ => ENNReal.ofReal (ω γ)) i T lev world j A F hFm hF hA

end

end Submission.Obl.k4_finite_affine_parent_sources.WorldPath
