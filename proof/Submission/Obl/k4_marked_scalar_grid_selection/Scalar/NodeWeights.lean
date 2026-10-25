/- Adapted from this LOT tree, obligation o100, session x0340, commit efabdd9,
   Submission/Obl/k4_scalar_marked_profile_selection/NodeWeights.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.Budgets

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

/-- Original record weights, as real numbers for logarithmic type selection. -/
noncomputable def realNodeMass {H J : ℕ} {κ : Type*} (I : Finset (AtomIndex H J))
    (σ ρ : ℝ) (w : Fin H → ℝ) (code : AtomIndex H J → κ) (c : κ) : ℝ := by
  classical
  exact (σ⁻¹ * min 1 (ρ / σ)) * ∑ i ∈ I.filter (fun i => code i = c), w i.1

/-- The real and extended-nonnegative-real record weights agree exactly. -/
theorem ofReal_realNodeMass {H J : ℕ} {κ : Type*} (I : Finset (AtomIndex H J))
    {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (code : AtomIndex H J → κ) (c : κ) :
    ENNReal.ofReal (realNodeMass I σ ρ w code c) = recordMass I (jointNodeWeight σ ρ w) code c := by
  classical
  dsimp [realNodeMass, recordMass, jointNodeWeight]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i.1)]
  simp only [Finset.mul_sum, mul_comm]

/-- An occupied record has at least its atom's weight times the noise density cap. -/
theorem realNodeMass_lower {H J : ℕ} {κ : Type*} (I : Finset (AtomIndex H J))
    {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (code : AtomIndex H J → κ) (i : AtomIndex H J) (hi : i ∈ I) :
    (σ⁻¹ * min 1 (ρ / σ)) * w i.1 ≤ realNodeMass I σ ρ w code (code i) := by
  classical
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.single_le_sum (s := I.filter (fun j => code j = code i))
    (f := fun j => w j.1) (a := i) (fun j _ => hw j.1) (by simp only [Finset.mem_filter, and_true]; exact hi)

/-- Every original record has weight bounded by the full repeated prior. -/
theorem realNodeMass_upper {H J : ℕ} {κ : Type*} (I : Finset (AtomIndex H J))
    {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (code : AtomIndex H J → κ) (c : κ) :
    realNodeMass I σ ρ w code c ≤ σ⁻¹ * (J : ℝ) := by
  classical
  dsimp [realNodeMass]
  calc
    _ ≤ (σ⁻¹ * min 1 (ρ / σ)) * (J : ℝ) :=
      mul_le_mul_of_nonneg_left (atom_tag_weight_sum_le w hw hw1 _) (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg J)
      exact mul_le_of_le_one_right (inv_nonneg.mpr hσ.le) (min_le_left _ _)

/-- For widths at most one the atom cap is at least the slope width. -/
theorem noiseCap_lower {σ ρ : ℝ} (hσ : 0 < σ) (hσ₁ : σ ≤ 1)
    (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) : ρ ≤ σ⁻¹ * min 1 (ρ / σ) := by
  have hinv : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ).mpr hσ₁
  have hdiv : ρ ≤ ρ / σ := by
    apply (le_div_iff₀ hσ).mpr
    exact mul_le_of_le_one_right hρ hσ₁
  have hmin : ρ ≤ min 1 (ρ / σ) := le_min hρ₁ hdiv
  calc
    ρ ≤ min 1 (ρ / σ) := hmin
    _ ≤ σ⁻¹ * min 1 (ρ / σ) :=
      le_mul_of_one_le_left (le_trans hρ hmin) hinv

/-- A lower bound on retained atom masses supplies a lower bound for every
record weight, uniformly over all slope widths in a bounded depth interval. -/
theorem realNodeMass_lower_cellWeight {H J : ℕ} {κ : Type*} (hJ : 1 ≤ J)
    (I : Finset (AtomIndex H J)) {σ ρ δ : ℝ} (hσ : 0 < σ) (hσ₁ : σ ≤ 1)
    (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hδ : 0 ≤ δ)
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) (code : AtomIndex H J → κ)
    (i : AtomIndex H J) (hi : i ∈ I) (hfloor : δ ≤ cellWeight J w i) :
    ρ * δ ≤ realNodeMass I σ ρ w code (code i) := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hcell : cellWeight J w i ≤ w i.1 :=
    div_le_self (hw i.1) hJr
  calc
    _ ≤ (σ⁻¹ * min 1 (ρ / σ)) * w i.1 :=
      mul_le_mul (noiseCap_lower hσ hσ₁ hρ hρ₁) (hfloor.trans hcell) hδ (by positivity)
    _ ≤ _ := realNodeMass_lower I hσ hρ w hw code i hi

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
