/-
Adapted from this LOT tree, o147, session x0502, commit 373d234,
Submission/Obl/k4_local_remainder_horizon_transfer/Homogenize/Encode.lean
(that session's own code).
-/
import Mathlib
import Submission.Obl.k4_remainder_pure_profile_normalization.Definitions

/-!
# Encoding several worlds into one

Homogenization (paper Lemma 2.5) is available, as the accepted obligation o075
`k4_joint_homogenization`, for a single world with unit derivative scale. To
homogenize a problem with many worlds (the charts of a normalized problem) we move
each world `γ` by an affine change of trajectory coefficients:

* the trajectory index `i` becomes `γ + W * i`, so the worlds have disjoint indices;
* the first planar coordinate is scaled by `a` and shifted by `o`, the second is scaled
  by `b`, and both planar velocities are shifted by `1/2`;
* the hidden coordinate is scaled by `θ`.

This file records the maps and their effect on lines and on Lebesgue measure.

-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set
open scoped ENNReal

/-! ## Indices -/

/-- The index of trajectory `i` of world `γ` in the encoded single world. -/
def encIdx (W : ℕ) (γ : Fin W) (i : ℕ) : ℕ := (γ : ℕ) + W * i

theorem encIdx_mod {W : ℕ} (γ : Fin W) (i : ℕ) : encIdx W γ i % W = γ := by
  unfold encIdx
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt γ.2

theorem encIdx_div {W : ℕ} (γ : Fin W) (i : ℕ) : encIdx W γ i / W = i := by
  unfold encIdx
  have hW : 0 < W := lt_of_le_of_lt (Nat.zero_le _) γ.2
  rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt γ.2, zero_add]

theorem encIdx_inj {W : ℕ} {γ γ' : Fin W} {i i' : ℕ}
    (h : encIdx W γ i = encIdx W γ' i') : γ = γ' ∧ i = i' := by
  refine ⟨Fin.ext ?_, ?_⟩
  · rw [← encIdx_mod γ i, ← encIdx_mod γ' i', h]
  · rw [← encIdx_div γ i, ← encIdx_div γ' i', h]

/-- The world of an encoded index. -/
def decWorld {W : ℕ} (hW : 0 < W) (n : ℕ) : Fin W := ⟨n % W, Nat.mod_lt _ hW⟩

theorem encIdx_decWorld {W : ℕ} (hW : 0 < W) (n : ℕ) :
    encIdx W (decWorld hW n) (n / W) = n := by
  unfold encIdx decWorld
  exact Nat.mod_add_div n W

theorem decWorld_encIdx {W : ℕ} (hW : 0 < W) (γ : Fin W) (i : ℕ) :
    decWorld hW (encIdx W γ i) = γ := by
  ext
  exact encIdx_mod γ i

theorem encIdx_le {W : ℕ} (γ : Fin W) (i : ℕ) : (encIdx W γ i : ℝ) ≤ W * (i + 1) := by
  unfold encIdx
  have : ((γ : ℕ) : ℝ) ≤ W := by exact_mod_cast γ.2.le
  push_cast
  nlinarith

/-! ## Coefficients -/

/-- The affine change of trajectory coefficients of one world. -/
noncomputable def encCoeff (a b θ o : ℝ) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![a * x 0 + o, b * x 1, θ * x 2, a * x 3 + 1 / 2, b * x 4 + 1 / 2, θ * x 5]

/-- Its inverse. -/
noncomputable def decCoeff (a b θ o : ℝ) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![(x 0 - o) / a, x 1 / b, x 2 / θ, (x 3 - 1 / 2) / a, (x 4 - 1 / 2) / b, x 5 / θ]

theorem decCoeff_encCoeff {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hθ : θ ≠ 0) (o : ℝ)
    (x : Fin 6 → ℝ) : decCoeff a b θ o (encCoeff a b θ o x) = x := by
  funext i
  fin_cases i <;> simp [decCoeff, encCoeff] <;> field_simp

theorem encCoeff_decCoeff {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hθ : θ ≠ 0) (o : ℝ)
    (x : Fin 6 → ℝ) : encCoeff a b θ o (decCoeff a b θ o x) = x := by
  funext i
  fin_cases i <;> simp [decCoeff, encCoeff] <;> field_simp <;> ring

theorem continuous_encCoeff (a b θ o : ℝ) : Continuous (encCoeff a b θ o) := by
  unfold encCoeff
  fun_prop

theorem continuous_decCoeff (a b θ o : ℝ) : Continuous (decCoeff a b θ o) := by
  unfold decCoeff
  fun_prop

/-- The coefficient change as a measurable equivalence. -/
noncomputable def encEquiv {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hθ : θ ≠ 0) (o : ℝ) :
    (Fin 6 → ℝ) ≃ᵐ (Fin 6 → ℝ) where
  toFun := encCoeff a b θ o
  invFun := decCoeff a b θ o
  left_inv := decCoeff_encCoeff ha hb hθ o
  right_inv := encCoeff_decCoeff ha hb hθ o
  measurable_toFun := (continuous_encCoeff a b θ o).measurable
  measurable_invFun := (continuous_decCoeff a b θ o).measurable

@[simp] theorem encEquiv_apply {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hθ : θ ≠ 0) (o : ℝ)
    (x : Fin 6 → ℝ) : encEquiv ha hb hθ o x = encCoeff a b θ o x := rfl

@[simp] theorem encEquiv_symm_apply {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hθ : θ ≠ 0)
    (o : ℝ) (x : Fin 6 → ℝ) : (encEquiv ha hb hθ o).symm x = decCoeff a b θ o x := rfl

/-- The diagonal of the linear part. -/
def encDiag (a b θ : ℝ) : Fin 6 → ℝ := ![a, b, θ, a, b, θ]

/-- The translation part. -/
noncomputable def encShift (o : ℝ) : Fin 6 → ℝ := ![o, 0, 0, 1 / 2, 1 / 2, 0]

theorem encCoeff_eq (a b θ o : ℝ) (x : Fin 6 → ℝ) :
    encCoeff a b θ o x =
      Matrix.toLin' (Matrix.diagonal (encDiag a b θ)) x + encShift o := by
  funext i
  rw [Matrix.toLin'_apply, Pi.add_apply, Matrix.mulVec_diagonal]
  fin_cases i <;> simp [encCoeff, encDiag, encShift]

/-- Lebesgue measure is multiplied by the inverse Jacobian `|a b θ|⁻²`. -/
theorem map_encCoeff_volume {a b θ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hθ : θ ≠ 0) (o : ℝ) :
    (volume : Measure (Fin 6 → ℝ)).map (encCoeff a b θ o) =
      ENNReal.ofReal |(a * b * θ) ^ 2|⁻¹ • volume := by
  have hdet : LinearMap.det (Matrix.toLin' (Matrix.diagonal (encDiag a b θ))) =
      (a * b * θ) ^ 2 := by
    rw [LinearMap.det_toLin', Matrix.det_diagonal]
    simp [encDiag, Fin.prod_univ_succ]
    ring
  have hdet0 : LinearMap.det (Matrix.toLin' (Matrix.diagonal (encDiag a b θ))) ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero ha hb) hθ)
  have hfun : encCoeff a b θ o =
      (fun x => x + encShift o) ∘ (Matrix.toLin' (Matrix.diagonal (encDiag a b θ))) := by
    funext x
    exact encCoeff_eq a b θ o x
  rw [hfun, ← Measure.map_map (measurable_add_const _)
    (LinearMap.continuous_of_finiteDimensional _).measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, Measure.map_smul,
    map_add_right_eq_self, hdet, abs_inv]
  exact (measurable_add_const _).aemeasurable

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
