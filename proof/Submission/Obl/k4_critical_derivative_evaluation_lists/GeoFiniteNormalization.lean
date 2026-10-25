import Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/- Adapted from this LOT tree, obligation o107, session x0353, commit 96bcaa7b51cc,
   file Submission/Obl/k4_finite_narrowness_path_improvement/FiniteNormalization.lean (namespace and imports renamed only). -/

/-! Conditional laws are unchanged by probability normalization, and selected
mass is restored by the exact original normalization factor. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists

open Finset
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

theorem finite_fiberMass_scale {Ω γ : Type*} [Fintype Ω] [DecidableEq γ]
    (P : Ω → ℝ) (key : Ω → γ) (z : γ) (a : ℝ) :
    fiberMass (fun e => a * P e) key z = a * fiberMass P key z := by
  unfold fiberMass
  rw [mul_sum]

theorem finite_atomMass_scale {Ω γ : Type*} [Fintype Ω] [DecidableEq γ]
    (P : Ω → ℝ) (key : Ω → γ) (e : Ω) (a : ℝ) :
    atomMass (fun e => a * P e) key e = a * atomMass P key e :=
  finite_fiberMass_scale P key (key e) a

theorem finite_condKey_scale {Ω γ : Type*} [Fintype Ω] [DecidableEq γ]
    (P : Ω → ℝ) (key : Ω → γ) (e er : Ω) (a : ℝ) (ha : a ≠ 0) :
    condKey (fun e => a * P e) key e er = condKey P key e er := by
  classical
  unfold condKey
  rw [finite_atomMass_scale]
  split_ifs
  · by_cases hd : atomMass P key e = 0
    · simp [hd]
    · field_simp
  · rfl

theorem finite_normalized_total {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) (M : ℝ) (hM : M ≠ 0) (hmass : ∑ e, P e = M) :
    (∑ e, M⁻¹ * P e) = 1 := by
  rw [← mul_sum, hmass, inv_mul_cancel₀ hM]

theorem finite_selected_mass_restore {Ω : Type*}
    (S : Finset Ω) (P : Ω → ℝ) (M A : ℝ) (hM : 0 < M)
    (hmass : A ≤ ∑ e ∈ S, M⁻¹ * P e) : M * A ≤ ∑ e ∈ S, P e := by
  calc
    _ ≤ M * ∑ e ∈ S, M⁻¹ * P e := mul_le_mul_of_nonneg_left hmass hM.le
    _ = ∑ e ∈ S, M * (M⁻¹ * P e) := mul_sum _ _ _
    _ = _ := sum_congr rfl fun e _ => by rw [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]

end Submission.Obl.k4_critical_derivative_evaluation_lists
