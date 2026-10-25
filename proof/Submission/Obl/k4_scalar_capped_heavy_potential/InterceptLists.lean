import Mathlib
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps

namespace Submission.Obl.k4_scalar_capped_heavy_potential

open Set MeasureTheory
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

/-- Pairwise diameter at each state gives uniformly short lists of
actual intercept bins. The state and the set may be arbitrary. -/
theorem intercept_bin_lists_of_diameter {Ω Q : Type*}
    (S : Set Ω) (state : Ω → Q) (intercept : Ω → ℝ)
    {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (hdiam : ∀ p ∈ S, ∀ p' ∈ S, state p = state p' →
      |intercept p - intercept p'| ≤ L * a) :
    ∃ F : Q → Finset ℤ, (∀ q, ((F q).card : ℝ) ≤ 2 * L + 5) ∧
      ∀ p ∈ S, (⌊intercept p / a⌋ : ℤ) ∈ F (state p) := by
  classical
  let V : Finset ℤ := Finset.Icc (-⌈L + 1⌉) ⌈L + 1⌉
  let F : Q → Finset ℤ := fun q =>
    if hq : ∃ p ∈ S, state p = q then
      V.image (fun z => (⌊intercept hq.choose / a⌋ : ℤ) + z)
    else ∅
  refine ⟨F, ?_, ?_⟩
  · intro q
    dsimp only [F]
    split_ifs
    · exact (Nat.cast_le.mpr Finset.card_image_le).trans (card_floor_offsets_le hL)
    · simp
      linarith
  · intro p hp
    have hq : ∃ p' ∈ S, state p' = state p := ⟨p, hp, rfl⟩
    dsimp only [F]
    rw [dite_eq_left hq]
    apply Finset.mem_image.mpr
    refine ⟨⌊intercept p / a⌋ - ⌊intercept hq.choose / a⌋, ?_, by omega⟩
    exact floor_offset_mem ha
      (hdiam p hp hq.choose hq.choose_spec.1 hq.choose_spec.2.symm)

/-- Small pointwise residuals and small physical variation control the
trajectory intercept, without choosing a common good time. -/
theorem intercept_diameter_of_residual {x x' f f' c c' ε U V : ℝ}
    (h : |x - f - c| ≤ ε) (h' : |x' - f' - c'| ≤ ε)
    (hx : |x - x'| ≤ U) (hf : |f - f'| ≤ V) :
    |c - c'| ≤ U + V + 2 * ε := by
  have h₀ : |c - (x - f)| ≤ ε := by
    simpa only [abs_sub_comm] using h
  have h₁ : |(x - f) - (x' - f')| ≤ U + V := by
    calc
      _ = |(x - x') - (f - f')| := by congr 1; ring
      _ ≤ |x - x'| + |f - f'| := abs_sub _ _
      _ ≤ _ := add_le_add hx hf
  have ht₀ := abs_sub_le c (x - f) (x' - f')
  have ht₁ := abs_sub_le c (x' - f') c'
  linarith

/-- Convert the pointwise finite lists into the zero-mass condition
needed by joint-state pruning. -/
theorem state_group_support_of_ae_list {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (state : Ω → Q) (group : Ω → ℤ)
    (F : Q → Finset ℤ) (hF : ∀ᵐ p ∂μ, group p ∈ F (state p)) :
    ∀ q c, c ∉ F q → μ {p | state p = q ∧ group p = c} = 0 := by
  intro q c hc
  apply measure_mono_null (t := {p | group p ∉ F (state p)}) _ (ae_iff.mp hF)
  intro p hp
  change group p ∉ F (state p)
  simpa only [hp.1, hp.2] using hc

end
end Submission.Obl.k4_scalar_capped_heavy_potential
