import Submission.Lib.K4VelocityStrips.StripBins
import Submission.Obl.k4_scalar_capped_heavy_potential.InterceptLists

namespace Submission.Obl.k4_scalar_capped_heavy_potential

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4VelocityStrips

noncomputable section

/-- One fixed intercept bin gives a whole-trajectory fit to a single
constant translate of the common potential. -/
theorem potential_fit_in_intercept_bin (P : MvPolynomial (Fin 2) ℝ)
    (z : Fin 2 → ℝ) {X c ε w : ℝ} (hw : 0 < w) (g : ℤ)
    (hg : (⌊c / w⌋ : ℤ) = g)
    (hfit : |X - eval z P - c| ≤ ε) :
    |X - eval z (P + C ((g : ℝ) * w))| ≤ ε + w := by
  have hc := midpoint_floor_center_bound hw c
  rw [hg] at hc
  rw [eval_add, eval_C]
  calc
    _ = |(X - eval z P - c) + (c - (g : ℝ) * w)| := by congr 1; ring
    _ ≤ |X - eval z P - c| + |c - (g : ℝ) * w| := abs_add_le _ _
    _ ≤ _ := add_le_add hfit hc

theorem shifted_potential_degree (P : MvPolynomial (Fin 2) ℝ) {D : ℕ}
    (hP : P.totalDegree ≤ D) (c : ℝ) : (P + C c).totalDegree ≤ D := by
  exact (totalDegree_add _ _).trans (max_le hP (by simp))

theorem shifted_potential_coeff_bound (P : MvPolynomial (Fin 2) ℝ) {H c : ℝ}
    (hH : 0 ≤ H) (hcoeff : ∀ m, |P.coeff m| ≤ H) (m : Fin 2 →₀ ℕ) :
    |(P + C c).coeff m| ≤ H + |c| := by
  calc
    _ ≤ |P.coeff m| + |(C c : MvPolynomial (Fin 2) ℝ).coeff m| := by
      rw [MvPolynomial.coeff_add]
      exact abs_add_le _ _
    _ ≤ H + |c| := by
      apply add_le_add (hcoeff m)
      by_cases hm : m = 0
      · subst m
        simp
      · simp [coeff_C, hm, eq_comm]

/-- The constant added to the potential has the same subpower size as
the original intercept function. -/
theorem intercept_bin_center_bound {c w H : ℝ} (hw : 0 < w)
    (hc : |c| ≤ H) (g : ℤ) (hg : (⌊c / w⌋ : ℤ) = g) : |(g : ℝ) * w| ≤ H + w := by
  have h := midpoint_floor_center_bound hw c
  rw [hg] at h
  calc
    _ ≤ |c| + |c - (g : ℝ) * w| := by
      have ht := abs_sub_le ((g : ℝ) * w) c 0
      simpa only [sub_zero, abs_sub_comm, add_comm] using ht
    _ ≤ _ := add_le_add hc h

/-- A bounded original intercept function meets only finitely many
integer bins; no lower bound is imposed on any bin. -/
theorem intercept_bin_mem_finite_window {c w H : ℝ} (hw : 0 < w) (hc : |c| ≤ H) :
    (⌊c / w⌋ : ℤ) ∈ Finset.Icc ⌊-H / w⌋ ⌊H / w⌋ := by
  exact Finset.mem_Icc.mpr
    ⟨Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hc).1 hw.le),
      Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hc).2 hw.le)⟩

/-- Within one actual joint (base-cell, hidden-bin) cell, the original
intercept labels occupy at most thirteen bins. -/
theorem joint_cell_intercept_lists {Ω : Type*} (S : Set Ω)
    (u : Ω → Fin 2 → ℝ) (X c : Ω → ℝ) (f : (Fin 2 → ℝ) → ℝ)
    {ξ w ε : ℝ} (hξ : 0 < ξ) (hw : 0 < w) (hε : ε ≤ w)
    (hfit : ∀ p ∈ S, |X p - f (u p) - c p| ≤ ε)
    (hosc : ∀ p ∈ S, ∀ p' ∈ S,
      (fun i => (⌊u p i / ξ⌋ : ℤ)) = (fun i => (⌊u p' i / ξ⌋ : ℤ)) →
      |f (u p) - f (u p')| ≤ w) :
    ∃ F : ((Fin 2 → ℤ) × ℤ) → Finset ℤ,
      (∀ q, ((F q).card : ℝ) ≤ 13) ∧
      ∀ p ∈ S, (⌊c p / w⌋ : ℤ) ∈
        F ((fun i => (⌊u p i / ξ⌋ : ℤ)), ⌊X p / w⌋) := by
  let code : Ω → (Fin 2 → ℤ) × ℤ := fun p =>
    ((fun i => (⌊u p i / ξ⌋ : ℤ)), ⌊X p / w⌋)
  have hdiam : ∀ p ∈ S, ∀ p' ∈ S, code p = code p' → |c p - c p'| ≤ 4 * w := by
    intro p hp p' hp' heq
    have hb := congrArg Prod.fst heq
    have hx := congrArg Prod.snd heq
    have hxd : |X p - X p'| ≤ w := by
      have ht := (Int.abs_sub_lt_one_of_floor_eq_floor hx).le
      rw [← sub_div, abs_div, abs_of_pos hw] at ht
      simpa using (div_le_iff₀ hw).mp ht
    have h := intercept_diameter_of_residual (hfit p hp) (hfit p' hp') hxd (hosc p hp p' hp' hb)
    linarith
  have hlist := intercept_bin_lists_of_diameter S code c hw (by norm_num : (0 : ℝ) ≤ 4) hdiam
  simpa only [show (2 : ℝ) * 4 + 5 = 13 by norm_num] using hlist

/-- The fine physical states carry at most seven actual intercept bins
when all simulation errors fit inside one target intercept width. -/
theorem fine_cell_intercept_lists {Ω : Type*} (S : Set Ω)
    (X : Ω → Fin 3 → ℝ) (c f : Ω → ℝ) {b w ε V : ℝ}
    (hb : 0 < b) (hw : 0 < w) (herror : b + V + 2 * ε ≤ w)
    (hfit : ∀ p ∈ S, |X p 2 - f p - c p| ≤ ε)
    (hosc : ∀ p ∈ S, ∀ p' ∈ S,
      (fun i => (⌊X p i / b⌋ : ℤ)) = (fun i => (⌊X p' i / b⌋ : ℤ)) → |f p - f p'| ≤ V) :
    ∃ F : (Fin 3 → ℤ) → Finset ℤ,
      (∀ q, ((F q).card : ℝ) ≤ 7) ∧
      ∀ p ∈ S, (⌊c p / w⌋ : ℤ) ∈ F (fun i => (⌊X p i / b⌋ : ℤ)) := by
  let code : Ω → Fin 3 → ℤ := fun p i => ⌊X p i / b⌋
  have hdiam : ∀ p ∈ S, ∀ p' ∈ S, code p = code p' → |c p - c p'| ≤ 1 * w := by
    intro p hp p' hp' heq
    have hx := congrFun heq 2
    have hxd : |X p 2 - X p' 2| ≤ b := by
      have ht := (Int.abs_sub_lt_one_of_floor_eq_floor hx).le
      rw [← sub_div, abs_div, abs_of_pos hb] at ht
      simpa using (div_le_iff₀ hb).mp ht
    have hc := intercept_diameter_of_residual (hfit p hp) (hfit p' hp') hxd (hosc p hp p' hp' heq)
    linarith
  have hl := intercept_bin_lists_of_diameter S code c hw (by norm_num : (0 : ℝ) ≤ 1) hdiam
  simpa only [show (2 : ℝ) * 1 + 5 = 7 by norm_num] using hl

end
end Submission.Obl.k4_scalar_capped_heavy_potential
