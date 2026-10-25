/-
Adapted from: here:o064
Written in this workspace by session x0217, from the supplied paper,
Lemma a03:actual-lists. No external formal code.
-/

import Submission.Lib.K4OriginalLists.CellAveraging

/-!
Original-law recovery on a one-dimensional polynomial cell partition, retaining
the original discrete observation.  The loss is independent of all finite tag
counts and of the complexity of the analytical mask and its fine list rule.
-/

namespace Submission.Lib.K4OriginalLists

open Finset MeasureTheory

/-- A masked measurable list rule can be replaced by a finite table indexed only by the
base cell and the original observed tag, at a quantitative polynomial averaging cost. -/
theorem original_polynomial_cell_list
    {ι o β : Type*} [Fintype ι] [Fintype o] [Fintype β] {m : ℕ}
    (ν : ι → Measure ℝ) [∀ c, IsProbabilityMeasure (ν c)]
    (C : ι → Set ℝ) (w : ι → ℝ) (hw : ∀ c, 0 ≤ w c)
    (p : Fin m → Polynomial ℝ) (rule : (Fin m → Bool) → (o × β) → ℝ) (H ρ : ℝ)
    (hbound : ∀ s, ∑ a, |rule s a| ≤ H)
    (hsupport : ∀ c, ∀ᵐ x ∂ν c, x ∈ C c)
    (hdiam : ∀ c x, x ∈ C c → ∀ y ∈ C c, |x - y| ≤ |ρ|)
    (hdom : (∑ c, ENNReal.ofReal (w c) • ν c) ≤ volume)
    (allowed : Finset β) (D : ℕ)
    (mask : (ι × o) → ℝ → β → ℝ)
    (hmaskint : ∀ c a, Integrable (fun x => mask c x a)
      (ENNReal.ofReal (w c.1) • ν c.1))
    (hmask : ∀ c x a, mask c x a ≤ rule (fun i => decide (0 ≤ (p i).eval x)) (c.2, a))
    (L : (ι × o) → ℝ → Finset β) (hLmeas : ∀ c, MeasurableLists (L c))
    (hL : ∀ c x, L c x ⊆ allowed ∧ (L c x).card ≤ D)
    (mass : ℝ)
    (hsuccess : mass ≤ continuousListMass
      (fun c : ι × o => ENNReal.ofReal (w c.1) • ν c.1) mask L) :
    ∃ table : (ι × o) → Finset β,
      (∀ c, table c ⊆ allowed ∧ (table c).card ≤ D) ∧
      mass - 8 * H * (∑ i, ((p i).natDegree : ℝ)) * |ρ| ≤
        continuousListMass (fun c : ι × o => ENNReal.ofReal (w c.1) • ν c.1)
          (fun c x a => rule (fun i => decide (0 ≤ (p i).eval x)) (c.2, a))
          (fun c _ => table c) := by
  classical
  let f : ℝ → (o × β) → ℝ := fun x => rule (fun i => decide (0 ≤ (p i).eval x))
  let μ : (ι × o) → Measure ℝ := fun c => ENNReal.ofReal (w c.1) • ν c.1
  haveI (c : ι × o) : IsFiniteMeasure (μ c) := ⟨by simp [μ]⟩
  have hp : ∀ c a, Integrable (fun x => f x a) (ν c) :=
    fun c => integrable_polynomial_sign_rule_component (ν c) p rule H hbound
  have hpμ : ∀ (c : ι × o) a, Integrable (fun x => f x (c.2, a)) (μ c) :=
    fun c a => (hp c.1 (c.2, a)).smul_measure ENNReal.ofReal_ne_top
  let e := 4 * H * (∑ i, ((p i).natDegree : ℝ)) * |ρ|
  have havgerror : (∑ c : ι × o, ∫ x, ∑ a,
      |f x (c.2, a) - 1 * ∫ y, f y (c.2, a) ∂ν c.1| ∂μ c) ≤ e := by
    have hsplit (j : ι) :
        (∑ b : o, ∫ x, ∑ a : β, |f x (b, a) - ∫ y, f y (b, a) ∂ν j| ∂ν j) =
          ∫ x, ∑ a : o × β, |f x a - ∫ y, f y a ∂ν j| ∂ν j := by
      simp only [Fintype.sum_prod_type]
      exact (integral_finsetSum _ (fun b _ => integrable_finsetSum _
        (fun a _ => ((hp j (b, a)).sub (integrable_const _)).abs))).symm
    calc
      _ = ∑ j, w j * ∫ x, ∑ a : o × β, |f x a - ∫ y, f y a ∂ν j| ∂ν j := by
        rw [Fintype.sum_prod_type]
        apply sum_congr rfl
        intro j _
        simp only [μ, one_mul, integral_smul_measure, ENNReal.toReal_ofReal (hw j), smul_eq_mul]
        rw [← mul_sum, hsplit]
      _ ≤ e := sign_cell_averaging_total_error_real_le ν C w hw p rule H ρ
        hbound hsupport hdiam hdom
  obtain ⟨table, htable, hsuccess'⟩ := recover_original_continuous_list allowed D μ
    (fun c x a => f x (c.2, a)) mask (fun _ _ => 1)
    (fun c a => ∫ y, f y (c.2, a) ∂ν c.1) hpμ hmaskint
    (fun _ => integrable_const _) hmask (fun _ _ => zero_le_one)
    e mass havgerror L hLmeas hL hsuccess
  refine ⟨table, htable, ?_⟩
  have he : mass - 8 * H * (∑ i, ((p i).natDegree : ℝ)) * |ρ| = mass - 2 * e := by
    dsimp [e]
    ring
  rw [he]
  exact hsuccess'

end Submission.Lib.K4OriginalLists
