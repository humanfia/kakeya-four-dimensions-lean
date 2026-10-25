-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit cc2492748f08.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/SubpowerLikelihood.lean.
import Submission.Obl.k4_finite_affine_parent_sources.LikelihoodPreparation

/-! A single cutoff balances likelihood deletion against a vanishing
power of the resolution. This makes the entropy preparation quantitative
along the guarded diagonal, without replacing any reference law. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

open Finset Filter
open scoped Topology
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-- If `B` bounds information plus its unit negative-part correction,
the cutoff exponent `sqrt (B / log N)` bounds both the discarded mass
and the exponent of the retained likelihood multiplier. -/
theorem likelihood_cutoff_balance {N B : ℝ} (hN : 1 < N) (hB : 0 < B) :
    0 < Real.sqrt (B / Real.log N) ∧
      B / (Real.sqrt (B / Real.log N) * Real.log N) = Real.sqrt (B / Real.log N) ∧
      Real.exp (Real.sqrt (B / Real.log N) * Real.log N) =
        N ^ Real.sqrt (B / Real.log N) := by
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hr : 0 < B / Real.log N := div_pos hB hlog
  have hs : 0 < Real.sqrt (B / Real.log N) := Real.sqrt_pos.mpr hr
  refine ⟨hs, ?_, ?_⟩
  · apply (div_eq_iff (mul_pos hs hlog).ne').mpr
    calc
      B = (B / Real.log N) * Real.log N := (div_mul_cancel₀ B hlog.ne').symm
      _ = Real.sqrt (B / Real.log N) ^ 2 * Real.log N := by rw [Real.sq_sqrt hr.le]
      _ = _ := by ring
  · rw [Real.rpow_def_of_pos (by linarith : 0 < N)]
    congr 1
    ring

/-- The balanced likelihood preparation at a single sample. The returned
joint bounds continue to refer to the original probability law. -/
theorem finite_balanced_likelihood
    {Ω H Z : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype H] [DecidableEq H]
    [Fintype Z] [DecidableEq Z]
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e) (hP1 : ∑ e, P e = 1)
    (coarse fine : Ω → H) (parent : H → H) (palette : Ω → Z)
    (hrefine : ∀ e, coarse e = parent (fine e))
    (N B : ℝ) (hN : 1 < N) (hB : 0 < B)
    (hinfo : negCondEnt P palette fine - negCondEnt P palette coarse + 1 ≤ B) :
    ∃ S : Finset Ω,
      1 - Real.sqrt (B / Real.log N) ≤ ∑ e ∈ S, P e ∧
      ∀ Q : Ω → ℝ, (∀ e, Q e ≤ if e ∈ S then P e else 0) → ∀ h z,
        fiberMass Q (fun e => (fine e, palette e)) (h, z) ≤
          N ^ Real.sqrt (B / Real.log N) * fiberMass P fine h *
            historyPalette P coarse palette (parent h) z := by
  obtain ⟨hs, hbalance, hpow⟩ := likelihood_cutoff_balance hN hB
  have hθ : 0 < Real.sqrt (B / Real.log N) * Real.log N :=
    mul_pos hs (Real.log_pos hN)
  obtain ⟨S, hmass, hcap⟩ := finite_prepared_likelihood P hP hP1
    coarse fine parent palette hrefine _ hθ
  refine ⟨S, ?_, ?_⟩
  · have hdiv := div_le_div_of_nonneg_right hinfo hθ.le
    rw [hbalance] at hdiv
    exact (sub_le_sub_left hdiv 1).trans hmass
  · simpa only [hpow] using hcap

/-- Vanishing relative information produces a vanishing deletion budget
and a subpower likelihood multiplier, using the same exponent for both. -/
theorem balanced_likelihood_subpower
    (N B : ℕ → ℝ) (hN : ∀ k, 1 < N k)
    (hsmall : Tendsto (fun k => B k / Real.log (N k)) atTop (𝓝 0)) :
    Tendsto (fun k => Real.sqrt (B k / Real.log (N k))) atTop (𝓝 0) ∧
      (∀ k, 1 ≤ N k ^ Real.sqrt (B k / Real.log (N k))) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        N k ^ Real.sqrt (B k / Real.log (N k)) ≤ N k ^ ε := by
  have ht : Tendsto (fun k => Real.sqrt (B k / Real.log (N k))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hsmall)
  refine ⟨ht, ?_, ?_⟩
  · intro k
    exact Real.one_le_rpow (hN k).le (Real.sqrt_nonneg _)
  · intro ε hε
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with k hk
    exact Real.rpow_le_rpow_of_exponent_le (hN k).le hk.le

end

end Submission.Obl.k4_finite_affine_parent_sources
