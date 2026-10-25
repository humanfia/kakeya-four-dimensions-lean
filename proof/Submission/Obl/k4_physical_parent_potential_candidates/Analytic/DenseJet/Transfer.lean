-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/DenseJet/Transfer.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/DenseJet/Transfer.lean.
-- Only the source value-norming declarations used here are retained; earlier provenance is preserved.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/DenseJet/Transfer.lean
-- Earlier source attributions below are retained.
import Mathlib

/-!
# Transferring directional tests

Elementary estimates used to move directional tests from the direction of a trajectory to a
fixed nearby direction, and from one base point to another:

* `iteratedDeriv_line_eq`: the `k`-th derivative along the line `u + t v` at `t = 0` is the
  `k`-th Fréchet derivative evaluated on `v, …, v`;
* `abs_diagonal_sub_le`: changing the direction changes a diagonal `k`-linear value by at most
  `k ‖T‖ max(‖p‖, ‖v‖)^(k-1) ‖p - v‖`;
* `norm_iteratedFDeriv_sub_le`: on a convex set, the `k`-th derivative moves by at most the
  supremum of the `(k+1)`-st derivative times the displacement.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet.Transfer

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The jet of a real affine slice is the diagonal Fréchet jet. -/
theorem iteratedDeriv_line_eq {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) {u : E} (hu : u ∈ U) (v : E) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => f (u + t • v)) 0 = iteratedFDeriv ℝ k f u (fun _ => v) := by
  let g : E → ℝ := fun z => f (u + z)
  let W : Set E := (fun z : E => u + z) ⁻¹' U
  let T : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hW : IsOpen W := hU.preimage (by fun_prop)
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g W :=
    hf.comp (by fun_prop) (fun z hz => hz)
  have hWT : IsOpen (T ⁻¹' W) := hW.preimage T.continuous
  have h0 : T 0 ∈ W := by simpa [T, W] using hu
  have hid := T.iteratedFDerivWithin_comp_right hg hW.uniqueDiffOn hWT.uniqueDiffOn
    h0 (i := k) (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  rw [iteratedFDerivWithin_of_isOpen k hWT h0, iteratedFDerivWithin_of_isOpen k hW h0] at hid
  have hshift : iteratedFDeriv ℝ k g (T 0) = iteratedFDeriv ℝ k f u := by
    simpa [g, T] using iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) k u 0
  rw [hshift] at hid
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ k (g ∘ T) 0 (fun _ => 1) = _
  rw [hid]
  simp [T]

/-- Changing the direction of a diagonal multilinear value. -/
theorem abs_diagonal_sub_le {k : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ)
    (p v : E) :
    |T (fun _ => p) - T (fun _ => v)| ≤ ‖T‖ * k * max ‖p‖ ‖v‖ ^ (k - 1) * ‖p - v‖ := by
  have h := T.norm_image_sub_le (fun _ => p) (fun _ => v)
  rw [Real.norm_eq_abs, Fintype.card_fin] at h
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h0 : T (fun _ => p) = T (fun _ => v) := by
      congr 1
      funext i
      exact i.elim0
    rw [h0, sub_self, abs_zero]
    simp
  · have hnp : ‖(fun _ : Fin k => p)‖ = ‖p‖ := by
      haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
      exact pi_norm_const p
    have hnv : ‖(fun _ : Fin k => v)‖ = ‖v‖ := by
      haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
      exact pi_norm_const v
    have hnd : ‖(fun _ : Fin k => p) - (fun _ : Fin k => v)‖ = ‖p - v‖ := by
      haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
      have : (fun _ : Fin k => p) - (fun _ : Fin k => v) = fun _ : Fin k => p - v := rfl
      rw [this]
      exact pi_norm_const (p - v)
    rw [hnp, hnv, hnd] at h
    exact h

/-- On a convex open set where the `(k+1)`-st derivative is bounded by `M`, the `k`-th
derivative is `M`-Lipschitz. -/
theorem norm_iteratedFDeriv_sub_le {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U) (k : ℕ) {M : ℝ}
    (hM : ∀ x ∈ U, ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ M) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖iteratedFDeriv ℝ k f y - iteratedFDeriv ℝ k f x‖ ≤ M * ‖y - x‖ := by
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z := by
    intro z hz
    have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f z := hf.contDiffAt (hU.mem_nhds hz)
    exact hcd.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top k)
  apply hconv.norm_image_sub_le_of_norm_fderiv_le (fun z hz => hdiff z hz) _ hx hy
  intro z hz
  rw [norm_fderiv_iteratedFDeriv]
  exact hM z hz

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet.Transfer
