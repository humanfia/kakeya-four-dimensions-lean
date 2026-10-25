import Submission.Obl.k4_pair_anchor_jet_bins.Interface

namespace Submission.Obl.k4_pair_anchor_jet_bins

open Set Metric Filter
open scoped Topology
open Submission.Lib.K4QuadraticSheets

/- Adapted from LOT session x0525 on o158,
   Submission/Obl/k4_matched_pair_representative_realization/PathBranches.lean,
   as reported in its 2026-10-21T05:52Z post. All source is this tree's own work. -/

/-- A continuous nonzero square root of a holomorphic function is holomorphic. -/
theorem differentiableAt_of_sq {f g : E3 → ℂ} {z : E3}
    (hf : ContinuousAt f z) (hf0 : f z ≠ 0) (hg : DifferentiableAt ℂ g z)
    (heq : (fun x => f x ^ 2) =ᶠ[𝓝 z] g) : DifferentiableAt ℂ f z := by
  have hc : (2 : ℂ) * f z ≠ 0 := mul_ne_zero (by norm_num) hf0
  have hp : HasDerivAt (fun w : ℂ => w ^ 2) (2 * f z) (f z) := by
    simpa using (hasDerivAt_id (f z)).fun_pow 2
  exact (hp.hasFDerivAt.of_comp_of_leftInverse hf hg.hasFDerivAt heq
    (f'symm := ContinuousLinearMap.toSpanSingleton ℂ ((2 * f z)⁻¹))
    (by intro w; dsimp; field_simp)).differentiableAt

/-- Consecutive segment tubes share a star centre, so have no monodromy. -/
theorem simplyConnected_broken_tube (a b c : E3) {r : ℝ} (hr : 0 < r) :
    IsSimplyConnected (thickening r (segment ℝ a b ∪ segment ℝ b c)) := by
  have hstar : StarConvex ℝ b (thickening r (segment ℝ a b ∪ segment ℝ b c)) := by
    rw [thickening_union]
    exact (((convex_segment a b).thickening r).starConvex
      (self_subset_thickening hr _ (right_mem_segment ℝ a b))).union
      (((convex_segment b c).thickening r).starConvex
        (self_subset_thickening hr _ (left_mem_segment ℝ b c)))
  have hb : b ∈ thickening r (segment ℝ a b ∪ segment ℝ b c) :=
    self_subset_thickening hr _ (Or.inl (right_mem_segment ℝ a b))
  have := hstar.contractibleSpace ⟨b, hb⟩
  change SimplyConnectedSpace _
  infer_instance

/-- Nonvanishing of the discriminant on a broken tube provides an analytic square root there. -/
theorem sqrt_on_broken_tube (P : MvPolynomial (Fin 4) ℂ) (a b c : E3)
    {r : ℝ} (hr : 0 < r)
    (hd0 : ∀ z ∈ thickening r (segment ℝ a b ∪ segment ℝ b c),
      qdisc P (fun j => z j) ≠ 0) :
    ∃ S : E3 → ℂ, AnalyticOnNhd ℂ S (thickening r (segment ℝ a b ∪ segment ℝ b c)) ∧
      ∀ z ∈ thickening r (segment ℝ a b ∪ segment ℝ b c),
        S z ^ 2 = qdisc P (fun j => z j) ∧ qdisc P (fun j => z j) ≠ 0 := by
  let U := thickening r (segment ℝ a b ∪ segment ℝ b c)
  let g : E3 → ℂ := fun z => qdisc P (fun j => z j)
  have hUo : IsOpen U := isOpen_thickening
  have hgc : ContinuousOn g U := (differentiable_qdisc P).continuous.continuousOn
  obtain ⟨S, hSc, hsq⟩ := Complex.exists_continuousOn_pow_eq
    (simplyConnected_broken_tube a b c hr) hUo hgc
    (by rintro ⟨z, hz, heq⟩; exact hd0 z hz heq) (n := 2) (by norm_num)
  have hSa : AnalyticOnNhd ℂ S U := by
    intro z hz
    have hd : g z ≠ 0 := hd0 z hz
    have hS0 : S z ≠ 0 := by
      intro h0
      apply hd
      rw [← hsq z, h0]
      norm_num
    let T : E3 → ℂ := fun y => rotSqrt (g z) (S z) (g y)
    have hTa : AnalyticAt ℂ T z := by
      change AnalyticAt ℂ (fun y => (S z) * (g y / g z) ^ (1 / 2 : ℂ)) z
      exact analyticAt_const.mul (((analyticAt_qdisc P z).div analyticAt_const hd).cpow
        analyticAt_const (by change g z / g z ∈ Complex.slitPlane; simp [hd]))
    have hTz : T z = S z := by simp [T, rotSqrt, hd]
    have hsum0 : S z + T z ≠ 0 := by
      rw [hTz, ← two_mul]
      exact mul_ne_zero (by norm_num) hS0
    have hnear : ∀ᶠ y in 𝓝 z, S y + T y ≠ 0 :=
      ((hSc.continuousAt (hUo.mem_nhds hz)).add hTa.continuousAt).eventually_ne hsum0
    apply hTa.congr
    filter_upwards [hnear] with y hy
    have hT : T y ^ 2 = g y := rotSqrt_sq hd (hsq z) (g y)
    have hfac : (T y - S y) * (S y + T y) = 0 := by
      linear_combination hT - hsq y
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hy)
  exact ⟨S, hSa, fun z hz => ⟨hsq z, hd0 z hz⟩⟩

end Submission.Obl.k4_pair_anchor_jet_bins
