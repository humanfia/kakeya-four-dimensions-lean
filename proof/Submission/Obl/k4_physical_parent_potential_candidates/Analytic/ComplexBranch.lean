-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/ComplexBranch.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/ComplexBranch.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/ComplexBranch.lean
-- Earlier source attributions below are retained.
import Mathlib
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.SimpleRoot

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

lemma complex_sqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  simp [Complex.sqrt]

/-- Near a positive real number squared, the principal square root has the
expected Lipschitz bound with no dependence on polynomial coefficients. -/
theorem complex_sqrt_near_positive (z : ℂ) {β : ℝ} (hβ : 0 < β) :
    ‖Complex.sqrt z - (β : ℂ)‖ ≤ ‖z - (β : ℂ) ^ 2‖ / β := by
  have hre : 0 ≤ (Complex.sqrt z).re := by
    rw [Complex.sqrt, Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hdenre : β ≤ (Complex.sqrt z + (β : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hden : β ≤ ‖Complex.sqrt z + (β : ℂ)‖ :=
    hdenre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hid : (Complex.sqrt z - (β : ℂ)) * (Complex.sqrt z + (β : ℂ)) =
      z - (β : ℂ) ^ 2 := by
    linear_combination complex_sqrt_sq z
  have hnorm : ‖Complex.sqrt z - (β : ℂ)‖ * ‖Complex.sqrt z + (β : ℂ)‖ =
      ‖z - (β : ℂ) ^ 2‖ := by rw [← norm_mul, hid]
  exact (le_div_iff₀ hβ).mpr
    ((mul_le_mul_of_nonneg_left hden (norm_nonneg _)).trans_eq hnorm)

/-- A uniform comparison margin keeps the square root in the slit plane and
keeps the stable root formula's denominator uniformly nonzero. -/
theorem stable_quadratic_complex_margins (a b c : ℂ) {β : ℝ} (hβ : 0 < β)
    (hb : ‖b - (β : ℂ)‖ ≤ β / 4)
    (hdisc : ‖(b ^ 2 - 4 * a * c) - (β : ℂ) ^ 2‖ ≤ β ^ 2 / 4) :
    0 < (b ^ 2 - 4 * a * c).re ∧
      β ≤ ‖b + Complex.sqrt (b ^ 2 - 4 * a * c)‖ ∧
      β / 2 ≤ ‖Complex.sqrt (b ^ 2 - 4 * a * c)‖ ∧
      ‖Complex.sqrt (b ^ 2 - 4 * a * c)‖ ≤ 2 * β := by
  let Δ := b ^ 2 - 4 * a * c
  have hroot : ‖Complex.sqrt Δ - (β : ℂ)‖ ≤ β / 4 := by
    apply (complex_sqrt_near_positive Δ hβ).trans
    apply (div_le_iff₀ hβ).mpr
    nlinarith [hdisc]
  have hbre : |b.re - β| ≤ β / 4 := by
    have h : |b.re - β| ≤ ‖b - (β : ℂ)‖ := by
      simpa using Complex.abs_re_le_norm (b - (β : ℂ))
    exact h.trans hb
  have hrre : |(Complex.sqrt Δ).re - β| ≤ β / 4 := by
    have h : |(Complex.sqrt Δ).re - β| ≤ ‖Complex.sqrt Δ - (β : ℂ)‖ := by
      simpa using Complex.abs_re_le_norm (Complex.sqrt Δ - (β : ℂ))
    exact h.trans hroot
  have hΔre : |Δ.re - β ^ 2| ≤ β ^ 2 / 4 := by
    have h : |Δ.re - β ^ 2| ≤ ‖Δ - (β : ℂ) ^ 2‖ := by
      have hRe : (Δ - (β : ℂ) ^ 2).re = Δ.re - β ^ 2 := by
        rw [pow_two, Complex.sub_re, Complex.mul_re]
        simp [pow_two]
      have h' := Complex.abs_re_le_norm (Δ - (β : ℂ) ^ 2)
      rw [hRe] at h'
      exact h'
    exact h.trans hdisc
  have hbparts := abs_le.mp hbre
  have hrparts := abs_le.mp hrre
  have hΔparts := abs_le.mp hΔre
  refine ⟨by dsimp [Δ] at *; nlinarith [sq_pos_of_pos hβ], ?_, ?_, ?_⟩
  · have hle : β ≤ (b + Complex.sqrt Δ).re := by
      simp only [Complex.add_re]
      linarith
    exact hle.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  · have hle : β / 2 ≤ (Complex.sqrt Δ).re := by linarith
    exact hle.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  · have htriangle : ‖Complex.sqrt Δ‖ ≤ ‖Complex.sqrt Δ - (β : ℂ)‖ + β := by
      calc
        ‖Complex.sqrt Δ‖ = ‖(Complex.sqrt Δ - (β : ℂ)) + (β : ℂ)‖ := by
          congr 1
          ring
        _ ≤ ‖Complex.sqrt Δ - (β : ℂ)‖ + ‖(β : ℂ)‖ := norm_add_le _ _
        _ = ‖Complex.sqrt Δ - (β : ℂ)‖ + β := by simp [abs_of_pos hβ]
    linarith

/-- The complex stable-root formula defines a holomorphic simple branch on any
domain with the fixed comparison margins. It covers the linear case as well. -/
theorem holomorphic_stable_quadratic_branch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (a : ℂ) (b c : E → ℂ) (hb : DifferentiableOn ℂ b U)
    (hc : DifferentiableOn ℂ c U) {β : ℝ} (hβ : 0 < β)
    (hbclose : ∀ z ∈ U, ‖b z - (β : ℂ)‖ ≤ β / 4)
    (hdisc : ∀ z ∈ U, ‖((b z) ^ 2 - 4 * a * c z) - (β : ℂ) ^ 2‖ ≤ β ^ 2 / 4) :
    ∃ f : E → ℂ, DifferentiableOn ℂ f U ∧
      ∀ z ∈ U, c z + b z * f z + a * (f z) ^ 2 = 0 ∧
        β / 2 ≤ ‖b z + 2 * a * f z‖ ∧ ‖b z + 2 * a * f z‖ ≤ 2 * β ∧
        ‖f z‖ ≤ 2 * ‖c z‖ / β := by
  let Δ : E → ℂ := fun z => (b z) ^ 2 - 4 * a * c z
  let f : E → ℂ := fun z => -2 * c z / (b z + Complex.sqrt (Δ z))
  have hmargins (z : E) (hz : z ∈ U) :=
    stable_quadratic_complex_margins a (b z) (c z) hβ (hbclose z hz) (hdisc z hz)
  have hden (z : E) (hz : z ∈ U) : b z + Complex.sqrt (Δ z) ≠ 0 := by
    exact norm_pos_iff.mp (hβ.trans_le (hmargins z hz).2.1)
  have hΔ : DifferentiableOn ℂ Δ U := (hb.pow 2).sub (hc.const_mul _)
  have hsqrt : DifferentiableOn ℂ (fun z => Complex.sqrt (Δ z)) U := by
    apply Complex.differentiableOn_sqrt.comp hΔ
    intro z hz
    exact Or.inl (hmargins z hz).1
  have hdiff : DifferentiableOn ℂ f U := by
    intro z hz
    dsimp [f]
    simp only [div_eq_mul_inv]
    have hcz := hc z hz
    have hbz := hb z hz
    have hsz := hsqrt z hz
    have hdenz := hden z hz
    fun_prop
  refine ⟨f, hdiff, ?_⟩
  intro z hz
  obtain ⟨hroot, hderiv⟩ := stable_quadratic_root_formula a (b z) (c z)
    (Complex.sqrt (Δ z)) (complex_sqrt_sq _) (hden z hz)
  refine ⟨hroot, ?_, ?_, ?_⟩
  · change β / 2 ≤ ‖b z + 2 * a * (-2 * c z / (b z + Complex.sqrt (Δ z)))‖
    rw [hderiv]
    exact (hmargins z hz).2.2.1
  · change ‖b z + 2 * a * (-2 * c z / (b z + Complex.sqrt (Δ z)))‖ ≤ 2 * β
    rw [hderiv]
    exact (hmargins z hz).2.2.2
  · dsimp [f]
    rw [norm_div, norm_mul]
    norm_num
    exact div_le_div_of_nonneg_left (by positivity) hβ (hmargins z hz).2.1

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
