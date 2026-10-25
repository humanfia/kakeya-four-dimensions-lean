-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/PhysicalDirection.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/PhysicalDirection.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/PhysicalDirection.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.DenseJet.Rational
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.RobustTests

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MvPolynomial MeasureTheory
open scoped ContDiff ENNReal

/-- Directions with first coordinate one need a shorter parameter window
before applying norming on the radius-four branch domain. -/
theorem small_line_direction {A : ℝ} (hA : 2 ≤ A) {u p : Base}
    (hu : u ∈ closedBall (0 : Base) 1) (hp : ‖p‖ ≤ A) :
    ‖u‖ + 4 * ‖(8 * A)⁻¹ • p‖ < 4 := by
  have hA0 : 0 < A := by linarith
  have hv : ‖(8 * A)⁻¹ • p‖ ≤ 1 / 8 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
    apply (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq
    field_simp
  have hu' : ‖u‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hu
  linarith

/-- Undo the short parameter window in a diagonal jet. One fixed power
pays for every order through six. -/
theorem abs_diagonal_jet_le_of_small_line {A B : ℝ} (hA : 2 ≤ A) (hB : 0 ≤ B)
    {f : Base → ℝ} (hf : ContDiffOn ℝ ∞ f (ball 0 4))
    {u : Base} (hu : u ∈ closedBall (0 : Base) 1) (p : Base)
    (k : ℕ) (hk : k ≤ 6)
    (hline : |iteratedDeriv k (fun t : ℝ => f (u + t • ((8 * A)⁻¹ • p))) 0| ≤ B) :
    |iteratedFDeriv ℝ k f u (fun _ => p)| ≤ A ^ 24 * B := by
  have hA0 : 0 < A := by linarith
  have hscale0 : 8 * A ≠ 0 := by positivity
  let v : Base := (8 * A)⁻¹ • p
  have hv : (8 * A) • v = p := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hscale0, one_smul]
  have hu4 : u ∈ ball (0 : Base) 4 := by
    rw [mem_ball, dist_zero_right]
    have hh : ‖u‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hu
    linarith
  have hjet : |iteratedFDeriv ℝ k f u (fun _ => v)| ≤ B := by
    rw [← DenseJet.Transfer.iteratedDeriv_line_eq isOpen_ball hf hu4 v k]
    exact hline
  have heq : iteratedFDeriv ℝ k f u (fun _ => p) =
      (8 * A) ^ k * iteratedFDeriv ℝ k f u (fun _ => v) := by
    calc
      _ = iteratedFDeriv ℝ k f u (fun _ => (8 * A) • v) := by rw [hv]
      _ = _ := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
          (iteratedFDeriv ℝ k f u).map_smul_univ (fun _ : Fin k => 8 * A) (fun _ => v)
  have hsmall : 8 * A ≤ A ^ 4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hA 3
    norm_num at hh
    nlinarith [mul_le_mul_of_nonneg_right hh hA0.le]
  have hpower : (8 * A) ^ k ≤ A ^ 24 := by
    calc
      _ ≤ (A ^ 4) ^ k := pow_le_pow_left₀ (by positivity) hsmall k
      _ = A ^ (4 * k) := (pow_mul _ _ _).symm
      _ ≤ A ^ 24 := pow_le_pow_right₀ (by linarith) (by omega)
  rw [heq, abs_mul, abs_of_nonneg (pow_nonneg (by positivity) k)]
  exact (mul_le_mul_of_nonneg_left hjet (by positivity)).trans
    (mul_le_mul_of_nonneg_right hpower hB)

/-- The rational-branch line estimate in the physical direction used by
the sampled certificate. The norming constants are fixed before all data. -/
theorem directional_jet_bound_rational_physical (hR : DenseJet.SheetRemezAssertion) (D : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ D → U.totalDegree ≤ D →
      V.totalDegree ≤ D → W.totalDegree ≤ D →
      ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * s z) →
      ContDiffOn ℂ ∞ F (ball 0 4) → ContDiffOn ℝ ∞ f (ball 0 4) →
      (∀ x : Base, ‖x‖ < 4 → F (DenseJet.realSlice x) = (f x : ℂ)) →
      ∀ (A : ℝ), 2 ≤ A → ∀ (u p : Base) (α β : ℝ),
      u ∈ closedBall (0 : Base) 1 → ‖p‖ ≤ A →
      eval (fun i => (DenseJet.realSlice u) i) W ≠ 0 →
      ∀ (S : Set ℝ) (θ ε : ℝ), MeasurableSet S → S ⊆ Icc (-1) 1 → 0 < θ → θ ≤ 1 →
        0 ≤ ε → ENNReal.ofReal θ ≤ volume S →
        (∀ t ∈ S, |f (u + t • ((8 * A)⁻¹ • p)) - α - β * t| ≤ ε) →
        ∀ k : ℕ, 2 ≤ k → k ≤ 6 →
          |iteratedFDeriv ℝ k f u (fun _ => p)| ≤ K * θ ^ (-C) * A ^ 24 * ε := by
  obtain ⟨K, C, hK, hC, hline⟩ := DenseJet.Line.directional_jet_bound_rational hR D
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW s F f hroot hrep hF hf hmatch A hA u p α β hu hp hWa
    S θ ε hS hSsub hθ hθ1 hε hvol hbound k hk2 hk6
  have hh := hline Δ U V W hΔ hU hV hW s F f hroot hrep hF hmatch
    u ((8 * A)⁻¹ • p) α β (small_line_direction hA hu hp) hWa
    S θ ε hS hSsub hθ hθ1 hε hvol hbound k hk2 hk6 0 (by norm_num)
  have hphysical := abs_diagonal_jet_le_of_small_line hA (by positivity) hf hu p k hk6 hh
  exact hphysical.trans_eq (by ring)

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
