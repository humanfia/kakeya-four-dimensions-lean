import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.RealGeometry
import Submission.Obl.k4_algebraic_real_jet_comparison.SheetBounds

/- Adapted from LOT session x0383 on o114, commit 2744aa271e28,
   Submission/Obl/k4_terminal_representative_atlas/RealComplexComparison.lean.
   This is the present tree's own proof, reported in its 2026-10-21T06:20Z post. -/

/-!
A local real-ball comparison of two algebraic sheets controls their difference
on an interior complex ball. All constants depend only on dimension and degree.
-/

namespace Submission.Obl.k4_pair_anchor_jet_bins

open Set Metric MvPolynomial
open Submission.Obl.k4_algebraic_real_jet_comparison
  (realEmbedding HasSheetRelation affineRelation eval_affineRelation
    affineRelation_injective totalDegree_affineRelation_le)

/-- Rescaling an algebraic sheet from a local ball gives a relation on the
standard radius-four complex ball, with the same degree. -/
theorem hasSheetRelation_local_rescale {n D : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℂ) (hP : P ≠ 0) (hdeg : P.totalDegree ≤ D)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (a : EuclideanSpace ℂ (Fin n))
    {r : ℝ} (hr : 0 < r)
    (hroot : ∀ z ∈ ball a (8*r), eval (Fin.snoc (fun i => z i) (f z)) P = 0) :
    HasSheetRelation n D (fun z => f (a + (2*r:ℂ) • z)) := by
  have hσ : (2*r:ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2:ℝ)*r ≠ 0)
  refine ⟨affineRelation (fun i => a i) (2*r:ℂ) 1 P, ?_,
    (totalDegree_affineRelation_le _ _ _ P).trans hdeg, ?_⟩
  · intro hz
    apply hP
    exact affineRelation_injective (fun i => a i) hσ one_ne_zero (by simpa using hz)
  · intro z hz
    rw [eval_affineRelation]
    have hpoint : a + (2*r:ℂ) • z ∈ ball a (8*r) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hnorm : ‖(2*r:ℂ)‖ = 2*r := by
        rw [show (2*r:ℂ) = ((2*r:ℝ):ℂ) by norm_cast,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hnorm]
      have hz4 : ‖z‖ < 4 := mem_ball_zero_iff.mp hz
      nlinarith
    simpa only [one_mul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using hroot _ hpoint

/-- Real local agreement is sufficient for the complex local norm hypothesis
in the common-anchor continuation argument. -/
theorem exists_local_real_complex_difference_bound (n D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f g : EuclideanSpace ℂ (Fin n) → ℂ)
      (P Q : MvPolynomial (Fin (n+1)) ℂ),
      P ≠ 0 → Q ≠ 0 → P.totalDegree ≤ D → Q.totalDegree ≤ D →
      ∀ a : EuclideanSpace ℝ (Fin n), ∀ r V : ℝ, 0 < r → 0 < V →
      DifferentiableOn ℂ f (ball (realEmbedding n a) (8*r)) →
      DifferentiableOn ℂ g (ball (realEmbedding n a) (8*r)) →
      (∀ z ∈ ball (realEmbedding n a) (8*r), eval (Fin.snoc (fun i => z i) (f z)) P = 0) →
      (∀ z ∈ ball (realEmbedding n a) (8*r), eval (Fin.snoc (fun i => z i) (g z)) Q = 0) →
      (∀ x : EuclideanSpace ℝ (Fin n), x ∈ closedBall a r →
        ‖f (realEmbedding n x) - g (realEmbedding n x)‖ ≤ V) →
      ∀ z ∈ closedBall (realEmbedding n a) (2*r), ‖f z - g z‖ ≤ C*V := by
  obtain ⟨E, hE⟩ := Submission.Obl.k4_algebraic_real_jet_comparison.exists_sheet_difference_degree n D
  obtain ⟨C, hC, hbound⟩ := Submission.Obl.k4_algebraic_real_jet_comparison.exists_sheet_norm_constant n E
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, ?_⟩
  intro f g P Q hP hQ hPD hQD a r V hr hV hf hg hProot hQroot hreal z hz
  let σ : ℂ := ((2*r:ℝ):ℂ)
  let T : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
    fun w => realEmbedding n a + σ • w
  let F : EuclideanSpace ℂ (Fin n) → ℂ := fun w => f (T w) - g (T w)
  have hσ : σ ≠ 0 := by dsimp [σ]; exact_mod_cast (by positivity : (2:ℝ)*r ≠ 0)
  have hσnorm : ‖σ‖ = 2*r := by
    dsimp [σ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hmap : MapsTo T (ball 0 4) (ball (realEmbedding n a) (8*r)) := by
    intro w hw
    dsimp only [T]
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hσnorm]
    have hw4 : ‖w‖ < 4 := mem_ball_zero_iff.mp hw
    nlinarith
  have hdiff : DifferentiableOn ℂ F (ball 0 4) :=
    (hf.comp (by fun_prop : DifferentiableOn ℂ T (ball 0 4)) hmap).sub
      (hg.comp (by fun_prop : DifferentiableOn ℂ T (ball 0 4)) hmap)
  have hrel : HasSheetRelation n E F := by
    simpa [F, T, σ] using hE _ _
      (hasSheetRelation_local_rescale P hP hPD f _ hr hProot)
      (hasSheetRelation_local_rescale Q hQ hQD g _ hr hQroot)
  have hbase (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ (1:ℝ)/2) :
      ‖F (realEmbedding n x)‖ ≤ V := by
    have heq : T (realEmbedding n x) = realEmbedding n (a + (2*r) • x) := by
      ext i
      simp [T, σ, realEmbedding]
    have hx' : a + (2*r) • x ∈ closedBall a r := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2*r)]
      nlinarith
    simpa only [F, heq] using hreal _ hx'
  let u : EuclideanSpace ℂ (Fin n) := σ⁻¹ • (z - realEmbedding n a)
  have hu : ‖u‖ ≤ 1 := by
    dsimp [u]
    rw [norm_smul, norm_inv, hσnorm, inv_mul_eq_div]
    apply (div_le_one (by positivity : 0 < 2*r)).mpr
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hback : T u = z := by
    dsimp [T, u]
    rw [smul_smul, mul_inv_cancel₀ hσ, one_smul, add_sub_cancel]
  have hh := hbound F hrel hdiff V hV hbase u hu
  simpa only [F, hback] using hh

end Submission.Obl.k4_pair_anchor_jet_bins
