-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/QuadraticFitNorming.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/QuadraticFitNorming.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/QuadraticFitNorming.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.LinePolynomialError
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.PhysicalDirection
import Submission.Obl.k4_algebraic_sheet_remez.PolynomialDerivatives

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MvPolynomial MeasureTheory
open scoped ContDiff ENNReal

/-- Use the accepted polynomial derivative identity to remove a quadratic
fit from every derivative of order at least three. -/
theorem iteratedDeriv_quadratic_fit (α β γ : ℝ) (k : ℕ) (hk : 3 ≤ k) :
    iteratedDeriv k (fun t : ℝ => α + β * t + γ * t ^ 2) = 0 := by
  let P : Polynomial ℝ := Polynomial.C α + Polynomial.C β * Polynomial.X +
    Polynomial.C γ * Polynomial.X ^ 2
  have hP : (fun t : ℝ => α + β * t + γ * t ^ 2) = fun t => P.eval t := by
    funext t
    simp [P]
  have hP3 : (Polynomial.derivative^[3]) P = 0 := by simp [P, Function.iterate_succ_apply']
  have hPk : (Polynomial.derivative^[k]) P = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
    rw [Function.iterate_add_apply, hP3]
    simp
  rw [hP, Submission.Obl.k4_algebraic_sheet_remez.iteratedDeriv_polynomial_eval, hPk]
  funext t
  simp

/-- Long witnesses for a quadratic line fit bound the third through sixth
line derivatives of a rational quadratic-extension branch at the anchor. -/
theorem quadratic_fit_line_norming (hR : DenseJet.SheetRemezAssertion) (D : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ D → U.totalDegree ≤ D →
      V.totalDegree ≤ D → W.totalDegree ≤ D →
      ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * s z) →
      ContDiffOn ℂ ∞ F (ball 0 4) → ContDiffOn ℝ ∞ f (ball 0 4) →
      (∀ x : Base, ‖x‖ < 4 → F (DenseJet.realSlice x) = (f x : ℂ)) →
      ∀ (u v : Base) (α β γ : ℝ), ‖u‖ + 4 * ‖v‖ < 4 →
      eval (fun i => (DenseJet.realSlice u) i) W ≠ 0 →
      ∀ (S : Set ℝ) (θ ε : ℝ), MeasurableSet S → S ⊆ Icc (-1) 1 → 0 < θ → θ ≤ 1 →
        0 ≤ ε → ENNReal.ofReal θ ≤ volume S →
        (∀ t ∈ S, |f (u + t • v) - (α + β * t + γ * t ^ 2)| ≤ ε) →
        ∀ k : ℕ, 3 ≤ k → k ≤ 6 →
          |iteratedDeriv k (fun t : ℝ => f (u + t • v)) 0| ≤ K * θ ^ (-C) * ε := by
  obtain ⟨K, C, hK, hC, hline⟩ := DenseJet.Line.line_jet_bound hR (8 * (D + 2) + 2)
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW s F f hroot hrep hF hf hmatch u v α β γ huv hWa
    S θ ε hS hSsub hθ hθ1 hε hvol hbound k hk3 hk6
  let Q : MvPolynomial (Fin 1) ℂ := MvPolynomial.C (α : ℂ) +
    MvPolynomial.C (β : ℂ) * X 0 + MvPolynomial.C (γ : ℂ) * (X 0) ^ 2
  have hQ : Q.totalDegree ≤ 2 := by
    have hlinear : (MvPolynomial.C (β : ℂ) * (X 0 : MvPolynomial (Fin 1) ℂ)).totalDegree ≤ 1 :=
      (totalDegree_mul _ _).trans (by simp)
    have hsquare : ((X 0 : MvPolynomial (Fin 1) ℂ) ^ 2).totalDegree ≤ 2 :=
      (totalDegree_pow _ _).trans (by simp)
    exact (totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le (by simp) (hlinear.trans (by omega))))
      ((totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hsquare)))
  have hpt : ∀ ζ : ℂ, ‖ζ‖ < 4 → ‖DenseJet.realSlice u + ζ • DenseJet.realSlice v‖ < 4 := by
    intro ζ hζ
    calc
      _ ≤ ‖DenseJet.realSlice u‖ + ‖ζ‖ * ‖DenseJet.realSlice v‖ := by
        simpa only [norm_smul] using norm_add_le (DenseJet.realSlice u) (ζ • DenseJet.realSlice v)
      _ ≤ ‖u‖ + 4 * ‖v‖ := by
        rw [DenseJet.norm_realSlice_apply, DenseJet.norm_realSlice_apply]
        gcongr
      _ < 4 := huv
  have hmap : MapsTo (fun z : EuclideanSpace ℂ (Fin 1) =>
      DenseJet.realSlice u + z 0 • DenseJet.realSlice v) (ball 0 4) (ball 0 4) := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz ⊢
    exact hpt (z 0) ((PiLp.norm_apply_le z 0).trans_lt hz)
  have hrel := hasSheetRelation_polynomial_line_error D 2 Δ U V W hΔ hU hV hW
    (ball 0 4) s F hroot hrep (DenseJet.realSlice u) (DenseJet.realSlice v) Q hQ hWa hmap
  let G : ℂ → ℂ := fun ζ => F (DenseJet.realSlice u + ζ • DenseJet.realSlice v) -
    ((α : ℂ) + (β : ℂ) * ζ + (γ : ℂ) * ζ ^ 2)
  let g : ℝ → ℝ := fun t => f (u + t • v) - (α + β * t + γ * t ^ 2)
  have hrelG : k4_algebraic_real_jet_comparison.HasSheetRelation 1 (8 * (D + 2) + 2)
      (fun z : EuclideanSpace ℂ (Fin 1) => G (z 0)) := by
    simpa only [Q, G, map_add, map_mul, eval_C, eval_X, map_pow] using hrel
  have hG : ContDiffOn ℂ ∞ G (ball 0 4) := by
    have hlin : ContDiff ℂ ∞ (fun ζ : ℂ => DenseJet.realSlice u + ζ • DenseJet.realSlice v) := by fun_prop
    have hmaps : MapsTo (fun ζ : ℂ => DenseJet.realSlice u + ζ • DenseJet.realSlice v)
        (ball 0 4) (ball 0 4) := by
      intro ζ hζ
      simpa only [mem_ball, dist_zero_right] using
        hpt ζ (by simpa only [mem_ball, dist_zero_right] using hζ)
    exact (hF.comp hlin.contDiffOn hmaps).sub (by fun_prop)
  have hGg : ∀ t : ℝ, |t| < 4 → G t = (g t : ℂ) := by
    intro t ht
    have heq : DenseJet.realSlice u + (t : ℂ) • DenseJet.realSlice v =
        DenseJet.realSlice (u + t • v) := by
      ext i
      simp [DenseJet.realSlice_apply]
    have hnorm : ‖u + t • v‖ < 4 := by
      rw [← DenseJet.norm_realSlice_apply, ← heq]
      exact hpt t (by simpa using ht)
    simp only [G, g, heq, hmatch _ hnorm]
    push_cast
    rfl
  have hnormed := hline G g hrelG hG hGg S θ ε hS hSsub hθ hθ1 hε hvol hbound
    k hk6 0 (by norm_num)
  have hu4 : u ∈ ball (0 : Base) 4 := by
    rw [mem_ball, dist_zero_right]
    nlinarith [norm_nonneg v]
  have hψ : ContDiffAt ℝ k (fun t : ℝ => f (u + t • v)) 0 := by
    have hfu : ContDiffAt ℝ k f u :=
      (hf.contDiffAt (isOpen_ball.mem_nhds hu4)).of_le (by simp)
    have hfu' : ContDiffAt ℝ k f (u + (0 : ℝ) • v) := by simpa using hfu
    exact hfu'.comp 0 (show ContDiffAt ℝ k (fun t : ℝ => u + t • v) 0 from by fun_prop)
  have hfit : ContDiffAt ℝ k (fun t : ℝ => α + β * t + γ * t ^ 2) 0 := by fun_prop
  have hg : g = (fun t : ℝ => f (u + t • v)) - (fun t : ℝ => α + β * t + γ * t ^ 2) := rfl
  rw [hg, iteratedDeriv_sub hψ hfit, iteratedDeriv_quadratic_fit α β γ k hk3] at hnormed
  simpa using hnormed

/-- The quadratic-fit estimate directly in the physical directions of the
sampled residual tests. All parameter shortening costs use the same A^24. -/
theorem quadratic_fit_physical_norming (hR : DenseJet.SheetRemezAssertion) (D : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ D → U.totalDegree ≤ D →
      V.totalDegree ≤ D → W.totalDegree ≤ D →
      ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * s z) →
      ContDiffOn ℂ ∞ F (ball 0 4) → ContDiffOn ℝ ∞ f (ball 0 4) →
      (∀ x : Base, ‖x‖ < 4 → F (DenseJet.realSlice x) = (f x : ℂ)) →
      ∀ (A : ℝ), 2 ≤ A → ∀ (u p : Base) (α β γ : ℝ),
      u ∈ closedBall (0 : Base) 1 → ‖p‖ ≤ A →
      eval (fun i => (DenseJet.realSlice u) i) W ≠ 0 →
      ∀ (S : Set ℝ) (θ ε : ℝ), MeasurableSet S → S ⊆ Icc (-1) 1 → 0 < θ → θ ≤ 1 →
        0 ≤ ε → ENNReal.ofReal θ ≤ volume S →
        (∀ t ∈ S, |f (u + t • ((8 * A)⁻¹ • p)) - (α + β * t + γ * t ^ 2)| ≤ ε) →
        ∀ k : ℕ, 3 ≤ k → k ≤ 6 →
          |iteratedFDeriv ℝ k f u (fun _ => p)| ≤ K * θ ^ (-C) * A ^ 24 * ε := by
  obtain ⟨K, C, hK, hC, hline⟩ := quadratic_fit_line_norming hR D
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW s F f hroot hrep hF hf hmatch A hA u p α β γ hu hp hWa
    S θ ε hS hSsub hθ hθ1 hε hvol hbound k hk3 hk6
  have hh := hline Δ U V W hΔ hU hV hW s F f hroot hrep hF hf hmatch
    u ((8 * A)⁻¹ • p) α β γ (small_line_direction hA hu hp) hWa
    S θ ε hS hSsub hθ hθ1 hε hvol hbound k hk3 hk6
  have hphysical := abs_diagonal_jet_le_of_small_line hA (by positivity) hf hu p k hk6 hh
  exact hphysical.trans_eq (by ring)

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
