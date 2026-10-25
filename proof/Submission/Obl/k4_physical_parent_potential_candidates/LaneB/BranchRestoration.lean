import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.GraphNormalization
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.AnalyticRestoration
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.VerticalReturn

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set MeasureTheory MvPolynomial FubiniHessian QuadraticTube
open scoped ENNReal

noncomputable section

/-- Palette-free branch restoration in the original height scale. Affine
normalization, all normalized graph jets, the regular heavy patch and the
actual polynomial return are included in this certificate. -/
theorem branch_restoration {D J : ℕ} (hjet : DenseJetBound D J) :
    ∃ M C : ℕ, 1 ≤ M ∧ M ≤ C ∧
    ∀ {A : ℝ}, 2 ≤ A → 2*(2:ℝ)^J ≤ A → ∀ {f : Base → ℝ},
    ContDiffOn ℝ 6 f (Metric.ball (0:Base) 3) →
    ∀ (b s : ℝ) (L : Base →L[ℝ] ℝ), 0 < s →
    HasRealExtension D (fun y => (f y-b-L y)/s) →
    (∀ u ∈ Metric.closedBall (0:Base) 1, |f u-b-L u| ≤ 2*s) →
    (∀ (b' : ℝ) (L' : Base →L[ℝ] ℝ),
      ∃ u ∈ Metric.closedBall (0:Base) 1, s ≤ |f u-b'-L' u|) →
    (∀ i j, HasRealExtension D (fun x => hessian (fun y => (f y-b-L y)/s) x i j)) →
    (∀ i j k, HasRealExtension D (fun x => clearedCubicError (fun y => (f y-b-L y)/s) x i j k)) →
    ∀ {μ : Measure Base}, μ univ ≠ 0 → μ univ ≠ ⊤ →
    (∀ E : Set Base, MeasurableSet E → μ E ≤ ENNReal.ofReal A*μ univ*volume E) →
    μ (Metric.closedBall (0:Base) (1/2))ᶜ = 0 →
    ∀ {η ε : ℝ}, 0 ≤ η → 0 ≤ ε → η*A^C ≤ 1 → ε*A^C ≤ 1 →
    (∀ᵐ x ∂μ, ∃ p : Fin 7 → Base,
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) ∧
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i,p j,p k] r) t)|) ∧
      (∀ i, |iteratedFDeriv ℝ 2 (fun y => (f y-b-L y)/s) x (fun _ => p i)| ≤ η)) →
    (∀ᵐ x ∂μ, ∀ i j k, |clearedCubicError (fun y => (f y-b-L y)/s) x i j k| ≤ ε) →
    ∀ {H : ℝ}, 1 ≤ H → |b| ≤ H →
    (∀ i : Fin 3, |L (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤ H) → s ≤ H → s⁻¹ ≤ H →
    ∃ c ∈ Metric.closedBall (0:Base) (1/2), ∃ Q : Poly,
      Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ 2025*A^C*H^5) ∧
      μ univ ≤ ENNReal.ofReal (A^C)*μ (Metric.ball c (A^M)⁻¹) ∧
      ∀ u ∈ Metric.closedBall c (2*(A^M)⁻¹), ∀ w : ℝ, A^C*|w-f u| ≤ s →
        |ev Q u w| ≤ A^C*(s*ε+|w-f u|) ∧
        (A^C)⁻¹ ≤ ev (pderiv (3:Fin 4) Q) u w ∧
        ev (pderiv (3:Fin 4) Q) u w ≤ A^C ∧
        |ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u w| ≤ A^C/s := by
  obtain ⟨M,C,hM,hMC,hrest⟩ := MeasureNorming.analytic_normalized_restoration hjet
  refine ⟨M,C,hM,hMC,?_⟩
  intro A hA hJA f hf b s L hs hext happ hlow hHext hNext μ hμ0 hμfin hdom hsupp
    η ε hη hε hηsm hεsm hdirs hNa H hH hb hL hsH hsIH
  obtain ⟨hg,hjets,hnon⟩ := normalized_graph_bounds hjet (by norm_num : (2:ℝ) ≤ 2)
    hf b L hs hext happ hlow
  have hbound : ∀ n : ℕ, n ≤ 4 → ∀ u ∈ Metric.closedBall (0:Base) 1,
      ‖iteratedFDeriv ℝ n (fun y => (f y-b-L y)/s) u‖ ≤ A := by
    intro n hn u hu
    exact (hjets n (hn.trans (by decide : 4 ≤ 6)) u
      (Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) hu)).trans hJA
  obtain ⟨c,hc,Q,hdeg,hcoeff,hmass,hQ⟩ := hrest hA hg hbound hnon hHext hNext
    hμ0 hμfin hdom hsupp hη hε hηsm hεsm hdirs hNa
  let ell : Fin 3 → ℝ := fun i => L (EuclideanSpace.basisFun (Fin 3) ℝ i)
  have haff (u:Base) : VerticalReturn.affine b ell u = b+L u := by
    unfold VerticalReturn.affine ell
    rw [Submission.Obl.k4_seven_direction_local_degree_restoration.linear_coordinates]
  have hnorm (u:Base) : (f u-VerticalReturn.affine b ell u)/s = (f u-b-L u)/s := by
    rw [haff]
    ring
  refine ⟨c,hc,VerticalReturn.polynomial b ell s Q,
    (VerticalReturn.degree_polynomial b ell s Q).trans hdeg,?_,hmass,?_⟩
  · exact VerticalReturn.coefficient_bound hH (by positivity) hb hL
      (by simpa only [abs_of_pos hs] using hsH)
      (by simpa only [abs_of_pos (inv_pos.mpr hs)] using hsIH) Q hdeg hcoeff
  · apply VerticalReturn.tube_certificate b ell hs (by positivity) f _ Q
    simpa only [hnorm] using hQ

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
