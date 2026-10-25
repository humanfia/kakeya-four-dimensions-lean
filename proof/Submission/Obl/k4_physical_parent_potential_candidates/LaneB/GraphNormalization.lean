import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.GraphExtensions
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.DenseJet.Bridge

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set Metric MvPolynomial MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

theorem SqrtRep.normalized_graph {D : ℕ} {sq F : EuclideanSpace ℂ (Fin 3) → ℂ}
    (hF : SqrtRep (ball 0 4) sq D F) (c s0 : ℝ) (L : Base →L[ℝ] ℝ) :
    SqrtRep (ball 0 4) sq (D+1)
      (fun z => (F z-DenseJet.complexAffine c L z)/(s0:ℂ)) := by
  let P : MvPolynomial (Fin 3) ℂ :=
    C (c:ℂ)+∑ i : Fin 3, C (L (EuclideanSpace.single i 1):ℂ)*X i
  have hdeg : P.totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le (by simp) ((totalDegree_finsetSum _ _).trans
      (Finset.sup_le fun i _ => (totalDegree_mul _ _).trans (by simp))))
  have heval : ∀ z : EuclideanSpace ℂ (Fin 3),
      eval (fun i => z i) P = DenseJet.complexAffine c L z := by
    intro z
    simp [P, DenseJet.complexAffine]
  exact ((hF.sub ((SqrtRep.poly P).mono hdeg)).div_const (s0:ℂ)).congr
    (fun z _ => by rw [heval])

theorem hasRealExtension_normalized_graph {D : ℕ}
    {Δ : MvPolynomial (Fin 3) ℂ} (hΔ : Δ.totalDegree ≤ D)
    {sq F : EuclideanSpace ℂ (Fin 3) → ℂ}
    (hroot : ∀ z ∈ ball (0:EuclideanSpace ℂ (Fin 3)) 4,
      (sq z)^2 = eval (fun i => z i) Δ)
    (hF : SqrtRep (ball 0 4) sq D F) {f : Base → ℝ}
    (hf : ∀ x ∈ ball (0:Base) 4, F (DenseJet.realSlice x) = (f x:ℂ))
    (c s0 : ℝ) (L : Base →L[ℝ] ℝ) :
    HasRealExtension (8*(D+1)+2) (fun y => (f y-c-L y)/s0) := by
  apply hasRealExtension_of_sqrtRep (hΔ.trans (by omega)) hroot
    (hF.normalized_graph c s0 L)
  intro x hx
  have haff := DenseJet.complexAffine_real c L x
  rw [← DenseJet.realSlice_apply] at haff
  rw [hf x hx, haff]
  push_cast
  ring

/-- The unit real base ball is large enough for the fixed-domain norming
estimate at every budget at least two. -/
theorem volume_unit_ball_floor {A : ℝ} (hA : 2 ≤ A) :
    ENNReal.ofReal A⁻¹ ≤ volume (closedBall (0:Base) 1) := by
  rw [EuclideanSpace.volume_closedBall_fin_three]
  norm_num only [ENNReal.ofReal_one, one_pow, one_mul]
  apply ENNReal.ofReal_le_ofReal
  have hI : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hπ := Real.pi_gt_three
  exact hI.trans (by linarith)

/-- Subtract an affine approximant and divide by its positive affine
distance. All actual jets, including orders zero and one, are uniformly
controlled by dense algebraic norming. The nonaffine lower witnesses scale
to one. -/
theorem normalized_graph_bounds {D J : ℕ} (hjet : DenseJetBound D J)
    {A : ℝ} (hA : 2 ≤ A) {f : Base → ℝ}
    (hf : ContDiffOn ℝ 6 f (ball (0:Base) 3))
    (c : ℝ) (L : Base →L[ℝ] ℝ) {s : ℝ} (hs : 0 < s)
    (hext : HasRealExtension D (fun y => (f y-c-L y)/s))
    (happrox : ∀ u ∈ closedBall (0:Base) 1, |f u-c-L u| ≤ 2*s)
    (hlower : ∀ (c' : ℝ) (L' : Base →L[ℝ] ℝ),
      ∃ u ∈ closedBall (0:Base) 1, s ≤ |f u-c'-L' u|) :
    ContDiffOn ℝ 6 (fun y => (f y-c-L y)/s) (ball (0:Base) 3) ∧
    (∀ n : ℕ, n ≤ 6 → ∀ u ∈ closedBall (0:Base) 2,
      ‖iteratedFDeriv ℝ n (fun y => (f y-c-L y)/s) u‖ ≤ 2*A^J) ∧
    (∀ (c' : ℝ) (L' : Base →L[ℝ] ℝ), ∃ u ∈ closedBall (0:Base) 1,
      1 ≤ |(f u-c-L u)/s-c'-L' u|) := by
  have hg : ContDiffOn ℝ 6 (fun y => (f y-c-L y)/s) (ball (0:Base) 3) :=
    ((hf.sub contDiffOn_const).sub L.contDiff.contDiffOn).div_const s
  have hv : ∀ u ∈ closedBall (0:Base) 1, |(f u-c-L u)/s| ≤ 2 := by
    intro u hu
    rw [abs_div, abs_of_pos hs]
    exact (div_le_iff₀ hs).2 (happrox u hu)
  refine ⟨hg,?_,?_⟩
  · intro n hn u hu
    have hb := (hjet A hA _ hext).1 (closedBall (0:Base) 1) 2
      isClosed_closedBall.measurableSet Subset.rfl (volume_unit_ball_floor hA)
      (by norm_num) hv n hn u hu
    simpa only [mul_comm] using hb
  · intro c' L'
    obtain ⟨u,hu,hl⟩ := hlower (c+s*c') (L+s • L')
    refine ⟨u,hu,?_⟩
    have he : s*((f u-c-L u)/s-c'-L' u) = f u-(c+s*c')-(L+s • L') u := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      field_simp
      ring
    rw [← he, abs_mul, abs_of_pos hs] at hl
    nlinarith only [hl,hs]

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
