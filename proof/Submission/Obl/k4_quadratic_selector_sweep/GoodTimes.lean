import Mathlib
import Submission.Lib.K4GoodTimes

namespace Submission.Obl.k4_quadratic_selector_sweep

open Set MeasureTheory

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The derivative of the affine sweep in the slope variable. -/
theorem fderiv_sweep {b : Space → Space} {S : Set Space}
    (hS : IsOpen S) (hb : ContDiffOn ℝ 1 b S) {s : Space} (hs : s ∈ S) (t : ℝ) :
    fderiv ℝ (fun z => b z + t • z) s =
      fderiv ℝ b s + t • ContinuousLinearMap.id ℝ Space := by
  have hbs : DifferentiableAt ℝ b s :=
    (hb.differentiableOn (by norm_num)).differentiableAt (hS.mem_nhds hs)
  exact (hbs.hasFDerivAt.add ((hasFDerivAt_id s).const_smul t)).fderiv

/-- The existing matrix estimate also applies to continuous linear maps. -/
theorem volume_linearMap_affine_good_times (A : Space →L[ℝ] Space)
    (a b t₀ q K : ℝ) (hq : 0 < q) (hK : 0 < K)
    (hlarge : ∃ t ∈ Icc t₀ (t₀ + q), K⁻¹ ≤ |a * t + b|) :
    ENNReal.ofReal (q / 2) ≤ volume {t : ℝ | t ∈ Icc t₀ (t₀ + q) ∧
      (q / 24) ^ 3 ≤ |(A + t • ContinuousLinearMap.id ℝ Space).det| ∧
      K⁻¹ / 16 ≤ |a * t + b|} := by
  let e := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hdet (t : ℝ) :
      ((LinearMap.toMatrix e e) A.toLinearMap + Matrix.scalar (Fin 3) t).det =
      (A + t • ContinuousLinearMap.id ℝ Space).det := by
    change _ = LinearMap.det (A + t • ContinuousLinearMap.id ℝ Space).toLinearMap
    rw [← LinearMap.det_toMatrix e]
    simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  simpa only [hdet] using
    Submission.Lib.K4GoodTimes.volume_det_affine_good_times
      ((LinearMap.toMatrix e e) A.toLinearMap) a b t₀ q K hq hK hlarge

/-- A C¹ selector and a continuous native derivative define measurable good times. -/
theorem exists_good_time_incidence
    (S : Set Space) (b : Space → Space) (g : Space × ℝ → ℝ)
    (t₀ q K : ℝ) (hS : IsOpen S) (hb : ContDiffOn ℝ 1 b S)
    (hg : ContinuousOn g (S ×ˢ (univ : Set ℝ)))
    (hq : 0 < q) (hK : 0 < K)
    (haffine : ∀ s ∈ S, ∃ a c : ℝ, ∀ t : ℝ, g (s, t) = a * t + c)
    (hlarge : ∀ s ∈ S, ∃ t ∈ Icc t₀ (t₀ + q), K⁻¹ ≤ |g (s, t)|) :
    ∃ G : Set (Space × ℝ), MeasurableSet G ∧
      (∀ s ∈ S, ENNReal.ofReal (q / 2) ≤
        (volume.restrict (Icc t₀ (t₀ + q))) {t : ℝ | (s, t) ∈ G}) ∧
      (∀ s t, (s, t) ∈ G ↔ s ∈ S ∧ t ∈ Icc t₀ (t₀ + q) ∧
        (q / 24) ^ 3 ≤ |(fderiv ℝ (fun z => b z + t • z) s).det| ∧
        K⁻¹ / 16 ≤ |g (s, t)|) := by
  classical
  let A : Space → (Space →L[ℝ] Space) :=
    S.piecewise (fderiv ℝ b) (fun _ => 0)
  have hA : Measurable A :=
    (hb.continuousOn_fderiv_of_isOpen hS (by norm_num)).measurable_piecewise
      continuousOn_const hS.measurableSet
  let g' : Space × ℝ → ℝ :=
    (S ×ˢ (univ : Set ℝ)).piecewise g (fun _ => 0)
  have hg' : Measurable g' := hg.measurable_piecewise continuousOn_const
    (hS.measurableSet.prod MeasurableSet.univ)
  let G : Set (Space × ℝ) := {p | p.1 ∈ S ∧ p.2 ∈ Icc t₀ (t₀ + q) ∧
    (q / 24) ^ 3 ≤ |(A p.1 + p.2 • ContinuousLinearMap.id ℝ Space).det| ∧
    K⁻¹ / 16 ≤ |g' p|}
  have hG : MeasurableSet G := by
    have hdet : Measurable (fun p : Space × ℝ =>
        (A p.1 + p.2 • ContinuousLinearMap.id ℝ Space).det) :=
      ContinuousLinearMap.continuous_det.measurable.comp
        ((hA.comp measurable_fst).add (measurable_snd.smul_const _))
    exact (hS.measurableSet.preimage measurable_fst).inter
      ((measurableSet_Icc.preimage measurable_snd).inter
        ((measurableSet_le measurable_const hdet.abs).inter
          (measurableSet_le measurable_const hg'.abs)))
  have hmem (s : Space) (t : ℝ) : (s, t) ∈ G ↔
      s ∈ S ∧ t ∈ Icc t₀ (t₀ + q) ∧
        (q / 24) ^ 3 ≤ |(fderiv ℝ (fun z => b z + t • z) s).det| ∧
        K⁻¹ / 16 ≤ |g (s, t)| := by
    by_cases hs : s ∈ S
    · simp [G, A, g', hs, fderiv_sweep hS hb hs]
    · simp [G, hs]
  refine ⟨G, hG, ?_, hmem⟩
  intro s hs
  obtain ⟨a, c, hac⟩ := haffine s hs
  have h := volume_linearMap_affine_good_times (fderiv ℝ b s) a c t₀ q K hq hK
    (by simpa only [hac] using hlarge s hs)
  rw [Measure.restrict_apply' measurableSet_Icc]
  convert h using 1
  congr 1
  ext t
  simp only [mem_inter_iff, mem_ofPred_eq, hmem, hs, true_and, hac,
    fderiv_sweep hS hb hs]
  tauto

end Submission.Obl.k4_quadratic_selector_sweep
