import Submission.Obl.k4_quadratic_selector_sweep.GoodTimes
import Submission.Obl.k4_quadratic_selector_sweep.Quadratic

namespace Submission.Obl.k4_quadratic_selector_sweep

open Set MeasureTheory

/-- Continuity of the native derivative along the sweep of a continuous selector. -/
theorem continuousOn_native_derivative
    (P : MvPolynomial (Fin 4) ℝ) (S : Set Space) (b : Space → Space)
    (hb : ContinuousOn b S) :
    ContinuousOn (fun p : Space × ℝ =>
      MvPolynomial.eval ![p.2, (b p.1 + p.2 • p.1) 0,
        (b p.1 + p.2 • p.1) 1, (b p.1 + p.2 • p.1) 2]
        (MvPolynomial.pderiv (3 : Fin 4) P)) (S ×ˢ (univ : Set ℝ)) := by
  have hb' : ContinuousOn (fun p : Space × ℝ => b p.1) (S ×ˢ (univ : Set ℝ)) :=
    hb.comp continuous_fst.continuousOn (by intro p hp; exact hp.1)
  have hf : ContinuousOn (fun p : Space × ℝ => b p.1 + p.2 • p.1)
      (S ×ˢ (univ : Set ℝ)) :=
    hb'.add (continuous_snd.continuousOn.smul continuous_fst.continuousOn)
  apply (MvPolynomial.continuous_eval
    (MvPolynomial.pderiv (3 : Fin 4) P)).comp_continuousOn
  apply continuousOn_pi.2
  intro i
  fin_cases i
  · exact continuous_snd.continuousOn
  · exact (EuclideanSpace.proj (0 : Fin 3)).continuous.comp_continuousOn hf
  · exact (EuclideanSpace.proj (1 : Fin 3)).continuous.comp_continuousOn hf
  · exact (EuclideanSpace.proj (2 : Fin 3)).continuous.comp_continuousOn hf

/-- All good-time conclusions follow from the smooth selector and eligibility. -/
theorem exists_quadratic_good_time_incidence
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (S : Set Space) (b : Space → Space) (t₀ q K : ℝ)
    (hS : IsOpen S) (hb : ContDiffOn ℝ 1 b S) (hq : 0 < q) (hK : 0 < K)
    (hlarge : ∀ s ∈ S, ∃ t ∈ Icc t₀ (t₀ + q), K⁻¹ ≤
      |MvPolynomial.eval ![t, (b s + t • s) 0, (b s + t • s) 1, (b s + t • s) 2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|) :
    ∃ G : Set (Space × ℝ), MeasurableSet G ∧
      (∀ s ∈ S, ENNReal.ofReal (q / 2) ≤
        (volume.restrict (Icc t₀ (t₀ + q))) {t : ℝ | (s, t) ∈ G}) ∧
      (∀ s t, (s, t) ∈ G ↔ s ∈ S ∧ t ∈ Icc t₀ (t₀ + q) ∧
        (q / 24) ^ 3 ≤ |(fderiv ℝ (fun z => b z + t • z) s).det| ∧
        K⁻¹ / 16 ≤ |MvPolynomial.eval
          ![t, (b s + t • s) 0, (b s + t • s) 1, (b s + t • s) 2]
          (MvPolynomial.pderiv (3 : Fin 4) P)|) := by
  apply exists_good_time_incidence S b
    (fun p => MvPolynomial.eval ![p.2, (b p.1 + p.2 • p.1) 0,
      (b p.1 + p.2 • p.1) 1, (b p.1 + p.2 • p.1) 2]
      (MvPolynomial.pderiv (3 : Fin 4) P)) t₀ q K hS hb
    (continuousOn_native_derivative P S b hb.continuousOn) hq hK
  · intro s hs
    exact quadratic_native_derivative_affine P hP (b s) s
  · exact hlarge

/-- A good-time fiber is contained in the corresponding regular fiber. -/
theorem good_fibers_of_regular_fibers
    (N : ℕ) (S : Set Space) (b : Space → Space) (G : Set (Space × ℝ))
    (q t : ℝ) (hq : 0 < q)
    (hG : ∀ s ∈ S, (s, t) ∈ G →
      (q / 24) ^ 3 ≤ |(fderiv ℝ (fun z => b z + t • z) s).det|)
    (hfiber : ∀ x : Space,
      {s : Space | s ∈ S ∧ (fderiv ℝ (fun z => b z + t • z) s).det ≠ 0 ∧
        b s + t • s = x}.Finite ∧
      {s : Space | s ∈ S ∧ (fderiv ℝ (fun z => b z + t • z) s).det ≠ 0 ∧
        b s + t • s = x}.ncard ≤ N) :
    ∀ x : Space,
      {s : Space | (s ∈ S ∧ (s, t) ∈ G) ∧ b s + t • s = x}.Finite ∧
      {s : Space | (s ∈ S ∧ (s, t) ∈ G) ∧ b s + t • s = x}.ncard ≤ N := by
  intro x
  have hsub : {s : Space | (s ∈ S ∧ (s, t) ∈ G) ∧ b s + t • s = x} ⊆
      {s : Space | s ∈ S ∧ (fderiv ℝ (fun z => b z + t • z) s).det ≠ 0 ∧
        b s + t • s = x} := by
    intro s hs
    refine ⟨hs.1.1, ?_, hs.2⟩
    exact abs_pos.mp ((by positivity : (0 : ℝ) < (q / 24) ^ 3).trans_le
      (hG s hs.1.1 hs.1.2))
  exact ⟨(hfiber x).1.subset hsub,
    (Set.ncard_le_ncard hsub (hfiber x).1).trans (hfiber x).2⟩

end Submission.Obl.k4_quadratic_selector_sweep
