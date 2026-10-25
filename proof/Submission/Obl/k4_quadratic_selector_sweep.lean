import Mathlib
import ChallengeDeps
import Submission.Obl.k4_eligibility_sign_description
import Submission.Obl.k4_bounded_sign_choice
import Submission.Obl.k4_sign_graph_generic_c1
import Submission.Obl.k4_sign_set_isolated_bound
import Submission.Obl.k4_quadratic_selector_sweep.SignFibers
import Submission.Obl.k4_quadratic_selector_sweep.Incidence
set_option linter.unusedVariables false

/-!
# `Submission.k4_quadratic_selector_sweep`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_quadratic_selector_sweep`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_quadratic_selector_sweep/`
belong to this obligation.
-/

open Submission.Obl.k4_quadratic_selector_sweep

theorem Submission.k4_quadratic_selector_sweep : ∃ N : ℕ, 0 < N ∧ ∀ (P : MvPolynomial (Fin 4) ℝ) (D : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (t₀ q a K R : ℝ), P.totalDegree ≤ 2 → Matrix.det D ≠ 0 → 0 < q → 0 < a → 1 ≤ K → 1 ≤ R → ∀ (Sigma : Set (EuclideanSpace ℝ (Fin 3))) (H : ℝ → Set (EuclideanSpace ℝ (Fin 3))), Sigma = {s : EuclideanSpace ℝ (Fin 3) | ‖s‖ ≤ R ∧ ∃ b : EuclideanSpace ℝ (Fin 3), ‖b‖ ≤ R ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), ‖Matrix.toEuclideanLin (D⁻¹) (WithLp.toLp 2 (fun i : Fin 2 => (b + t • s) i.castSucc - c i - t * u i))‖ ≤ K ∧ |MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2] P| ≤ K * a) ∧ ∃ t ∈ Set.Icc t₀ (t₀ + q), K⁻¹ ≤ |MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2] (MvPolynomial.pderiv (3 : Fin 4) P)|} → H = (fun t => {x : EuclideanSpace ℝ (Fin 3) | ‖Matrix.toEuclideanLin (D⁻¹) (WithLp.toLp 2 (fun i : Fin 2 => x i.castSucc - c i - t * u i))‖ ≤ K ∧ |MvPolynomial.eval ![t, x 0, x 1, x 2] P| ≤ K * a ∧ K⁻¹ / 16 ≤ |MvPolynomial.eval ![t, x 0, x 1, x 2] (MvPolynomial.pderiv (3 : Fin 4) P)|}) → ∃ S : Set (EuclideanSpace ℝ (Fin 3)), ∃ b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), ∃ G : Set (EuclideanSpace ℝ (Fin 3) × ℝ), IsOpen S ∧ ContDiffOn ℝ 1 b S ∧ S ⊆ Sigma ∧ MeasureTheory.volume (Sigma \ S) = 0 ∧ (∀ s ∈ S, ‖b s‖ ≤ R ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), ‖Matrix.toEuclideanLin (D⁻¹) (WithLp.toLp 2 (fun i : Fin 2 => (b s + t • s) i.castSucc - c i - t * u i))‖ ≤ K ∧ |MvPolynomial.eval ![t, (b s + t • s) 0, (b s + t • s) 1, (b s + t • s) 2] P| ≤ K * a) ∧ ∃ t ∈ Set.Icc t₀ (t₀ + q), K⁻¹ ≤ |MvPolynomial.eval ![t, (b s + t • s) 0, (b s + t • s) 1, (b s + t • s) 2] (MvPolynomial.pderiv (3 : Fin 4) P)|) ∧ MeasurableSet G ∧ (∀ s ∈ S, ENNReal.ofReal (q / 2) ≤ (MeasureTheory.volume.restrict (Set.Icc t₀ (t₀ + q))) {t : ℝ | (s, t) ∈ G}) ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), (∀ s ∈ {s : EuclideanSpace ℝ (Fin 3) | s ∈ S ∧ (s, t) ∈ G}, (q / 24) ^ 3 ≤ |(fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) => b z + t • z) s).det| ∧ b s + t • s ∈ H t) ∧ ∀ x : EuclideanSpace ℝ (Fin 3), {s : EuclideanSpace ℝ (Fin 3) | (s ∈ S ∧ (s, t) ∈ G) ∧ b s + t • s = x}.Finite ∧ {s : EuclideanSpace ℝ (Fin 3) | (s ∈ S ∧ (s, t) ∈ G) ∧ b s + t • s = x}.ncard ≤ N) := by
  classical
  obtain ⟨m, d, helig⟩ := Submission.k4_eligibility_sign_description
  obtain ⟨C, hC, hchoice⟩ := Submission.k4_bounded_sign_choice m d
  obtain ⟨N, hN, hisolated⟩ := Submission.k4_sign_set_isolated_bound C C
  refine ⟨N, hN, ?_⟩
  intro P D c u t₀ q a K R hP hD hq ha hK hR Sigma H hSigma hH
  obtain ⟨p, B, hpdeg, hE⟩ := helig P D c u t₀ q a K R hP hD hq ha hK hR
  obtain ⟨b, g, A, hgdeg, hgraph, hselect⟩ := hchoice p B hpdeg
  have hprojection (s : SlopeSpace) :
      (∃ y : SlopeSpace, graphSigns p s y ∈ B) ↔ s ∈ Sigma := by
    rw [hSigma]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨hsR, hyR, htime, hlarge⟩ := (hE s y).mp hy
      exact ⟨hsR, y, hyR, htime, hlarge⟩
    · rintro ⟨hsR, y, hyR, htime, hlarge⟩
      exact ⟨y, (hE s y).mpr ⟨hsR, hyR, htime, hlarge⟩⟩
  have hgraph' : ∀ s y : SlopeSpace, graphSigns g s y ∈ A ↔
      s ∈ Sigma ∧ b s = y := by
    intro s y
    exact (hgraph s y).trans (and_congr (hprojection s) Iff.rfl)
  obtain ⟨S, hS, hb, hsub, hnull⟩ :=
    Submission.k4_sign_graph_generic_c1 C g A Sigma b hgraph'
  have hbE (s : SlopeSpace) (hs : s ∈ S) :=
    ((hE s (b s)).mp (hselect s ((hprojection s).mpr (hsub hs)))).2
  obtain ⟨G, hG, hsections, hGmem⟩ :=
    exists_quadratic_good_time_incidence P hP S b t₀ q K hS hb hq
      (lt_of_lt_of_le zero_lt_one hK) (fun s hs => (hbE s hs).2.2)
  refine ⟨S, b, G, hS, hb, hsub, hnull, hbE, hG, hsections, ?_⟩
  intro t ht
  constructor
  · intro s hs
    have hgood := (hGmem s t).mp hs.2
    refine ⟨hgood.2.2.1, ?_⟩
    rw [hH]
    exact ⟨((hbE s hs.1).2.1 t ht).1, ((hbE s hs.1).2.1 t ht).2, hgood.2.2.2⟩
  · intro x
    obtain ⟨r, hrdeg, hrdescription⟩ :=
      sweep_fiber_sign_description g A Sigma b hgdeg hgraph' t x
    obtain ⟨hfinite, hcard⟩ :=
      hisolated r A {s : SlopeSpace | s ∈ Sigma ∧ b s + t • s = x}
        hrdeg hrdescription
    change (isolatedPoints {s : SlopeSpace | s ∈ Sigma ∧ b s + t • s = x}).Finite
      at hfinite
    change (isolatedPoints {s : SlopeSpace | s ∈ Sigma ∧ b s + t • s = x}).ncard ≤ N
      at hcard
    have hgoodsub :
        {s : SlopeSpace | (s ∈ S ∧ (s, t) ∈ G) ∧ b s + t • s = x} ⊆
          isolatedPoints {s : SlopeSpace | s ∈ Sigma ∧ b s + t • s = x} := by
      intro s hs
      apply regular_sweep_fiber_isolated S Sigma b hS hb hsub t x s hs.1.1 hs.2
      have hgood := (hGmem s t).mp hs.1.2
      exact abs_pos.mp ((by positivity : (0 : ℝ) < (q / 24) ^ 3).trans_le
        hgood.2.2.1)
    exact ⟨hfinite.subset hgoodsub, (Set.ncard_le_ncard hgoodsub hfinite).trans hcard⟩
