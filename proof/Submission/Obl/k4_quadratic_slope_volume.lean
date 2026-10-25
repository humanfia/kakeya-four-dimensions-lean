import Mathlib
import ChallengeDeps
import Submission.Obl.k4_quadratic_selector_sweep
import Submission.Obl.k4_bounded_fiber_volume
import Submission.Obl.k4_quadratic_slope_volume.SpatialVolume
import Submission.Obl.k4_quadratic_slope_volume.Area
import Submission.Obl.k4_quadratic_slope_volume.Sweep
set_option linter.unusedVariables false

open Set MeasureTheory
open scoped ENNReal

/-!
# `Submission.k4_quadratic_slope_volume`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_quadratic_slope_volume`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_quadratic_slope_volume/`
belong to this obligation.
-/

theorem Submission.k4_quadratic_slope_volume : ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 4) ℝ) (D : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (t₀ q a K R : ℝ), P.totalDegree ≤ 2 → Matrix.det D ≠ 0 → 0 < q → 0 < a → 1 ≤ K → 1 ≤ R → MeasureTheory.volume {s : EuclideanSpace ℝ (Fin 3) | ‖s‖ ≤ R ∧ ∃ b : EuclideanSpace ℝ (Fin 3), ‖b‖ ≤ R ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), ‖Matrix.toEuclideanLin (D⁻¹) (WithLp.toLp 2 (fun i : Fin 2 => (b + t • s) i.castSucc - c i - t * u i))‖ ≤ K ∧ |MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2] P| ≤ K * a) ∧ ∃ t ∈ Set.Icc t₀ (t₀ + q), K⁻¹ ≤ |MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2] (MvPolynomial.pderiv (3 : Fin 4) P)|} ≤ ENNReal.ofReal (C * K ^ 4 * a * |Matrix.det D| / q ^ 3) := by
  classical
  obtain ⟨N, hN, hselector⟩ := Submission.k4_quadratic_selector_sweep
  refine ⟨27648 * (N : ℝ) * 64 * Real.pi, by positivity, ?_⟩
  intro P D c u t₀ q a K R hP hD hq ha hK hR
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let Sigma : Set (EuclideanSpace ℝ (Fin 3)) := {s : EuclideanSpace ℝ (Fin 3) | ‖s‖ ≤ R ∧ ∃ b : EuclideanSpace ℝ (Fin 3), ‖b‖ ≤ R ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), ‖Matrix.toEuclideanLin (D⁻¹) (WithLp.toLp 2 (fun i : Fin 2 => (b + t • s) i.castSucc - c i - t * u i))‖ ≤ K ∧ |MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2] P| ≤ K * a) ∧ ∃ t ∈ Set.Icc t₀ (t₀ + q), K⁻¹ ≤ |MvPolynomial.eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2] (MvPolynomial.pderiv (3 : Fin 4) P)|}
  let H : ℝ → Set (EuclideanSpace ℝ (Fin 3)) := fun t =>
    {x | ‖Matrix.toEuclideanLin (D⁻¹) (WithLp.toLp 2
      (fun i : Fin 2 => x i.castSucc - c i - t * u i))‖ ≤ K ∧
      |MvPolynomial.eval ![t, x 0, x 1, x 2] P| ≤ K * a ∧
      K⁻¹ / 16 ≤ |MvPolynomial.eval ![t, x 0, x 1, x 2]
        (MvPolynomial.pderiv (3 : Fin 4) P)|}
  obtain ⟨S, b, G, hS, hC1, hsub, hnull, hfit, hG, hlow, hpieces⟩ :=
    hselector P D c u t₀ q a K R hP hD hq ha hK hR Sigma H rfl rfl
  let V : ℝ≥0∞ := ENNReal.ofReal (64 * Real.pi * K ^ 4 * a * |Matrix.det D|)
  have hV : ∀ t : ℝ, volume (H t) ≤ V := by
    intro t
    exact Submission.Obl.k4_quadratic_slope_volume.volume_quadratic_spatial_slice
      P hP D hD c u t a K ha hK
  have hhigh : ∀ t ∈ Icc t₀ (t₀ + q),
      ENNReal.ofReal ((q / 24) ^ 3) *
        (volume.restrict S) {s : EuclideanSpace ℝ (Fin 3) | (s, t) ∈ G} ≤
      (N : ℝ≥0∞) * V := by
    intro t ht
    obtain ⟨hgood, hfibers⟩ := hpieces t ht
    let T : Set (EuclideanSpace ℝ (Fin 3)) := {s | s ∈ S ∧ (s, t) ∈ G}
    have hT : MeasurableSet T := hS.measurableSet.inter
      (hG.preimage (measurable_id.prodMk measurable_const))
    have hFT : ContDiffOn ℝ 1 (fun z => b z + t • z) S :=
      hC1.add (contDiffOn_id.const_smul t)
    have harea := Submission.k4_bounded_fiber_volume N S T (fun z => b z + t • z)
      ((q / 24) ^ 3) hS hFT hT (fun _ hs => hs.1) (by positivity)
      (fun s hs => (hgood s hs).1) hfibers
    have himage : (fun z => b z + t • z) '' T ⊆ H t := by
      rintro _ ⟨s, hs, rfl⟩
      exact (hgood s hs).2
    have hfinal : ENNReal.ofReal ((q / 24) ^ 3) * volume T ≤
        (N : ℝ≥0∞) * V := by
      refine harea.trans ?_
      gcongr
      exact (measure_mono himage).trans (hV t)
    have hsec : MeasurableSet {s : EuclideanSpace ℝ (Fin 3) | (s, t) ∈ G} :=
      hG.preimage (measurable_id.prodMk measurable_const)
    have hset : {s : EuclideanSpace ℝ (Fin 3) | (s, t) ∈ G} ∩ S =
        {s : EuclideanSpace ℝ (Fin 3) | s ∈ S ∧ (s, t) ∈ G} := by
      ext s
      simp only [mem_inter_iff, mem_ofPred_eq, and_comm]
    rw [Measure.restrict_apply hsec, hset]
    exact hfinal
  have hsweep := Submission.Obl.k4_quadratic_slope_volume.slope_volume_of_time_slice_bounds
    S hS.measurableSet t₀ q hq G hG ((N : ℝ≥0∞) * V) hlow hhigh
  have hmeasure : volume Sigma ≤ volume S := by
    calc
      volume Sigma ≤ volume (Sigma ∩ S) + volume (Sigma \ S) :=
        measure_le_inter_add_sdiff volume Sigma S
      _ ≤ volume S + volume (Sigma \ S) := by
        gcongr
        exact inter_subset_right
      _ = volume S := by rw [hnull, add_zero]
  change volume Sigma ≤ _
  refine hmeasure.trans (hsweep.trans_eq ?_)
  dsimp [V]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp [ne_of_gt hq, ne_of_gt hKpos]
