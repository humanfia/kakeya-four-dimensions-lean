import Mathlib
import ChallengeDeps
open MeasureTheory Set

namespace Submission.Obl.k4_polynomial_variation_tube

noncomputable def axis (n : ℕ) : EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (Fin.cons 1 (fun _ => 0))

lemma norm_axis (n : ℕ) : ‖axis n‖ = 1 := by
  simp [axis, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

noncomputable def lineCoordinates {n : ℕ} (a : EuclideanSpace ℝ (Fin (n+1)))
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    (ℝ × (Fin n → ℝ)) ≃ᵐ EuclideanSpace ℝ (Fin (n+1)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm.trans
    ((MeasurableEquiv.toLp 2 _).trans
      (R.toMeasurableEquiv.trans (MeasurableEquiv.addLeft a)))

lemma lineCoordinates_apply {n : ℕ} (a : EuclideanSpace ℝ (Fin (n+1)))
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (t : ℝ) (y : Fin n → ℝ) :
    lineCoordinates a R (t,y) = a + R (WithLp.toLp 2 (Fin.cons t y)) := by
  change a + R (WithLp.toLp 2 ((0 : Fin (n+1)).insertNth t y)) = _
  simp

lemma measurePreserving_lineCoordinates {n : ℕ} (a : EuclideanSpace ℝ (Fin (n+1)))
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    MeasurePreserving (lineCoordinates a R) := by
  exact (measurePreserving_add_left volume a).comp
    (R.measurePreserving.comp ((PiLp.volume_preserving_toLp (Fin (n+1))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm))

lemma continuous_lineCoordinates {n : ℕ} (a : EuclideanSpace ℝ (Fin (n+1)))
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    Continuous (lineCoordinates a R) := by
  have h : Continuous (fun u : ℝ × (Fin n → ℝ) =>
      a + R (WithLp.toLp 2 (Fin.cons u.1 u.2))) := by fun_prop
  simpa only [← lineCoordinates_apply] using h

lemma lineCoordinates_fiber {n : ℕ} (a : EuclideanSpace ℝ (Fin (n+1)))
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (e : EuclideanSpace ℝ (Fin (n+1))) (hR : R (axis n) = e)
    (t : ℝ) (y : Fin n → ℝ) :
    lineCoordinates a R (t,y) = lineCoordinates a R (0,y) + t • e := by
  rw [lineCoordinates_apply, lineCoordinates_apply, ← hR, ← R.map_smul, add_assoc,
    ← R.map_add]
  congr 2
  ext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [axis]

def transverseBox (n : ℕ) : Set (Fin n → ℝ) :=
  Set.Icc (fun _ => -4) (fun _ => 4)

lemma volume_transverseBox (n : ℕ) : volume.real (transverseBox n) = 8^n := by
  change (volume (Set.Icc (fun _ : Fin n => (-4 : ℝ)) (fun _ => 4))).toReal = _
  rw [Real.volume_Icc_pi_toReal (by intro j; norm_num)]
  norm_num

lemma rectangle_integral_le {n : ℕ} (a : EuclideanSpace ℝ (Fin (n+1)))
    (R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (e : EuclideanSpace ℝ (Fin (n+1))) (hR : R (axis n) = e)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hf : Continuous f) (B : ℝ)
    (hline : ∀ (b : EuclideanSpace ℝ (Fin (n+1))) (s t : ℝ),
      s ≤ t → (∫ u in Set.Icc s t, f (b + u • e)) ≤ B)
    (s t : ℝ) (hst : s ≤ t) :
    (∫ u in Set.Icc s t ×ˢ transverseBox n, f (lineCoordinates a R u)) ≤ 8^n * B := by
  have hcont := hf.comp (continuous_lineCoordinates a R)
  have hint : IntegrableOn (fun u => f (lineCoordinates a R u))
      (Set.Icc s t ×ˢ transverseBox n) volume :=
    hcont.continuousOn.integrableOn_compact
      (isCompact_Icc.prod (show IsCompact (transverseBox n) from isCompact_Icc))
  have hint' : Integrable (fun u => f (lineCoordinates a R u))
      ((volume.restrict (Set.Icc s t)).prod (volume.restrict (transverseBox n))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hint
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hint']
  calc
    (∫ y in transverseBox n, ∫ u in Set.Icc s t, f (lineCoordinates a R (u,y)))
        ≤ ∫ _y in transverseBox n, B := by
      apply integral_mono hint'.integral_prod_right
        (continuous_const.continuousOn.integrableOn_compact
          (show IsCompact (transverseBox n) from isCompact_Icc))
      intro y
      calc
        _ = ∫ u in Set.Icc s t, f (lineCoordinates a R (0,y) + u • e) :=
          integral_congr_ae (ae_of_all _ (fun u => congrArg f (lineCoordinates_fiber a R e hR u y)))
        _ ≤ B := hline (lineCoordinates a R (0,y)) s t hst
    _ = 8^n * B := by rw [setIntegral_const, smul_eq_mul, volume_transverseBox]

end Submission.Obl.k4_polynomial_variation_tube
