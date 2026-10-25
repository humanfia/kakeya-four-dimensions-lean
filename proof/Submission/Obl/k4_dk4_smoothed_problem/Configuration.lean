import Submission.Obl.k4_dk4_smoothed_problem.DyadicNumerics
import Submission.Obl.k4_dk4_smoothed_problem.PlanarCeiling
import Submission.Obl.k4_dk4_smoothed_problem.Tempered

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_dk4_smoothed_problem

open Framework

noncomputable def configurationIntercept {c R σ : ℝ} {k : ℕ}
    (A : BadConfiguration c R σ k) : Fin A.n → Fin 3 → ℝ :=
  fun i => FiniteSmoothing.spatialCoords (A.x i)

noncomputable def configurationSlope {c R σ : ℝ} {k : ℕ}
    (A : BadConfiguration c R σ k) : Fin A.n → Fin 3 → ℝ :=
  fun i => FiniteSmoothing.spatialCoords (A.v i)

noncomputable def configurationPrior {c R σ : ℝ} {k : ℕ}
    (A : BadConfiguration c R σ k) : Measure Coefficients :=
  nativePrior (smoothingRadius k) (configurationIntercept A) (configurationSlope A)

noncomputable def configurationEvent {c R σ : ℝ} {k : ℕ}
    (A : BadConfiguration c R σ k) : Set (Coefficients × ℝ) :=
  boundedNativeEvent (R + 3) (⋃ j, Metric.ball (A.z j) (2 * radius k))

theorem abs_spatialCoords_le (w : EuclideanSpace ℝ (Fin 4)) (j : Fin 3) :
    |FiniteSmoothing.spatialCoords w j| ≤ ‖w‖ := by
  have h := PiLp.norm_apply_le (WithLp.toLp 2 (FiniteSmoothing.spatialCoords w)) j
  have h' : |FiniteSmoothing.spatialCoords w j| ≤
      ‖WithLp.toLp 2 (FiniteSmoothing.spatialCoords w)‖ := by
    simpa only [PiLp.toLp_apply, Real.norm_eq_abs] using h
  exact h'.trans (FiniteSmoothing.norm_spatialCoords_le w)

theorem configuration_coordinate_bounds {c R σ : ℝ} {k : ℕ}
    (hR : 1 ≤ R) (A : BadConfiguration c R σ k) :
    (∀ i j, |configurationIntercept A i j| + smoothingRadius k ≤ R + 3) ∧
      (∀ i j, |configurationSlope A i j| + smoothingRadius k ≤ R + 3) ∧
      (∀ i, |configurationSlope A i 2| + smoothingRadius k ≤ 3) := by
  have hr := smoothingRadius_le_one k
  have hx (i : Fin A.n) (j : Fin 3) : |configurationIntercept A i j| ≤ R :=
    (abs_spatialCoords_le (A.x i) j).trans (A.bounded i)
  have hv (i : Fin A.n) (j : Fin 3) : |configurationSlope A i j| ≤ 2 :=
    (abs_spatialCoords_le (A.v i) j).trans (A.coordinates i).2.2
  exact ⟨fun i j => by linarith [hx i j],
    (fun i j => by linarith [hv i j]), fun i => by linarith [hv i 2]⟩

theorem configuration_slope_boxes_disjoint {c R σ : ℝ} {k : ℕ}
    (A : BadConfiguration c R σ k) :
    Pairwise (fun i j => Disjoint
      (FiniteSmoothing.coordBox (smoothingRadius k) (configurationSlope A i))
      (FiniteSmoothing.coordBox (smoothingRadius k) (configurationSlope A j))) := by
  have hδ : 0 < radius k := by rw [radius_eq_inv]; exact inv_pos.mpr (scale_pos k)
  apply FiniteSmoothing.coordBox_pairwise_disjoint (δ := radius k)
    (smoothingRadius_pos k).le (by unfold smoothingRadius; linarith)
    (configurationSlope A)
  intro i j hij
  change radius k ≤
    ‖WithLp.toLp 2 (FiniteSmoothing.spatialCoords (A.v i)) -
      WithLp.toLp 2 (FiniteSmoothing.spatialCoords (A.v j))‖
  rw [FiniteSmoothing.norm_spatialCoords_sub (A.coordinates i).2.1 (A.coordinates j).2.1]
  exact A.separated i j hij

theorem configuration_slope_ceiling {c R σ : ℝ} {k : ℕ}
    (hc : 0 < c) (A : BadConfiguration c R σ k)
    (Z : Set (EuclideanSpace ℝ (Fin 3))) :
    configurationPrior A
      {l | (WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5] : EuclideanSpace ℝ (Fin 3)) ∈ Z} ≤
      ENNReal.ofReal (slopeFactor c k) * volume Z := by
  have hsmall : (216 / c) * ((k : ℝ) + 1) ^ 2 ≤ slopeFactor c k := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right (by norm_num : (216 : ℝ) ≤ 46656) hc.le
  have hheight : (A.n : ENNReal)⁻¹ *
      (ENNReal.ofReal (2 * smoothingRadius k) ^ 3)⁻¹ ≤ ENNReal.ofReal (slopeFactor c k) := by
    rw [← ofReal_box_height A.n_pos (smoothingRadius_pos k) 3]
    exact ENNReal.ofReal_le_ofReal ((slope_height_le hc A.count_lower).trans hsmall)
  exact (nativePrior_slope_le (smoothingRadius_pos k) (configurationIntercept A)
    (configurationSlope A) (configuration_slope_boxes_disjoint A) Z).trans
      (mul_le_mul' hheight le_rfl)

theorem configuration_joint_ceiling {c R σ : ℝ} {k : ℕ}
    (hc : 0 < c) (hR : 1 ≤ R) (A : BadConfiguration c R σ k)
    (t : ℝ) (S T : Set (EuclideanSpace ℝ (Fin 2))) :
    configurationPrior A {l | planarLine l t ∈ S ∧ planarVelocity l ∈ T} ≤
      ENNReal.ofReal (slopeFactor c k * scale k ^ 2) * volume S * volume T := by
  have hr := smoothingRadius_pos k
  have hM := (configuration_coordinate_bounds hR A).2.2
  have h := nativePrior_joint_le hr (configurationIntercept A) (configurationSlope A)
    hM (configuration_slope_boxes_disjoint A) t S T
  have hident : ENNReal.ofReal
      ((A.n : ℝ)⁻¹ * ((2 * smoothingRadius k) ^ 3)⁻¹ *
        ((2 * smoothingRadius k) ^ 2)⁻¹ * 6) =
      (A.n : ENNReal)⁻¹ * (ENNReal.ofReal (2 * smoothingRadius k) ^ 3)⁻¹ *
        (ENNReal.ofReal (2 * smoothingRadius k) ^ 2)⁻¹ * ENNReal.ofReal (2 * (3 : ℝ)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_box_height A.n_pos hr 3, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by positivity)]
    norm_num
  have hheight : (A.n : ENNReal)⁻¹ * (ENNReal.ofReal (2 * smoothingRadius k) ^ 3)⁻¹ *
      (ENNReal.ofReal (2 * smoothingRadius k) ^ 2)⁻¹ * ENNReal.ofReal (2 * (3 : ℝ)) ≤
      ENNReal.ofReal (slopeFactor c k * scale k ^ 2) := by
    rw [← hident]
    exact ENNReal.ofReal_le_ofReal (joint_height_le hc A.count_lower)
  exact h.trans (mul_le_mul' (mul_le_mul' hheight le_rfl) le_rfl)

theorem configuration_time_mass {c R σ : ℝ} {k : ℕ}
    (hc : 0 < c) (hR : 1 ≤ R) (A : BadConfiguration c R σ k) :
    ENNReal.ofReal (nativeFactor c R k)⁻¹ ≤
      ((configurationPrior A).prod volume).restrict (configurationEvent A) univ := by
  obtain ⟨hb, hs, hM⟩ := configuration_coordinate_bounds hR A
  have hδ : 0 < radius k := by rw [radius_eq_inv]; exact inv_pos.mpr (scale_pos k)
  have hrad (j : Fin A.m) : A.ρ j + 6 * smoothingRadius k ≤ 2 * radius k := by
    have hρ := (A.radii j).2
    change A.ρ j ≤ radius k at hρ
    unfold smoothingRadius
    linarith
  have htime (i : Fin A.n) : ENNReal.ofReal (c / ((k : ℝ) + 1) ^ 2) ≤
      volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        FiniteSmoothing.graphLine (configurationIntercept A i) (configurationSlope A i) t ∈
          ⋃ j, Metric.ball (A.z j) (A.ρ j)} := by
    simpa only [configurationIntercept, configurationSlope,
      FiniteSmoothing.graphLine_spatialCoords (A.coordinates i).1 (A.coordinates i).2.1]
      using A.time_mass i
  exact (ENNReal.ofReal_le_ofReal (nativeFactor_inv_le hc hR k)).trans
    (boundedNativeEvent_time_mass A.n_pos (smoothingRadius_pos k)
      (configurationIntercept A) (configurationSlope A) hb hs A.z A.ρ hrad _ htime)

theorem configuration_tempered {c R σ : ℝ} {k : ℕ}
    (hc : 0 < c) (hR : 1 ≤ R) (hσ : 0 < σ)
    (hN : 2 ≤ scale k) (hcN : c + 1 ≤ scale k) (hRN : R + 3 ≤ scale k)
    (A : BadConfiguration c R σ k) :
    TemperedAt (scale k) (nativeFactor c R k) 32 4
      (configurationPrior A) (configurationEvent A) := by
  have hN1 : 1 ≤ scale k := by linarith
  have hpow : scale k ≤ scale k ^ 32 := by
    simpa only [pow_one] using pow_le_pow_right₀ hN1 (by omega : 1 ≤ 32)
  obtain ⟨hb, hs, hM⟩ := configuration_coordinate_bounds hR A
  obtain ⟨hnN, hmN⟩ := count_bounds hσ hN hcN A
  apply native_tempered A.n_pos (smoothingRadius_pos k)
    (mul_pos (by norm_num) (by rw [radius_eq_inv]; exact inv_pos.mpr (scale_pos k)))
    (by linarith : 0 ≤ R + 3) (nativeFactor_ge hc hR k).2 32 4 le_rfl
    (configurationIntercept A) (configurationSlope A) hb hs hnN
    (componentHeight_le A.n_pos hN) (atom_count_le hN hmN) (hRN.trans hpow)
    (by positivity) A.z
  simpa only [configurationPrior, configurationEvent, Measure.restrict_apply_univ] using
    configuration_time_mass hc hR A

theorem configuration_cover {c R σ : ℝ} {k : ℕ} (hσ : 0 < σ)
    (A : BadConfiguration c R σ k) :
    (A.m : ℝ) ≤ 16 * scale k ^ (4 - σ) ∧
      ∀ p ∈ configurationEvent A, ∃ j : Fin A.m,
        ‖physicalPoint p - A.z j‖ ≤ 16 / scale k := by
  refine ⟨A.cover_count.trans (cover_count_le hσ k), ?_⟩
  intro p hp
  obtain ⟨j, hj⟩ := mem_iUnion.mp hp.2.2.2
  have hdist : ‖physicalPoint p - A.z j‖ < 2 * radius k := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hj
  refine ⟨j, hdist.le.trans ?_⟩
  rw [radius_eq_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 16)
    (inv_pos.mpr (scale_pos k)).le

end Submission.Obl.k4_dk4_smoothed_problem
