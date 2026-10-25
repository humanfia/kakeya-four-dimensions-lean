import Submission.Obl.k4_adapted_affine_cube_cover.Assembly
import Submission.Obl.k4_adapted_affine_cube_cover.Frame

namespace Submission.Obl.k4_adapted_affine_cube_cover

open MeasureTheory Set Module
open scoped ENNReal

/-- Assemble the adapted basis and the finite geometric packing into the frozen cover properties. -/
theorem cover_of_cube_packing (n : ℕ)
    (cube : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin n) → ℝ → Set (EuclideanSpace ℝ (Fin n)))
    (hcube : ∀ b a s, cube b a s =
      (fun t : Fin n → ℝ => a + s • (∑ i : Fin n, t i • b i)) '' Icc 0 1)
    (hcompact : ∀ b a s, IsCompact (cube b a s))
    (hvolume : ∀ b a s, 0 ≤ s → volume (cube b a s) =
      ENNReal.ofReal (s ^ n * |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b|))
    (hpacking : ∀ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (∀ i, ‖b i‖ ≤ 1) → ∀ η : ℝ, 0 < η → (n : ℝ) * η ≤ 1 / 8 →
      ∀ c : EuclideanSpace ℝ (Fin n), ∃ (k : ℕ) (a : Fin k → EuclideanSpace ℝ (Fin n)),
        (∀ h, cube b (a h) η ⊆ Metric.ball c 1) ∧
        Pairwise (fun h j => Disjoint (cube b (a h) η) (cube b (a j) η)) ∧
        volume (Metric.ball c (1 / 4)) ≤ (2 : ℝ≥0∞) ^ n * ∑ h, volume (cube b (a h) η)) :
    ∃ d : ℝ, 0 < d ∧ ∀ η : ℝ, 0 < η → (n : ℝ) * η ≤ (1 / 8 : ℝ) →
      ∃ C : ℝ, 0 < C ∧ ∀ V : Seminorm ℝ (EuclideanSpace ℝ (Fin n)), Continuous V →
      (∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ V v) → ∀ c : EuclideanSpace ℝ (Fin n),
      ∃ (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (k : ℕ)
        (Q : Fin k → Set (EuclideanSpace ℝ (Fin n))),
        (∀ i : Fin n, V (b i) ≤ 1) ∧
        (k : ℝ) ≤ C * (volume {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1}).toReal⁻¹ ∧
        (∀ h : Fin k, ∃ a : EuclideanSpace ℝ (Fin n), Q h =
          (fun t : Fin n → ℝ => a + η • (∑ i : Fin n, t i • b i)) '' Icc 0 1) ∧
        (∀ h : Fin k, IsCompact (Q h) ∧ 0 < volume (Q h) ∧ Q h ⊆ Metric.ball c 1) ∧
        d ≤ ∑ h : Fin k, (volume (Q h)).toReal ∧
        (∑ h : Fin k, volume.restrict (Q h)) ≤ volume.restrict (Metric.ball c 1) := by
  classical
  let d := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 4))).toReal / (2 : ℝ) ^ n
  have hd : 0 < d := div_pos
    (ENNReal.toReal_pos (Metric.measure_ball_pos volume _ (by norm_num)).ne' measure_ball_lt_top.ne)
    (by positivity)
  refine ⟨d, hd, fun η hη hnη => ?_⟩
  let p : ℝ := η ^ n / (2 : ℝ) ^ n
  have hp : 0 < p := div_pos (pow_pos hη n) (by positivity)
  let C := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal / p
  have hC : 0 < C := div_pos
    (ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne) hp
  refine ⟨C, hC, fun V hV hdom c => ?_⟩
  obtain ⟨b, hbV, hbnorm, hbdet⟩ := exists_adapted_basis V hV hdom
  obtain ⟨k, a, hsub, hdisj, hcover⟩ := hpacking b hbnorm η hη hnη c
  let Q : Fin k → Set (EuclideanSpace ℝ (Fin n)) := fun h => cube b (a h) η
  have hQcompact (h : Fin k) : IsCompact (Q h) := hcompact b (a h) η
  have hQvol (h : Fin k) : (volume (Q h)).toReal =
      η ^ n * |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b| := by
    rw [show Q h = cube b (a h) η from rfl, hvolume b (a h) η hη.le,
      ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hη.le n) (abs_nonneg _))]
  have hQpos (h : Fin k) : 0 < volume (Q h) := by
    rw [show Q h = cube b (a h) η from rfl, hvolume b (a h) η hη.le]
    exact ENNReal.ofReal_pos.mpr (mul_pos (pow_pos hη n)
      (abs_pos.mpr ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.isUnit_det b).ne_zero))
  have hlower (h : Fin k) : p * (volume {x | V x ≤ 1}).toReal ≤
      (volume (Q h)).toReal := by
    rw [hQvol]
    dsimp only [p]
    calc
      η ^ n / 2 ^ n * (volume {x | V x ≤ 1}).toReal =
          η ^ n * ((volume {x | V x ≤ 1}).toReal / 2 ^ n) := by ring
      _ ≤ η ^ n * |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b| :=
        mul_le_mul_of_nonneg_left hbdet (pow_nonneg hη.le n)
  have hcount := card_bound_of_volume Q c hQcompact hdisj hsub hp
    (volume_unit_body_toReal_pos V hV hdom) hlower
  refine ⟨b, k, Q, hbV, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Measure.addHaar_ball_center volume c, C] using hcount
  · intro h
    exact ⟨a h, hcube b (a h) η⟩
  · intro h
    exact ⟨hQcompact h, hQpos h, hsub h⟩
  · exact mass_bound_of_cover Q c hQcompact hcover
  · exact sum_restrict_le_of_disjoint volume Q (Metric.ball c 1)
      (fun h => (hQcompact h).measurableSet) hdisj hsub

end Submission.Obl.k4_adapted_affine_cube_cover
