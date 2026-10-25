import Submission.Obl.k4_adapted_oscillation_tests.Tiles
import Submission.Obl.k4_adapted_oscillation_tests.TileOscillation

/-!
# Assembly of the adapted oscillation tests

Take the maximal frame `T` of the unit body (`Frame.lean`), the scaled map `L = η • T` and the
tiles `affineCube L (a h)` of `Tiles.lean`. On each tile the oscillation tests force
`volume / 2 ≤ η ∑ i ∫ ‖Df (T eᵢ)‖` (`tile_oscillation`); summing over the disjoint tiles inside
`B(c,1)`, whose total volume is at least `2^-n volume B(0,1/4)`, gives a direction `T eᵢ` with a
large integral once `η` is small. The count of tiles is `≤ volume B(0,1) / (η^n |det T|)`, and
`volume K ≤ 2^n |det T|`.
-/

namespace Submission.Obl.k4_adapted_oscillation_tests

open MeasureTheory Metric Set

variable {n : ℕ}

/-- A linear map sending the standard basis into the closed unit ball is bounded by the
`ℓ¹` norm of the coordinates. -/
theorem norm_apply_le_sum_abs
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : ∀ i, ‖T (EuclideanSpace.single i 1)‖ ≤ 1) (w : EuclideanSpace ℝ (Fin n)) :
    ‖T w‖ ≤ ∑ j, |w j| := by
  have hw : w = ∑ j, w j • EuclideanSpace.single j (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  calc ‖T w‖ = ‖∑ j, w j • T (EuclideanSpace.single j 1)‖ := by
        conv_lhs => rw [hw]
        simp [map_sum, map_smul]
    _ ≤ ∑ j, ‖w j • T (EuclideanSpace.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ j, |w j| := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (hT j)

theorem main (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : Seminorm ℝ (EuclideanSpace ℝ (Fin n)), Continuous V →
      (∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ V v) → ∀ c : EuclideanSpace ℝ (Fin n),
      ∃ (k : ℕ) (Q : Fin k → Set (EuclideanSpace ℝ (Fin n))),
        (k : ℝ) ≤ C * (volume {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1}).toReal⁻¹ ∧
        (∀ h : Fin k, IsCompact (Q h) ∧ 0 < volume (Q h) ∧ Q h ⊆ ball c 1) ∧
        ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f →
          (∀ h : Fin k, |∫ x in Q h, f x| ≤ (volume (Q h)).toReal / 2 ∧
            (volume (Q h)).toReal ≤ ∫ x in Q h, |f x|) →
          ∃ v : EuclideanSpace ℝ (Fin n), V v ≤ 1 ∧
            A ≤ ∫ x in ball c 1, ‖(fderiv ℝ f x) v‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set β : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal with hβ
  set γ : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 4))).toReal with hγ
  have hβpos : 0 < β :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hγpos : 0 < γ :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 (by norm_num)).ne' measure_ball_lt_top.ne
  set η : ℝ := min (1 / (8 * n)) (γ / (2 ^ (n + 1) * n * A)) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hηn : η * n ≤ 1 / 8 := by
    have h : η ≤ 1 / (8 * n) := min_le_left _ _
    calc η * n ≤ 1 / (8 * n) * n := by gcongr
      _ = 1 / 8 := by field_simp
  have hηA : η * n * A * 2 ^ (n + 1) ≤ γ := by
    have h : η ≤ γ / (2 ^ (n + 1) * n * A) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  refine ⟨2 ^ n * β / η ^ n, by positivity, ?_⟩
  intro V hV hdom c
  obtain ⟨T, hTV, hTdet, hKvol⟩ := exists_frameMap V hV hdom
  have hTnorm : ∀ i, ‖T (EuclideanSpace.single i 1)‖ ≤ 1 := fun i => (hdom _).trans (hTV i)
  have hdetηT : (η • T).det = η ^ n * T.det := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul,
      finrank_euclideanSpace_fin]
  have hdetηT0 : (η • T).det ≠ 0 := by
    rw [hdetηT]
    exact mul_ne_zero (pow_ne_zero _ hηpos.ne') hTdet
  set L := (η • T).toContinuousLinearEquivOfDetNeZero hdetηT0 with hLdef
  have hLapply : ∀ x, L x = η • T x := fun x => rfl
  have hLdet : (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).det =
      η ^ n * T.det := by
    rw [hLdef, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero, hdetηT]
  have hLdet' : LinearMap.det (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
      η ^ n * T.det := hLdet
  have hLb : ∀ w, ‖L w‖ ≤ η * ∑ j, |w j| := by
    intro w
    rw [hLapply, norm_smul, Real.norm_eq_abs, abs_of_pos hηpos]
    exact mul_le_mul_of_nonneg_left (norm_apply_le_sum_abs T hTnorm w) hηpos.le
  obtain ⟨k, a, hsub, hdisj, hcount, hcover⟩ := tiling L η hηpos hηn hLb c
  have hQ : ∀ h, affineCube L (a h) =
      (fun x => a h + L x) '' (WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 1) := fun h => rfl
  have hvolQ : ∀ h, (volume (affineCube L (a h))).toReal = η ^ n * |T.det| := by
    intro h
    rw [volume_affineCube_toReal, hLdet', abs_mul, abs_of_pos (pow_pos hηpos n)]
  refine ⟨k, fun h => affineCube L (a h), ?_, ?_, ?_⟩
  · -- the number of tests
    have hball1 : volume (ball c 1) = volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      Measure.addHaar_ball_center _ _ _
    have hk1 : (k : ℝ) * (η ^ n * |T.det|) ≤ β := by
      have h1 := ENNReal.toReal_mono (by rw [hball1]; exact measure_ball_lt_top.ne) hcount
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (abs_nonneg _),
        hLdet, abs_mul, abs_of_pos (pow_pos hηpos n), hball1] at h1
      exact h1
    have hK1 : (volume {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1}).toReal ≤ 2 ^ n * |T.det| := by
      have h1 := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hKvol
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at h1
      simpa using h1
    have hK0 : 0 < (volume {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1}).toReal :=
      ENNReal.toReal_pos (volume_unitBody_pos V hV).ne' (volume_unitBody_lt_top V hdom).ne
    rw [← div_eq_mul_inv, le_div_iff₀ hK0]
    have hηn_pos : 0 < η ^ n := pow_pos hηpos n
    calc (k : ℝ) * (volume {v : EuclideanSpace ℝ (Fin n) | V v ≤ 1}).toReal
        ≤ k * (2 ^ n * |T.det|) := by gcongr
      _ = 2 ^ n / η ^ n * (k * (η ^ n * |T.det|)) := by field_simp
      _ ≤ 2 ^ n / η ^ n * β := by gcongr
      _ = 2 ^ n * β / η ^ n := by ring
  · intro h
    exact ⟨isCompact_affineCube L (a h), volume_affineCube_pos L (a h), hsub h⟩
  · intro f hf hosc
    set b : Fin n → EuclideanSpace ℝ (Fin n) := fun i => T (EuclideanSpace.single i 1) with hb
    have hcontg : ∀ v : EuclideanSpace ℝ (Fin n), Continuous fun x => ‖fderiv ℝ f x v‖ :=
      fun v => ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm
    have hint : ∀ v : EuclideanSpace ℝ (Fin n),
        IntegrableOn (fun x => ‖fderiv ℝ f x v‖) (ball c 1) volume := fun v =>
      ((hcontg v).continuousOn.integrableOn_compact (isCompact_closedBall c 1)).mono_set
        ball_subset_closedBall
    -- the estimate on one tile
    have htile : ∀ h, (volume (affineCube L (a h))).toReal / 2 ≤
        η * ∑ i, ∫ x in affineCube L (a h), ‖fderiv ℝ f x (b i)‖ := by
      intro h
      have h1 := tile_oscillation L (a h) f hf (hosc h).1 (hosc h).2
      simp only [hLapply, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hηpos,
        integral_const_mul] at h1
      rwa [← Finset.mul_sum] at h1
    -- the tiles are disjoint inside `B(c,1)`
    have hsum_i : ∀ i, ∑ h, ∫ x in affineCube L (a h), ‖fderiv ℝ f x (b i)‖ ≤
        ∫ x in ball c 1, ‖fderiv ℝ f x (b i)‖ := by
      intro i
      rw [← integral_biUnion_finset Finset.univ
        (fun h _ => (isCompact_affineCube L (a h)).isClosed.measurableSet)
        (fun h _ h' _ hhh' => by simpa only [hQ] using hdisj hhh')
        (fun h _ => (hint (b i)).mono_set (hsub h))]
      refine setIntegral_mono_set (hint (b i))
        (Filter.Eventually.of_forall fun x => norm_nonneg _) (Filter.Eventually.of_forall ?_)
      intro x hx
      obtain ⟨h, -, hxh⟩ := Set.mem_iUnion₂.mp hx
      exact hsub h hxh
    -- total volume of the tiles
    have hvolsum : γ / 2 ^ n ≤ ∑ h, (volume (affineCube L (a h))).toReal := by
      have hball : volume (ball c (1 / 4)) =
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 4)) :=
        Measure.addHaar_ball_center _ _ _
      have h1 := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))
        hcover
      rw [hball, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (abs_nonneg _), hLdet, abs_mul, abs_of_pos (pow_pos hηpos n)] at h1
      rw [← hγ] at h1
      simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h1
      simp only [hvolQ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [div_le_iff₀ (by positivity)]
      linarith
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hlt : ∀ i, ∫ x in ball c 1, ‖fderiv ℝ f x (b i)‖ < A := fun i => hcon (b i) (hTV i)
    have h1 : ∑ h, (volume (affineCube L (a h))).toReal / 2 ≤
        η * ∑ i, ∫ x in ball c 1, ‖fderiv ℝ f x (b i)‖ := by
      calc ∑ h, (volume (affineCube L (a h))).toReal / 2
          ≤ ∑ h, η * ∑ i, ∫ x in affineCube L (a h), ‖fderiv ℝ f x (b i)‖ :=
            Finset.sum_le_sum fun h _ => htile h
        _ = η * ∑ i, ∑ h, ∫ x in affineCube L (a h), ‖fderiv ℝ f x (b i)‖ := by
            rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ η * ∑ i, ∫ x in ball c 1, ‖fderiv ℝ f x (b i)‖ := by
            gcongr with i
            exact hsum_i i
    have h2 : ∑ i, ∫ x in ball c 1, ‖fderiv ℝ f x (b i)‖ < n * A := by
      calc ∑ i, ∫ x in ball c 1, ‖fderiv ℝ f x (b i)‖ < ∑ _i : Fin n, A :=
            Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i _ => hlt i
        _ = n * A := by simp
    have h3 : ∑ h, (volume (affineCube L (a h))).toReal / 2 =
        (∑ h, (volume (affineCube L (a h))).toReal) / 2 := by
      rw [Finset.sum_div]
    have h4 : η * ∑ i, ∫ x in ball c 1, ‖fderiv ℝ f x (b i)‖ < η * (n * A) :=
      mul_lt_mul_of_pos_left h2 hηpos
    have h5 : γ / 2 ^ n / 2 < η * (n * A) := by
      rw [h3] at h1
      have h8 : γ / 2 ^ n / 2 ≤ (∑ h, (volume (affineCube L (a h))).toReal) / 2 := by
        linarith [hvolsum]
      linarith
    have h6 : γ / 2 ^ n / 2 = γ / 2 ^ (n + 1) := by
      rw [pow_succ, div_div]
    rw [h6, div_lt_iff₀ (by positivity)] at h5
    have h7 : η * (n * A) * 2 ^ (n + 1) = η * n * A * 2 ^ (n + 1) := by ring
    linarith

end Submission.Obl.k4_adapted_oscillation_tests
