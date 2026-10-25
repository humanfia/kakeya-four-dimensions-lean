import Submission.Obl.k4_weighted_convex_tubes.Numerics

namespace Submission.Obl.k4_weighted_convex_tubes

open MeasureTheory Set

theorem weighted_of_sampling (hsampling : SamplingPrinciple)
    (hset : ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ a : ℝ, 0 < a ∧ EstimateAt ε α a) :
    ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (w : Fin n → ℝ) (A : ℝ),
    (∀ i, ‖v i‖ = 1) →
    (∀ i, tube (scale D) (x i) (v i) ⊆ Metric.ball 0 1) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube (scale D) (x i) (v i)) →
    (∀ i, 0 < w i) → 0 < A →
    (∀ i, c * (D : ℝ) ^ (-η) / (D : ℝ) ^ 2 ≤ (volume (Y i)).toReal) →
    (∀ W : Set Space, Convex ℝ W → ∀ F : Finset (Fin n),
      (∀ i ∈ F, tube (scale D) (x i) (v i) ⊆ W) →
      ENNReal.ofReal ((∑ i ∈ F, w i) / (D : ℝ) ^ 2) ≤
        ENNReal.ofReal A * volume W) →
    (∑ i, w i) / (D : ℝ) ^ 2 ≤ C * A * (D : ℝ) ^ ε * (volume (⋃ i, Y i)).toReal := by
  classical
  intro ε hε c hc
  obtain ⟨α, hα, a, ha, hestimate⟩ := hset ε hε
  obtain ⟨K, hK, r₀, hr₀, hsample⟩ := hsampling α hα
  let η := min (α / 2) ε
  have hη : 0 < η := lt_min (by positivity) hε
  have hηα : 2 * η ≤ α := by have := min_le_left (α / 2) ε; dsimp [η]; linarith
  have hηε : η ≤ ε := min_le_right _ _
  obtain ⟨N, hN, hlarge⟩ := eventual_dense hα hη hηα hc hr₀
  let b : ℝ := (volume (Metric.ball (0 : Space) 1)).toReal
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  let C₁ : ℝ := K / c
  let C₂ : ℝ := 10000 * K * (100 : ℝ) ^ ε / a
  let C₃ : ℝ := b / c * (N : ℝ) ^ (η + 2)
  let C := C₁ + C₂ + C₃ + 1
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hC₃ : 0 ≤ C₃ := by dsimp [C₃]; positivity
  have hC₁C : C₁ ≤ C := by dsimp [C]; linarith
  have hC₂C : C₂ ≤ C := by dsimp [C]; linarith
  have hC₃C : C₃ ≤ C := by dsimp [C]; linarith
  refine ⟨η, hη, C, by dsimp [C]; positivity, ?_⟩
  intro D hD n x v Y w A hv hball hY hYT hw hA hdense hcluster
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hd1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hd : (0 : ℝ) < D := by linarith
  have hDsq : 0 < (D : ℝ) ^ 2 := sq_pos_of_pos hd
  let T : ℝ := ∑ i, w i
  let V : ℝ := (volume (⋃ i, Y i)).toReal
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => (hw i).le
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hfinite : volume (⋃ i, Y i) ≠ ⊤ := union_volume_ne_top hball hYT
  have hYi (i) : volume (Y i) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (measure_mono (subset_iUnion Y i))
  have hVdense : c * (D : ℝ) ^ (-η) / (D : ℝ) ^ 2 ≤ V :=
    (hdense ⟨0, hnpos⟩).trans (ENNReal.toReal_mono hfinite
      (measure_mono (subset_iUnion Y ⟨0, hnpos⟩)))
  have hrecip := density_reciprocal hD hc hVdense
  have hpow : (D : ℝ) ^ η ≤ (D : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hd1 hηε
  have hpow1 : 1 ≤ (D : ℝ) ^ ε := Real.one_le_rpow hd1 hε.le
  change T / (D : ℝ) ^ 2 ≤ C * A * (D : ℝ) ^ ε * V
  by_cases hND : N ≤ D
  · obtain ⟨hr₀D, hden⟩ := hlarge D hND
    have hwcluster : WeightedClustering (scale D) x v w A := by
      intro W hW F hFW
      have hsum : 0 ≤ ∑ i ∈ F, w i := Finset.sum_nonneg fun i _ => (hw i).le
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hcluster W hW F hFW)
      simpa only [div_eq_mul_inv, one_div, one_mul] using
        mul_le_mul_of_nonneg_left (scale_sq_le hD) hsum
    rcases hsample (scale D) (scale_pos hD) (scale_le hD) hr₀D
      n x v w A hv hball hw hA hwcluster with hsmall | ⟨S, hmass, hcount⟩
    · calc
        T / (D : ℝ) ^ 2 = T * (1 / (D : ℝ) ^ 2) := by ring
        _ ≤ (K * A) * (((D : ℝ) ^ η / c) * V) :=
          mul_le_mul hsmall hrecip (by positivity) (by positivity)
        _ = C₁ * A * (D : ℝ) ^ η * V := by dsimp [C₁]; ring
        _ ≤ C₁ * A * (D : ℝ) ^ ε * V := by gcongr
        _ ≤ C * A * (D : ℝ) ^ ε * V := by gcongr
    · have hdenY (i) : ENNReal.ofReal (scale D ^ α * scale D ^ 2) ≤ volume (Y i) :=
        (ENNReal.ofReal_le_ofReal hden).trans ((ofReal_le_volume_iff (hYi i)).mpr (hdense i))
      have hvol : a * scale D ^ ε * (S.card : ℝ) * scale D ^ 2 ≤ V :=
        (ofReal_le_volume_iff hfinite).mp
          (estimate_subfamily hestimate (scale_pos hD) (scale_le hD) x v Y
            hv hball hY hYT hdenY S hcount)
      let q : ℝ := (100 : ℝ) ^ ε * (D : ℝ) ^ ε
      have hq : 0 < q := by dsimp [q]; positivity
      have hqcancel : scale D ^ ε * q = 1 := scale_rpow_inv hD ε
      have hcard : (S.card : ℝ) * scale D ^ 2 ≤ (q / a) * V := by
        have hh := mul_le_mul_of_nonneg_left hvol (div_nonneg hq.le ha.le)
        have heq : (q / a) * (a * scale D ^ ε * (S.card : ℝ) * scale D ^ 2) =
            (S.card : ℝ) * scale D ^ 2 := by
          calc
            _ = (q / a * a) * scale D ^ ε * ((S.card : ℝ) * scale D ^ 2) := by ring
            _ = (scale D ^ ε * q) * ((S.card : ℝ) * scale D ^ 2) := by
              rw [div_mul_cancel₀ _ ha.ne']; ring
            _ = _ := by rw [hqcancel, one_mul]
        rwa [heq] at hh
      calc
        T / (D : ℝ) ^ 2 = 10000 * T * scale D ^ 2 := by rw [scale_sq hD]; ring
        _ ≤ 10000 * (K * A * (S.card : ℝ)) * scale D ^ 2 := by gcongr
        _ = (10000 * K * A) * ((S.card : ℝ) * scale D ^ 2) := by ring
        _ ≤ (10000 * K * A) * ((q / a) * V) := by gcongr
        _ = C₂ * A * (D : ℝ) ^ ε * V := by dsimp [C₂, q]; ring
        _ ≤ C * A * (D : ℝ) ^ ε * V := by gcongr
  · have hDN : D ≤ N := by omega
    have hglobal : T / (D : ℝ) ^ 2 ≤ A * b := by
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA.le hb)).mp
      rw [ENNReal.ofReal_mul hA.le, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
      simpa only [T] using
        hcluster (Metric.ball 0 1) (convex_ball 0 1) Finset.univ (fun i _ => hball i)
    have hrecip' : 1 ≤ ((D : ℝ) ^ (η + 2) / c) * V := by
      calc
        1 = (D : ℝ) ^ 2 * (1 / (D : ℝ) ^ 2) := by field_simp
        _ ≤ (D : ℝ) ^ 2 * (((D : ℝ) ^ η / c) * V) := by gcongr
        _ = _ := by rw [Real.rpow_add hd, Real.rpow_two]; ring
    have hDNpow : (D : ℝ) ^ (η + 2) ≤ (N : ℝ) ^ (η + 2) :=
      Real.rpow_le_rpow hd.le (Nat.cast_le.mpr hDN) (by linarith)
    calc
      T / (D : ℝ) ^ 2 ≤ A * b := hglobal
      _ = (A * b) * 1 := by ring
      _ ≤ (A * b) * (((D : ℝ) ^ (η + 2) / c) * V) := by gcongr
      _ = (b / c * (D : ℝ) ^ (η + 2)) * A * V := by ring
      _ ≤ C₃ * A * V := by dsimp [C₃]; gcongr
      _ ≤ C₃ * A * (D : ℝ) ^ ε * V :=
        mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (mul_nonneg hC₃ hA.le) hpow1) hV
      _ ≤ C * A * (D : ℝ) ^ ε * V := by gcongr

end Submission.Obl.k4_weighted_convex_tubes
