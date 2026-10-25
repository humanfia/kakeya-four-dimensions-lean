import Submission.Obl.k4_matching_good_step_increment.Interfaces

open Filter
open scoped Topology

namespace Submission.Obl.k4_matching_good_step_increment

-- Adapted from x0185, o056, Limits.lean, commit 03104e2.
/-- Arbitrarily small exponent losses and arbitrarily large scales detect the sign. -/
theorem nonneg_of_cofinal_power_bound {c K s : ℝ} (hc : 0 < c)
    (h : ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R →
      ∃ N : ℝ, R ≤ N ∧ c ≤ K * N ^ (s + ε)) : 0 ≤ s := by
  by_contra hs
  have hs : s < 0 := lt_of_not_ge hs
  have ht : Tendsto (fun N : ℝ => K * N ^ (s + (-s / 2))) atTop (𝓝 0) := by
    simpa only [neg_neg, mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_rpow_neg_atTop (y := -(s + (-s / 2))) (by linarith)))
  obtain ⟨R, hR⟩ := eventually_atTop.mp (ht.eventually_lt_const hc)
  obtain ⟨N, hN, hbound⟩ := h (-s / 2) (by linarith) (max 2 R) (le_max_left _ _)
  have hsmall := hR N ((le_max_right _ _).trans hN)
  linarith

def endpointPullback (v : ℕ) (U : Fin (v + 1) → ℝ) (s₀ K : ℝ)
    (T : Set (ℝ × (Fin v → ℝ))) : Set (ℝ × (Fin v → ℝ)) :=
  {x | |x.1| ≤ 1 ∧ (∀ p : Fin v, |x.2 p| ≤ 1) ∧
    (∀ p r : Fin v, p ≠ r → K⁻¹ ≤ |x.2 p - x.2 r|) ∧
    (x.1, fun j : Fin v =>
      (U 0 * (x.1 - s₀) ^ ((j : ℕ) + 1) +
        ∑ p : Fin v, (U p.succ - U p.castSucc) *
          (x.1 - x.2 p) ^ ((j : ℕ) + 1)) /
      (((j : ℕ) + 1).factorial : ℝ)) ∈ T}

noncomputable def targetExponent (v q : ℕ) : ℝ :=
  (1 / (v : ℝ) + ((v : ℝ) + 1) / 2) / (q : ℝ)

/-- Apply the existing endpoint theorem to each member of the finite mixture. -/
theorem certificate_power_bound (hEnd : EndpointBound) (v : ℕ) (hv : 1 ≤ v) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q : ℕ) (Δ θ κ N : ℝ), 2 ≤ N →
      Certificate v q Δ θ κ N →
      1 / 4 ≤ N ^ (Δ - targetExponent v q + ((v : ℝ) + 1) * θ +
        ((A : ℝ) + 2) * κ) := by
  obtain ⟨A, hA, hE⟩ := hEnd v hv
  refine ⟨A, hA, ?_⟩
  intro q Δ θ κ N hN hcert
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  obtain ⟨K, n, w, U, s₀, T, hK, hKN, hw, hsum, hU, hs₀, hgap, hT, hvol, hlower⟩ := hcert
  have hK0 : 0 ≤ K := by linarith
  change MeasureTheory.volume T ≤ ENNReal.ofReal (K * N ^ (Δ - targetExponent v q)) at hvol
  change 1 / 4 ≤ K * N ^ (((v : ℝ) + 1) * θ) *
    (∑ i : Fin n, w i * (MeasureTheory.volume (endpointPullback v (U i) s₀ K T)).toReal) at hlower
  have hvol_i (i : Fin n) :
      (MeasureTheory.volume (endpointPullback v (U i) s₀ K T)).toReal ≤
        K ^ A * (K * N ^ (Δ - targetExponent v q)) := by
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    have hi := hE K hK (U i) s₀ T (hU i) hs₀ (hgap i) hT
    change MeasureTheory.volume (endpointPullback v (U i) s₀ K T) ≤ _ at hi
    calc
      _ ≤ ENNReal.ofReal (K ^ A) * MeasureTheory.volume T := hi
      _ ≤ ENNReal.ofReal (K ^ A) * ENNReal.ofReal (K * N ^ (Δ - targetExponent v q)) :=
        mul_le_mul le_rfl hvol (by positivity) (by positivity)
      _ = ENNReal.ofReal (K ^ A * (K * N ^ (Δ - targetExponent v q))) :=
        (ENNReal.ofReal_mul (pow_nonneg hK0 A)).symm
  have hsum_i :
      (∑ i : Fin n, w i * (MeasureTheory.volume (endpointPullback v (U i) s₀ K T)).toReal) ≤
      K ^ A * (K * N ^ (Δ - targetExponent v q)) := by
    calc
      _ ≤ ∑ i : Fin n, w i * (K ^ A * (K * N ^ (Δ - targetExponent v q))) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hvol_i i) (hw i))
      _ = (∑ i : Fin n, w i) * (K ^ A * (K * N ^ (Δ - targetExponent v q))) :=
        (Finset.sum_mul ..).symm
      _ ≤ 1 * (K ^ A * (K * N ^ (Δ - targetExponent v q))) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = _ := one_mul _
  calc
    1 / 4 ≤ K * N ^ (((v : ℝ) + 1) * θ) *
        (∑ i : Fin n, w i * (MeasureTheory.volume (endpointPullback v (U i) s₀ K T)).toReal) := hlower
    _ ≤ K * N ^ (((v : ℝ) + 1) * θ) * (K ^ A * (K * N ^ (Δ - targetExponent v q))) :=
      mul_le_mul_of_nonneg_left hsum_i (by positivity)
    _ = K ^ (A + 2) * N ^ (Δ - targetExponent v q + ((v : ℝ) + 1) * θ) := by
      rw [Real.rpow_add hNpos, pow_add]
      ring
    _ ≤ (N ^ κ) ^ (A + 2) * N ^ (Δ - targetExponent v q + ((v : ℝ) + 1) * θ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hK0 hKN _) (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_add hNpos]
      congr 1
      push_cast
      ring

/-- The finite-N certificates force the limiting local increment. -/
theorem increment_of_cofinal_certificates (hEnd : EndpointBound)
    (v q : ℕ) (hv : 1 ≤ v) (Δ θ : ℝ)
    (h : ∀ κ : ℝ, 0 < κ → ∀ R : ℝ, 2 ≤ R →
      ∃ N : ℝ, R ≤ N ∧ Certificate v q Δ θ κ N) :
    targetExponent v q - ((v : ℝ) + 1) * θ ≤ Δ := by
  obtain ⟨A, _, hA⟩ := certificate_power_bound hEnd v hv
  have hsign : 0 ≤ Δ - targetExponent v q + ((v : ℝ) + 1) * θ := by
    apply nonneg_of_cofinal_power_bound (c := 1 / 4) (K := 1) (by norm_num)
    intro ε hε R hR
    have hApos : 0 < (A : ℝ) + 2 := by positivity
    obtain ⟨N, hN, hcert⟩ := h (ε / ((A : ℝ) + 2)) (div_pos hε hApos) R hR
    refine ⟨N, hN, ?_⟩
    have hb := hA q Δ θ (ε / ((A : ℝ) + 2)) N (hR.trans hN) hcert
    simpa only [mul_div_cancel₀ ε (ne_of_gt hApos), one_mul] using hb
  linarith

/-- The volume exponent exceeds the requested increment, with spare error. -/
theorem targetExponent_sub_loss_le (J v q : ℕ) (hv : 1 ≤ v) (hvJ : v ≤ J)
    (hq : 1 ≤ q) (δ : ℝ) (hδ : 0 < δ) :
    (1 + 1 / (v : ℝ) - δ) / (q : ℝ) ≤
      targetExponent v q - ((v : ℝ) + 1) * (δ / (4 * ((J : ℝ) + 1) * (q : ℝ))) := by
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hvJR : (v : ℝ) ≤ J := by exact_mod_cast hvJ
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hJR : 0 < (J : ℝ) + 1 := by positivity
  have hcoef : ((v : ℝ) + 1) / (4 * ((J : ℝ) + 1)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hloss : ((v : ℝ) + 1) * (δ / (4 * ((J : ℝ) + 1) * (q : ℝ))) ≤ δ / (q : ℝ) := by
    calc
      _ = (((v : ℝ) + 1) / (4 * ((J : ℝ) + 1))) * (δ / (q : ℝ)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ 1 * (δ / (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := one_mul _
  have hmain : (1 + 1 / (v : ℝ)) / (q : ℝ) ≤ targetExponent v q := by
    unfold targetExponent
    apply div_le_div_of_nonneg_right _ hqR.le
    linarith
  rw [sub_div]
  linarith

end Submission.Obl.k4_matching_good_step_increment
