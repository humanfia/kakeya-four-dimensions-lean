-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.PrismCompact.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.PrismInterface
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file PrismCompact.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

/-- The union is at least as large as the average shading. -/
lemma shading_average_le_union {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r)
    (Z : Fin n → Set Space)
    (hden : ENNReal.ofReal (r * n) ≤ ∑ i, volume (Z i)) :
    ENNReal.ofReal r ≤ volume (⋃ i, Z i) := by
  have hsum := hden.trans (Finset.sum_le_sum (fun i _ =>
    measure_mono (Set.subset_iUnion Z i)))
  have hleft : ENNReal.ofReal (r * n) = (n : ENNReal) * ENNReal.ofReal r := by
    rw [ENNReal.ofReal_mul hr, ENNReal.ofReal_natCast, mul_comm]
  rw [hleft] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hn.ne') (by simp)).mp hsum

/-- The small-width formulation extends to all widths by a compact-range estimate. -/
theorem prism_frostman_all_scales {σ ω : ℝ} (hσ : 0 ≤ σ) (hω : 0 ≤ ω)
    (hF : PrismFrostmanEstimate σ ω) :
    ∀ e : ℝ, 0 < e → ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
    ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 1 →
    ∀ (n : ℕ) (P Z : Fin n → Set Space) (c e₁ e₂ e₃ : Fin n → Space),
    0 < n → (∀ i, Orthonormal ℝ ![e₁ i, e₂ i, e₃ i]) →
    (∀ i, Convex ℝ (P i)) → (∀ i, MeasurableSet (P i)) →
    (∀ i, {y | |inner ℝ (e₁ i) (y - c i)| ≤ s / 10 ∧
      |inner ℝ (e₂ i) (y - c i)| ≤ t / 10 ∧
      |inner ℝ (e₃ i) (y - c i)| ≤ (1 / 10 : ℝ)} ⊆ P i) →
    (∀ i, P i ⊆ {y | |inner ℝ (e₁ i) (y - c i)| ≤ 10 * s ∧
      |inner ℝ (e₂ i) (y - c i)| ≤ 10 * t ∧
      |inner ℝ (e₃ i) (y - c i)| ≤ (10 : ℝ)}) →
    (∀ i, P i ⊆ Metric.ball 0 10) →
    (∀ i j, i ≠ j → volume (P i ∩ P j) ≤
      (1 / 2 : ENNReal) * volume (P i)) →
    (∀ i, MeasurableSet (Z i)) → (∀ i, Z i ⊆ P i) →
    ENNReal.ofReal (s ^ η * n * s * t) ≤ ∑ i, volume (Z i) →
    (∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {i | P i ⊆ U}) ≤
        ENNReal.ofReal (s ^ (-η) * n) * volume U) →
    (∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (Set.ncard {i | P i ⊆ U}) * ENNReal.ofReal ((s * t) ^ 2) ≤
        ENNReal.ofReal (s ^ (-η)) * (volume U) ^ 2) →
    ENNReal.ofReal (A * s ^ e * t ^ ω * (n * (s * t) ^ 2) ^ (σ / 2)) ≤
      volume (⋃ i, Z i) := by
  intro e he
  obtain ⟨A, hA, η, hη, d₀, hd₀, hest⟩ := hF e he
  let d : ℝ := min d₀ 1
  have hd : 0 < d := lt_min hd₀ zero_lt_one
  let V : ℝ := (volume (ball (0 : Space) 10)).toReal
  let M : ℝ := 1 + d ^ (-η) * V ^ 2
  have hM : 0 < M := by dsimp [M]; positivity
  let W : ℝ := M ^ (σ / 2)
  have hW : 0 < W := Real.rpow_pos_of_pos hM _
  let B : ℝ := d ^ (η + 2) / W
  have hB : 0 < B := div_pos (Real.rpow_pos_of_pos hd _) hW
  refine ⟨min A B, lt_min hA hB, η, hη, ?_⟩
  intro s t hs hst ht n P Z c e₁ e₂ e₃ hn hframe hconv hPm hinner houter
    hball hover hZm hZP hden hfrost hquad
  have htpos : 0 < t := hs.trans_le hst
  have hs1 : s ≤ 1 := hst.trans ht
  by_cases hsmall : s ≤ d₀
  · refine (ENNReal.ofReal_le_ofReal ?_).trans
      (hest s t hs hst ht hsmall n P Z c e₁ e₂ e₃ hn hframe hconv hPm
        hinner houter hball hover hZm hZP hden hfrost hquad)
    gcongr
    exact min_le_left _ _
  have hds : d ≤ s := (min_le_left _ _).trans (le_of_not_ge hsmall)
  have hfull : {i | P i ⊆ ball (0 : Space) 10} = (Set.univ : Set (Fin n)) :=
    Set.eq_univ_of_forall hball
  have hcountE := hquad (ball 0 10) (convex_ball _ _)
  rw [hfull, Set.ncard_univ, Nat.card_fin] at hcountE
  have hcount : (n : ℝ) * (s * t) ^ 2 ≤ s ^ (-η) * V ^ 2 := by
    have h := ENNReal.toReal_mono (by finiteness) hcountE
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg n),
      ENNReal.toReal_ofReal (sq_nonneg (s * t)),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hs.le (-η)), ENNReal.toReal_pow, V] using h
  have hcountM : (n : ℝ) * (s * t) ^ 2 ≤ M := by
    calc
      _ ≤ s ^ (-η) * V ^ 2 := hcount
      _ ≤ d ^ (-η) * V ^ 2 := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hd hds (by linarith)) (sq_nonneg V)
      _ ≤ M := by dsimp [M]; linarith
  have hweight : ((n : ℝ) * (s * t) ^ 2) ^ (σ / 2) ≤ W :=
    Real.rpow_le_rpow (by positivity) hcountM (by positivity)
  have hsp : s ^ e ≤ 1 := Real.rpow_le_one hs.le hs1 he.le
  have htp : t ^ ω ≤ 1 := Real.rpow_le_one htpos.le ht hω
  have hcoeff : min A B * s ^ e * t ^ ω ≤ B := by
    calc
      _ ≤ min A B * 1 * 1 := by gcongr
      _ ≤ B := by simpa using min_le_right A B
  have htarget : min A B * s ^ e * t ^ ω * ((n : ℝ) * (s * t) ^ 2) ^ (σ / 2) ≤
      d ^ (η + 2) := by
    calc
      _ ≤ B * W := mul_le_mul hcoeff hweight (by positivity) hB.le
      _ = _ := by dsimp [B]; field_simp
  have hbase : d ^ (η + 2) ≤ s ^ η * s * t := by
    rw [Real.rpow_add hd, Real.rpow_two]
    calc
      _ ≤ s ^ η * (s * t) := mul_le_mul
        (Real.rpow_le_rpow hd.le hds hη.le)
        (by simpa [pow_two] using mul_le_mul hds (hds.trans hst) hd.le hs.le) (sq_nonneg d)
        (Real.rpow_nonneg hs.le η)
      _ = _ := by ring
  calc
    _ ≤ ENNReal.ofReal (s ^ η * s * t) := ENNReal.ofReal_le_ofReal (htarget.trans hbase)
    _ ≤ volume (⋃ i, Z i) := shading_average_le_union hn (by positivity) Z (by
      convert hden using 1 <;> congr 1 <;> ring)

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
