-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.PowerCellRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.CellRefinement
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.DyadicDepth
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Thickening
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file PowerCellRefinement.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridUnion)

private lemma depth_losses {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (hKr : K * r ≤ 1) (hsmall : 16384 * r ≤ 1) :
    8 * K * r ^ 2 ≤ 1 ∧ 128 * K * r ^ 2 ≤ 1 ∧ 16384 * K ^ 2 * r ^ 3 ≤ 1 := by
  have h8 : 8 * r ≤ 1 := by linarith
  have h128 : 128 * r ≤ 1 := by linarith
  have hp8 := mul_le_mul hKr h8 (by positivity : 0 ≤ 8 * r) zero_le_one
  have hp128 := mul_le_mul hKr h128 (by positivity : 0 ≤ 128 * r) zero_le_one
  have hsq := pow_le_pow_left₀ (mul_nonneg hK hr) hKr 2
  have hp := mul_le_mul hsq hsmall (by positivity : 0 ≤ 16384 * r) (by positivity)
  constructor
  · nlinarith only [hp8]
  constructor
  · nlinarith only [hp128]
  · nlinarith only [hp]

/-- The complete cell refinement with its losses expressed as powers of the original
scale, uniformly in the Frostman exponent. -/
theorem power_cell_refinement (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 < τ) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
    ∀ ζ s b : ℝ, 0 < s → s ≤ 1 →
    ∀ (n p : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space)
      (P : Fin p → Set Space),
    0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    (∀ i, ENNReal.ofReal (δ ^ ν * δ ^ 2) ≤ volume (Y i)) →
    Factored (δ ^ (-ζ)) b (fun i => tube δ (x i) (v i)) P →
    ∃ (S : Finset (Fin 3 → ℤ)) (t : ℝ) (k q : ℕ)
      (g : Fin k → Fin n) (h : Fin q → Fin p),
    0 < t ∧
    (∀ z ∈ S, ENNReal.ofReal (t * (27 * s ^ 3)) ≤ volume ((⋃ i, Y i) ∩ block s z) ∧
      volume ((⋃ i, Y i) ∩ block s z) ≤ ENNReal.ofReal (2 * t * (27 * s ^ 3))) ∧
    0 < k ∧ 0 < q ∧ Function.Injective g ∧ Function.Injective h ∧
    (∀ i, ENNReal.ofReal (δ ^ (ν + 2 * τ) * δ ^ 2) ≤
      volume (Y (g i) ∩ gridUnion s S)) ∧
    Factored (δ ^ (-(ν + 2 * ζ + 2 * τ))) b
      (fun i => tube δ (x (g i)) (v (g i))) (P ∘ h) ∧
    ∀ j, δ ^ (2 * ν + ζ + 3 * τ) * n ≤
      (q : ℝ) * Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ P (h j)} := by
  obtain ⟨d₁, hd₁, hdepth⟩ := dyadic_depth 18522 (ν + 2) (by norm_num) (by linarith) hτ
  obtain ⟨d₂, hd₂, hsmall⟩ := power_absorption 16384 hτ
  refine ⟨min d₁ (min d₂ 1), lt_min hd₁ (lt_min hd₂ zero_lt_one), ?_⟩
  intro δ hδ hδd ζ s b hs hs1 n p x v Y P hn hv hB hYm hYT hden hf
  have hδ1 : δ ≤ 1 := (hδd.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨K, hK, hKlow, hKhigh⟩ := hdepth δ hδ (hδd.trans (min_le_left _ _))
  have hsmall' := hsmall δ hδ
    ((hδd.trans (min_le_right _ _)).trans (min_le_left _ _))
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hlam : 0 < δ ^ ν := Real.rpow_pos_of_pos hδ _
  have hr : 0 < δ ^ τ := Real.rpow_pos_of_pos hδ _
  have hD : 0 < δ ^ (-ζ) := Real.rpow_pos_of_pos hδ _
  have hKpow : (K : ℝ) * δ ^ τ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hKhigh hr.le
    simpa only [Real.rpow_neg hδ.le, inv_mul_cancel₀ hr.ne'] using h
  obtain ⟨hloss8, hloss128, hloss16384⟩ := depth_losses hKr.le hr.le hKpow hsmall'
  have hlam1 : δ ^ ν ≤ 1 := Real.rpow_le_one hδ.le hδ1 hν
  have hLQ : δ ^ ν * δ ^ 2 ≤ 8 * δ ^ 2 := by nlinarith [sq_nonneg δ]
  have hupper (i : Fin n) : volume (Y i) ≤ ENNReal.ofReal (8 * δ ^ 2) := by
    calc
      _ ≤ volume (tube δ (x i) (v i) ∩ Metric.ball 0 1) :=
        measure_mono (subset_inter (hYT i) ((hYT i).trans (hB i)))
      _ ≤ _ := by simpa using tube_ball_volume_le (x i) (v i) 0 (hv i) (r := 1)
  have hKlow' : 18522 * (1 / 2 : ℝ) ^ K ≤ δ ^ ν * δ ^ 2 := by
    simpa only [Real.rpow_add hδ, Real.rpow_two] using hKlow
  obtain ⟨S, t, k, q, g, h, ht, hblocks, hk, hq, hg, hh, hpoint, hfact, hprod⟩ :=
    hf.cell_refinement hn hs hs1 (by positivity) hLQ Y hYm
      (fun i => (hYT i).trans (hB i)) hupper hden hK hKlow'
  have hdensity : δ ^ (ν + 2 * τ) = δ ^ ν * (δ ^ τ) ^ 2 := by
    rw [← Real.rpow_mul_natCast hδ.le τ 2, ← Real.rpow_add hδ]
    congr 1
    ring
  have herror : δ ^ (-(ν + 2 * ζ + 2 * τ)) =
      (δ ^ (-ζ)) ^ 2 / (δ ^ ν * (δ ^ τ) ^ 2) := by
    rw [← Real.rpow_mul_natCast hδ.le (-ζ) 2,
      ← Real.rpow_mul_natCast hδ.le τ 2, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
    congr 1
    ring
  have hproduct : δ ^ (2 * ν + ζ + 3 * τ) =
      (δ ^ ν) ^ 2 * (δ ^ τ) ^ 3 / δ ^ (-ζ) := by
    rw [← Real.rpow_mul_natCast hδ.le ν 2, ← Real.rpow_mul_natCast hδ.le τ 3,
      ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
    congr 1
    ring
  have hpointcoef : δ ^ (ν + 2 * τ) * δ ^ 2 ≤ δ ^ ν * δ ^ 2 / (8 * K) := by
    rw [hdensity, le_div_iff₀ (by positivity : (0 : ℝ) < 8 * K)]
    have h := mul_le_mul_of_nonneg_left hloss8 (by positivity : 0 ≤ δ ^ ν * δ ^ 2)
    nlinarith only [h]
  have herrcoef : 16 * K * (8 * δ ^ 2) * (δ ^ (-ζ)) ^ 2 / (δ ^ ν * δ ^ 2) ≤
      δ ^ (-(ν + 2 * ζ + 2 * τ)) := by
    rw [herror]
    have heq : 16 * K * (8 * δ ^ 2) * (δ ^ (-ζ)) ^ 2 / (δ ^ ν * δ ^ 2) =
        128 * K * (δ ^ (-ζ)) ^ 2 / δ ^ ν := by field_simp; ring
    rw [heq, div_le_div_iff₀ hlam (by positivity : 0 < δ ^ ν * (δ ^ τ) ^ 2)]
    have h := mul_le_mul_of_nonneg_left hloss128
      (by positivity : 0 ≤ δ ^ ν * (δ ^ (-ζ)) ^ 2)
    nlinarith only [h]
  have hprodcoef : δ ^ (2 * ν + ζ + 3 * τ) ≤
      (δ ^ ν * δ ^ 2) ^ 2 / (256 * (K : ℝ) ^ 2 * (8 * δ ^ 2) ^ 2 * δ ^ (-ζ)) := by
    have heq : (δ ^ ν * δ ^ 2) ^ 2 /
        (256 * (K : ℝ) ^ 2 * (8 * δ ^ 2) ^ 2 * δ ^ (-ζ)) =
        (δ ^ ν) ^ 2 / (16384 * (K : ℝ) ^ 2 * δ ^ (-ζ)) := by field_simp; ring
    rw [hproduct, heq, div_le_div_iff₀ hD (by positivity :
      0 < 16384 * (K : ℝ) ^ 2 * δ ^ (-ζ))]
    have h := mul_le_mul_of_nonneg_left hloss16384
      (by positivity : 0 ≤ (δ ^ ν) ^ 2 * δ ^ (-ζ))
    nlinarith only [h]
  refine ⟨S, t, k, q, g, h, (by positivity : 0 < (1 / 2 : ℝ) ^ (K + 1)).trans_le ht,
    hblocks, hk, hq, hg, hh, ?_, ?_, ?_⟩
  · intro i
    exact (ENNReal.ofReal_le_ofReal hpointcoef).trans (hpoint i)
  · exact hfact.mono_error herrcoef
  · intro j
    exact (mul_le_mul_of_nonneg_right hprodcoef (Nat.cast_nonneg n)).trans (hprod j)

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
