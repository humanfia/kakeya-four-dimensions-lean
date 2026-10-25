/- Adapted from this LOT tree, obligation o119, session x0404, commit b1aa67e,
   Submission/Obl/k4_finite_width_critical_contradiction/CompHomogSetup.lean. -/
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CompEncAe

/-!
# The encoded single world satisfies the hypotheses of o075

Encoding parameters at a sample with base `N`: hidden scale `σ = N ^ (-ρ₀)` (an exact dyadic
thickness when `ρ₀ log₂ N` is an integer), spacing `Λ = 2 (⌈N^M⌉ + 2)`, world `c` shifted by
`Λ c σ`.  When `ρ₀ ≥ 2M + 4` the encoded hidden coordinate lies in `[-1, 1]`, and the encoded
prior and event are tempered with exponent `6M + 4ρ₀ + 2`.
-/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp

attribute [local simp] encCoeff_zero encCoeff_one encCoeff_two encCoeff_three encCoeff_four encCoeff_five

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_dyadic_crop_worlds (BoolFormat PriorFormat EventFormat)

/-- The spacing between encoded worlds. -/
noncomputable def spacing (N : ℝ) (M : ℕ) : ℕ := 2 * (⌈N ^ M⌉₊ + 2)

theorem spacing_le {N : ℝ} (hN : 2 ≤ N) (M : ℕ) : (spacing N M : ℝ) ≤ N ^ (M + 3) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hM : (1 : ℝ) ≤ N ^ M := one_le_pow₀ hN1
  have hceil : (⌈N ^ M⌉₊ : ℝ) ≤ N ^ M + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h8 : (8 : ℝ) ≤ N ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN 3
  unfold spacing
  push_cast
  calc 2 * ((⌈N ^ M⌉₊ : ℝ) + 2) ≤ 2 * (N ^ M + 3) := by linarith
    _ ≤ 8 * N ^ M := by linarith
    _ ≤ N ^ 3 * N ^ M := by nlinarith
    _ = N ^ (M + 3) := by rw [← pow_add]; ring_nf

theorem half_spacing_gt {N : ℝ} (M : ℕ) (x : ℝ) (hx : |x| ≤ N ^ M) :
    |x| + 1 < (spacing N M : ℝ) / 2 := by
  have hceil : N ^ M ≤ (⌈N ^ M⌉₊ : ℝ) := Nat.le_ceil _
  unfold spacing
  push_cast
  linarith

/-- The encoded hidden coordinate is at most one. -/
theorem abs_enc_hidden_le {N σ B w : ℝ} {M W : ℕ} (hN : 2 ≤ N) (c : ℕ) (hc : c < W)
    (hW : (W : ℝ) ≤ N ^ M) (hσ0 : 0 ≤ σ) (hσ : σ * N ^ (2 * M + 4) ≤ 1)
    (hBw : |B * w| ≤ N ^ M) :
    |B * σ * w + (spacing N M : ℝ) * c * σ| ≤ 1 := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hM : (1 : ℝ) ≤ N ^ M := one_le_pow₀ hN1
  have hΛ := spacing_le hN M
  have hc' : (c : ℝ) ≤ W := by exact_mod_cast hc.le
  have hΛ0 : (0 : ℝ) ≤ spacing N M := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hA : |B * σ * w| = |B * w| * σ := by
    rw [show B * σ * w = (B * w) * σ by ring, abs_mul, abs_of_nonneg hσ0]
  have hB : |(spacing N M : ℝ) * c * σ| = (spacing N M : ℝ) * c * σ :=
    abs_of_nonneg (by positivity)
  have hΛc : (spacing N M : ℝ) * c ≤ N ^ (M + 3) * N ^ M :=
    mul_le_mul hΛ (hc'.trans hW) hc0 (by positivity)
  have hpow : N ^ (M + 3) * N ^ M = N ^ (2 * M + 3) := by rw [← pow_add]; ring_nf
  have hpow2 : N ^ (2 * M + 4) = N * N ^ (2 * M + 3) := by rw [pow_succ]; ring
  have hMle : N ^ M ≤ N ^ (2 * M + 3) := pow_le_pow_right₀ hN1 (by omega)
  calc |B * σ * w + (spacing N M : ℝ) * c * σ|
      ≤ |B * σ * w| + |(spacing N M : ℝ) * c * σ| := abs_add_le _ _
    _ = |B * w| * σ + (spacing N M : ℝ) * c * σ := by rw [hA, hB]
    _ ≤ N ^ M * σ + N ^ (2 * M + 3) * σ := by
        gcongr
        rw [← hpow]; exact hΛc
    _ ≤ σ * N ^ (2 * M + 4) := by
        rw [hpow2]
        nlinarith [mul_nonneg hσ0 (by positivity : (0:ℝ) ≤ N ^ (2 * M + 3))]
    _ ≤ 1 := hσ

/-- The encoded single-world sequence satisfies the format hypothesis of o075, for any
encoding scale `σ n` with `σ ≤ 1`, `σ⁻¹ ≤ N^ρ` and `σ N^(2M+4) ≤ 1`. -/
theorem encoded_format075 (N K : ℕ → ℝ) (hN : ∀ n, 2 ≤ N n) (hK1 : ∀ n, 1 ≤ K n)
    (W : ℕ → ℕ) (a : (n : ℕ) → Fin (W n) → ℝ) (ν : (n : ℕ) → Fin (W n) → Measure Traj)
    (E : (n : ℕ) → Fin (W n) → Set Inc) (B : (n : ℕ) → Fin (W n) → ℝ) (M D ρ : ℕ)
    (σ : ℕ → ℝ) (hσ0 : ∀ n, 0 < σ n) (hσ1 : ∀ n, σ n ≤ 1) (hσinv : ∀ n, (σ n)⁻¹ ≤ N n ^ ρ)
    (hσbig : ∀ n, σ n * N n ^ (2 * M + 4) ≤ 1)
    (hW : ∀ n, 0 < W n ∧ (W n : ℝ) ≤ N n ^ M)
    (ha : ∀ n c, 0 ≤ a n c) (hasum : ∀ n, ∑ c, a n c = 1)
    (hν : ∀ n c, IsProbabilityMeasure (ν n c) ∧ PriorFormat (N n ^ M) D (ν n c))
    (hE : ∀ n c, EventFormat (N n ^ M) D (E n c))
    (hB : ∀ n c, 0 < B n c ∧ B n c ≤ N n ^ M ∧ (B n c)⁻¹ ≤ N n ^ M)
    (hnat : ∀ n c, ∀ᵐ l ∂(ν n c), ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4] : EuclideanSpace ℝ (Fin 2))‖ +
        ‖(WithLp.toLp 2 ![l.2 3, l.2 4] : EuclideanSpace ℝ (Fin 2))‖ ≤ K n ∧
      |B n c * (l.2 2 + t * l.2 5)| ≤ N n ^ M)
    (hmass : ∀ n, ENNReal.ofReal (K n)⁻¹ ≤
      ∑ c, ENNReal.ofReal (a n c) * ((ν n c).prod volume) (E n c)) :
    Submission.Obl.k4_joint_homogenization.Format N K
      (fun n => encPrior (W n) (a n) (fun c => B n c * σ n)
        (fun c => (spacing (N n) M : ℝ) * (c : ℕ) * σ n) (ν n))
      (fun n => encEvent (hW n).1 (fun c => B n c * σ n)
        (fun c => (spacing (N n) M : ℝ) * (c : ℕ) * σ n) (E n)) := by
  refine ⟨6 * M + 4 * ρ + 2, D, fun n => ?_⟩
  have : ∀ c, IsProbabilityMeasure (ν n c) := fun c => (hν n c).1
  have hN1 : (1 : ℝ) ≤ N n := by linarith [hN n]
  have hNpos : (0 : ℝ) < N n := by linarith [hN n]
  set σ' : ℝ := σ n with hσdef
  have hσ0' : 0 < σ' := hσ0 n
  set β : ℝ := N n ^ (2 * M + 2 * ρ) with hβdef
  have hβ1 : 1 ≤ β := one_le_pow₀ hN1
  have hR1 : (1 : ℝ) ≤ N n ^ M := one_le_pow₀ hN1
  -- the parameters satisfy the size hypotheses
  have hbpar : ∀ c, B n c * σ' ≠ 0 ∧ |B n c * σ'| ≤ β ∧ ((B n c * σ') ^ 2)⁻¹ ≤ β := by
    intro c
    obtain ⟨hB0, hBle, hBinv⟩ := hB n c
    refine ⟨by positivity, ?_, ?_⟩
    · rw [abs_of_pos (by positivity)]
      calc B n c * σ' ≤ N n ^ M * 1 := mul_le_mul hBle (hσ1 n) hσ0'.le (by positivity)
        _ ≤ β := by rw [mul_one]; exact pow_le_pow_right₀ hN1 (by omega)
    · have : ((B n c * σ') ^ 2)⁻¹ = ((B n c)⁻¹) ^ 2 * (σ'⁻¹) ^ 2 := by
        field_simp
      rw [this]
      calc ((B n c)⁻¹) ^ 2 * (σ'⁻¹) ^ 2 ≤ (N n ^ M) ^ 2 * (N n ^ ρ) ^ 2 := by
            gcongr
            exact hσinv n
        _ = β := by rw [hβdef, ← pow_mul, ← pow_mul, ← pow_add]; ring_nf
  have hopar : ∀ c : Fin (W n), |(spacing (N n) M : ℝ) * (c : ℕ) * σ'| ≤ β := by
    intro c
    have := abs_enc_hidden_le (B := 0) (w := 0) (hN n) c c.isLt (hW n).2 hσ0'.le (hσbig n)
      (by simpa using (by positivity : (0 : ℝ) ≤ N n ^ M))
    simp only [zero_mul, zero_add] at this
    linarith
  have hsize : 4 * (W n : ℝ) * N n ^ M * β ^ 2 ≤ N n ^ (6 * M + 4 * ρ + 2) := by
    have h4 : (4 : ℝ) ≤ N n ^ 2 := by nlinarith [hN n]
    have hWM := (hW n).2
    calc 4 * (W n : ℝ) * N n ^ M * β ^ 2 ≤ N n ^ 2 * N n ^ M * N n ^ M * β ^ 2 := by
          gcongr
      _ = N n ^ (6 * M + 4 * ρ + 2) := by
          rw [hβdef, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]; ring_nf
  refine ⟨encPrior_isProbability _ _ _ (ha n) (hasum n) _ (fun c => (hν n c).1), ?_, ?_⟩
  · exact (encPrior_format (hW n).1 hR1 hβ1 (a n) _ _ (ν n)
      (fun c => ⟨ha n c, (Finset.single_le_sum (fun c' _ => ha n c') (Finset.mem_univ c)).trans
        (hasum n).le⟩) hbpar hopar (fun c => (hν n c).2)).mono hsize
  have hEv := (encEvent_format (hW n).1 hR1 hβ1 _ _ (E n)
    (fun c => ⟨(hbpar c).1, (hbpar c).2.1⟩) hopar (hE n)).mono hsize
  obtain ⟨hEm, hEsub, hEbdd, hEsl⟩ := hEv
  refine ⟨hEm, hEsub, hEbdd, hEsl, ?_, ?_⟩
  · refine ae_encPrior (hW n).1 _ _ _ (fun c => (hbpar c).1) _ fun c => ?_
    filter_upwards [hnat n c] with l hl t ht
    obtain ⟨hy, hw⟩ := hl t ht
    refine ⟨?_, ?_⟩
    · simpa [encTraj, encCoeff] using hy
    · have := abs_enc_hidden_le (B := B n c) (w := l.2 2 + t * l.2 5) (hN n) c c.isLt
        (hW n).2 hσ0'.le (hσbig n) hw
      have heq : (![t, (encTraj (W n) c (B n c * σ')
          ((spacing (N n) M : ℝ) * (c : ℕ) * σ') l).2 0 + t * (encTraj (W n) c (B n c * σ')
          ((spacing (N n) M : ℝ) * (c : ℕ) * σ') l).2 3, (encTraj (W n) c (B n c * σ')
          ((spacing (N n) M : ℝ) * (c : ℕ) * σ') l).2 1 + t * (encTraj (W n) c (B n c * σ')
          ((spacing (N n) M : ℝ) * (c : ℕ) * σ') l).2 4, (encTraj (W n) c (B n c * σ')
          ((spacing (N n) M : ℝ) * (c : ℕ) * σ') l).2 2 + t * (encTraj (W n) c (B n c * σ')
          ((spacing (N n) M : ℝ) * (c : ℕ) * σ') l).2 5] : Fin 4 → ℝ) 3 =
          B n c * σ' * (l.2 2 + t * l.2 5) + (spacing (N n) M : ℝ) * (c : ℕ) * σ' := by
        simp [encTraj, encCoeff]; ring
      rw [heq]
      exact this.trans (hK1 n)
  · show ENNReal.ofReal (K n)⁻¹ ≤ (((encPrior (W n) (a n) (fun c => B n c * σ')
      (fun c => (spacing (N n) M : ℝ) * (c : ℕ) * σ') (ν n)).prod volume).restrict
      (encEvent (hW n).1 (fun c => B n c * σ') (fun c => (spacing (N n) M : ℝ) * (c : ℕ) * σ')
        (E n))) univ
    rw [encLaw_eq (hW n).1 _ _ _ (ν n) (E n) (fun c => (hE n c).1) (fun c => (hbpar c).1)]
    refine (hmass n).trans (le_of_eq ?_)
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_encInc _ _ _ _)
      MeasurableSet.univ, preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter]

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp
