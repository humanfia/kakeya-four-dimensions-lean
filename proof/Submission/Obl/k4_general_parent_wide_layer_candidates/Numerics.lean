import Submission.Obl.k4_general_parent_wide_layer_candidates.Return

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory MvPolynomial Set Filter
open scoped ENNReal

noncomputable section

/-- The true whole-assignment lower bound makes every candidate floor at
fixed depths at least a fixed inverse power. -/
theorem reference_floor_lower {N K d κ ℓ s v ε D : ℝ}
    (hN : 2 ≤ N) (hK : 0 < K) (hKN : K ≤ N) (hD : 0 < D)
    (hDu : D ≤ K * N ^ (κ * s)) (hε : ε ≤ 1) :
    N ^ (-(d * (s + v) + (3 * κ + ℓ) * s + 5)) ≤
      (N ^ (-d * v - ε) / D) * ((N ^ (-s)) ^ d * D⁻¹ ^ 2 * N ^ (-ℓ * s) / K) := by
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hden : D ^ 3 * K ≤ N ^ (3 * κ * s + 4) := by
    calc
      _ ≤ (K * N ^ (κ * s)) ^ 3 * K := by gcongr
      _ ≤ (N * N ^ (κ * s)) ^ 3 * N := by gcongr
      _ = N ^ (3 * κ * s + 4) := by
        rw [show (N * N ^ (κ * s)) ^ 3 * N = N ^ 4 * (N ^ (κ * s)) ^ 3 by ring]
        rw [← Real.rpow_mul_natCast hNp.le, ← Real.rpow_natCast]
        rw [← Real.rpow_add hNp]
        congr 1
        ring
  have hnum : N ^ (-(d * (s + v) + (3 * κ + ℓ) * s + 5)) *
      (D ^ 3 * K) ≤ N ^ (-d * v - ε) * (N ^ (-s)) ^ d * N ^ (-ℓ * s) := by
    calc
      _ ≤ N ^ (-(d * (s + v) + (3 * κ + ℓ) * s + 5)) * N ^ (3 * κ * s + 4) := by gcongr
      _ ≤ N ^ (-d * v - ε) * (N ^ (-s)) ^ d * N ^ (-ℓ * s) := by
        rw [← Real.rpow_mul hNp.le]
        simp only [← Real.rpow_add hNp]
        apply Real.rpow_le_rpow_of_exponent_le hN1
        nlinarith
  have hident :
      (N ^ (-d * v - ε) / D) * ((N ^ (-s)) ^ d * D⁻¹ ^ 2 * N ^ (-ℓ * s) / K) =
        (N ^ (-d * v - ε) * (N ^ (-s)) ^ d * N ^ (-ℓ * s)) / (D ^ 3 * K) := by
    field_simp
  rw [hident]
  exact (le_div_iff₀ (by positivity)).mpr hnum

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

def calibrationExponent (s v : ℝ) : ℝ := p.d * (s + v) + (3 * p.κ + p.ℓ) * s + 5

theorem calibrationExponent_ge_five (h : p.Valid) {s v : ℝ} (hs : 0 ≤ s) (hv : 0 ≤ v) :
    5 ≤ p.calibrationExponent s v := by
  dsimp [calibrationExponent]
  have h1 := mul_nonneg h.dimension_nonneg (add_nonneg hs hv)
  have h2 := mul_nonneg (show 0 ≤ 3 * p.κ + p.ℓ by linarith [h.rate_pos, h.transverse_pos]) hs
  linarith

theorem AtDepth.reference_floor_absolute {k : ℕ} {s R v ε : ℝ}
    (hat : p.AtDepth k s R) (hN : 2 ≤ p.N k) (hK : 0 < p.K k)
    (hKN : p.K k ≤ p.N k) (hε : ε ≤ 1) (i : Fin (p.n k s)) :
    ENNReal.ofReal (p.N k ^ (-p.calibrationExponent s v)) ≤
      ENNReal.ofReal (p.N k ^ (-p.d * v - ε) / (2 : ℝ) ^ p.T k s) *
        p.ν k (p.A k s i) := by
  have hν := (hat.2.2.2.2.1 i).1
  have hpow : 0 ≤ p.N k ^ (-p.d * v - ε) / (2 : ℝ) ^ p.T k s := by positivity
  have hfloor := reference_floor_lower (d := p.d) (ℓ := p.ℓ) (v := v) hN hK hKN (pow_pos (by norm_num : (0 : ℝ) < 2) _)
    hat.2.1 hε
  calc
    _ ≤ ENNReal.ofReal ((p.N k ^ (-p.d * v - ε) / (2 : ℝ) ^ p.T k s) *
      ((p.N k ^ (-s)) ^ p.d * ((2 : ℝ) ^ p.T k s)⁻¹ ^ 2 *
        p.N k ^ (-p.ℓ * s) / p.K k)) := ENNReal.ofReal_le_ofReal hfloor
    _ = ENNReal.ofReal (p.N k ^ (-p.d * v - ε) / (2 : ℝ) ^ p.T k s) *
      ENNReal.ofReal ((p.N k ^ (-s)) ^ p.d * ((2 : ℝ) ^ (-(p.T k s : ℤ))) ^ 2 *
        p.N k ^ (-p.ℓ * s) / p.K k) := by
      rw [ENNReal.ofReal_mul hpow]
      simp only [zpow_neg, zpow_natCast]
    _ ≤ _ := by gcongr

end Parent
end
end Submission.Obl.k4_general_parent_wide_layer_candidates
