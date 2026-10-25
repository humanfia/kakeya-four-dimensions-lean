-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/GainBuffer.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.ScaleTransfer
import Submission.Obl.k4_quadratic_finite_greedy_cover.Candidates

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open Set

/-- The original candidate mass exponent fits in the rounded gain budget.
The same inequality, with positive signs, controls the per-parent count. -/
theorem rounded_gain_exponent
    (d₁ step h h' L ε ε' : ℝ) (hd₁ : 0 ≤ d₁) (hd₁' : d₁ ≤ 1)
    (hstep : 0 ≤ step) (hL : 0 ≤ L) (hgap : h ≤ h' + step) (hε : ε ≤ 4 * ε') :
    (d₁ * h + step) * L + ε ≤ (d₁ * h' + 4 * step) * L + 4 * ε' := by
  have ha := mul_le_mul_of_nonneg_left hgap hd₁
  have hb := mul_le_mul_of_nonneg_right hd₁' hstep
  have hc : d₁ * h + step ≤ d₁ * h' + 4 * step := by nlinarith
  exact add_le_add (mul_le_mul_of_nonneg_right hc hL) hε

/-- A single numerical buffer pays for both dyadic-scale comparisons in the
whole-block value, derivative and curvature bounds. -/
theorem rounded_candidate_upper
    (Nk L : ℝ) (W C Mc : ℕ) (B : Fin W → ℝ) (ρ gain ε : ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (j : Fin C → ℕ) (A : Fin C → Set Trajectory) (a : CandidateDatum C)
    (h step slack : ℝ) (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hstep : 0 ≤ step)
    (hB : 0 ≤ B (γ a.parent)) (hlo : h ≤ a.gain) (hhi : a.gain ≤ h + step)
    (hbuffer : 2 * Nk ^ (ρ * gain * L + ε) * Nk ^ (step * L) ≤ slack)
    (hg : CandidateGeometry Nk L W C Mc B ρ gain ε r T lev γ j A a) :
    ∀ l ∈ a.trajectories, ∀ t ∈ Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T (lev a.parent))
      (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T (lev a.parent)),
      |MvPolynomial.eval (x l t) a.test| ≤ slack * δ Nk (r (lev a.parent) + h * L) ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) a.test)| ≤
        slack * B (γ a.parent) ∧
      |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) a.test))| ≤
        slack * B (γ a.parent) ^ 2 / δ Nk (r (lev a.parent) + h * L) := by
  have hNpos : 0 < Nk := lt_of_lt_of_le zero_lt_one hN
  let K := Nk ^ (ρ * gain * L + ε)
  let Q := Nk ^ (step * L)
  have hK : 0 ≤ K := Real.rpow_nonneg hNpos.le _
  have hQ : 1 ≤ Q := Real.one_le_rpow hN (mul_nonneg hstep hL)
  have h2K : 2 * K ≤ slack := by nlinarith
  have hKS : K ≤ slack := by linarith
  have hδa : 0 < δ Nk (r (lev a.parent) + a.gain * L) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) (δ_bounds hNpos _).1
  have hδh : 0 < δ Nk (r (lev a.parent) + h * L) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) (δ_bounds hNpos _).1
  have hs := rounded_gain_scales hN (r (lev a.parent)) L a.gain h step hL hlo hhi
  intro l hl t ht
  obtain ⟨hv, hd, hdd⟩ := hg.2.2.2.2.2.2.2 l hl t ht
  refine ⟨?_, hd.trans (mul_le_mul_of_nonneg_right hKS hB), ?_⟩
  · calc
      _ ≤ K * δ Nk (r (lev a.parent) + a.gain * L) := hv
      _ ≤ K * (2 * δ Nk (r (lev a.parent) + h * L)) :=
        mul_le_mul_of_nonneg_left hs.1 hK
      _ ≤ slack * δ Nk (r (lev a.parent) + h * L) := by nlinarith
  · apply (le_div_iff₀ hδh).mpr
    let v := |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4)
      (MvPolynomial.pderiv (3 : Fin 4) a.test))|
    have hvpos : 0 ≤ v := abs_nonneg _
    have hmult := (le_div_iff₀ hδa).mp hdd
    calc
      v * δ Nk (r (lev a.parent) + h * L) ≤
          v * (2 * Q * δ Nk (r (lev a.parent) + a.gain * L)) :=
        mul_le_mul_of_nonneg_left hs.2 hvpos
      _ = (2 * Q) * (v * δ Nk (r (lev a.parent) + a.gain * L)) := by ring
      _ ≤ (2 * Q) * (K * B (γ a.parent) ^ 2) :=
        mul_le_mul_of_nonneg_left hmult (by positivity)
      _ = (2 * K * Q) * B (γ a.parent) ^ 2 := by ring
      _ ≤ slack * B (γ a.parent) ^ 2 :=
        mul_le_mul_of_nonneg_right hbuffer (sq_nonneg _)

/-- The fourfold slack covers the original fourth-power derivative cutoff;
its dyadic comparison factor is absorbed by any spare output power. -/
theorem fourfold_gain_buffers
    (N step L ε ε' : ℝ) (hN : 1 ≤ N) (hstep : 0 ≤ step) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hε' : ε ≤ ε') (habsorb : 2 ≤ N ^ ε') :
    2 * N ^ (step * L + ε) * N ^ (step * L) ≤ N ^ (4 * step * L + 4 * ε') ∧
      (N ^ (step * L + ε)) ^ 4 ≤ N ^ (4 * step * L + 4 * ε') := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hε'pos : 0 ≤ ε' := hε.trans hε'
  constructor
  · calc
      _ ≤ N ^ ε' * N ^ (step * L + ε) * N ^ (step * L) := by gcongr
      _ = N ^ (2 * step * L + ε + ε') := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hN
    norm_num
    nlinarith

end Submission.Obl.k4_quadratic_finite_greedy_cover
