-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/ReturnLosses.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Mathlib

namespace Submission.Obl.k4_finite_affine_candidate_return

/-- The native gain can be used verbatim as the original fractional
gain. This keeps the dimension term in the mass floor exact. -/
theorem return_gain_bounds
    (n : ℕ) (hn : 2 ≤ n) (unit ρ gain R v L child : ℝ)
    (hunit : 0 < unit) (hunitn : unit * n ≤ 1 / 8)
    (hρ : 0 < ρ) (hρmax : ρ ≤ 1 / 4)
    (hgain : gain ≤ ρ * unit / (1000000 * ((n : ℝ) + 1)))
    (hR : 1 < R) (hRn : R ≤ n) (hvlo : R⁻¹ ≤ v) (hvhi : v ≤ R)
    (hL : 0 < L) (hchild : child ≤ L / 2) :
    gain ≤ unit * v ∧ unit * v ≤ 1 / 8 ∧ child + 2 * (unit * v) * L ≤ L := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hvn : (n : ℝ)⁻¹ ≤ v := (inv_anti₀ (by linarith) hRn).trans hvlo
  have hcoef : ρ / (1000000 * ((n : ℝ) + 1)) ≤ (n : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (by positivity) hnpos).mpr
    nlinarith
  have hlow : gain ≤ unit * v := by
    calc
      _ ≤ ρ * unit / (1000000 * ((n : ℝ) + 1)) := hgain
      _ = unit * (ρ / (1000000 * ((n : ℝ) + 1))) := by ring
      _ ≤ unit * (n : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hcoef hunit.le
      _ ≤ unit * v := mul_le_mul_of_nonneg_left hvn hunit.le
  have hupper : unit * v ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left (hvhi.trans hRn) hunit.le).trans hunitn
  exact ⟨hlow, hupper, by nlinarith⟩

/-- The common stage rounding exponent is negligible compared with each
tested gain, and the native candidate loss uses at most a quarter of it. -/
theorem return_relative_losses
    (n : ℕ) (hn : 2 ≤ n) (unit L ρ R v ε' : ℝ)
    (hunit : 0 < unit) (hL : 0 < L) (hρ : 0 < ρ)
    (hR : 1 < R) (hRn : R ≤ n) (hv : R⁻¹ ≤ v) (hε' : ε' ≤ ρ / (4 * R)) :
    ρ * unit * L / (1000000 * ((n : ℝ) + 1)) ≤ (ρ * unit * v * L) / 1000000 ∧
      unit * L * ε' ≤ (ρ * unit * v * L) / 4 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hvn : (n : ℝ)⁻¹ ≤ v := (inv_anti₀ (by linarith) hRn).trans hv
  have hvn' : ((n : ℝ) + 1)⁻¹ ≤ v :=
    (inv_anti₀ hnpos (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)).trans hvn
  constructor
  · have h := mul_le_mul_of_nonneg_left hvn' (by positivity : 0 ≤ ρ * unit * L / 1000000)
    convert h using 1 <;> field_simp
  · have hep : ε' ≤ ρ * v / 4 := by
      calc
        _ ≤ ρ / (4 * R) := hε'
        _ = (ρ / 4) * R⁻¹ := by ring
        _ ≤ (ρ / 4) * v := mul_le_mul_of_nonneg_left hv (by positivity)
        _ = _ := by ring
    have h := mul_le_mul_of_nonneg_left hep (mul_pos hunit hL).le
    convert h using 1 <;> ring

/-- One explicit power allowance simultaneously pays dyadic rounding,
the source domination factor, the fixed model slack and the auxiliary
no-candidate row bound. -/
theorem return_loss_absorption
    (N ε A e g J K H : ℝ) (hN : 1 ≤ N) (hε : 0 < ε) (hA : 0 ≤ A)
    (he : e ≤ A / 1000000) (hg : g ≤ e)
    (hJ₀ : 0 ≤ J) (hK₀ : 0 ≤ K) (hH₀ : 0 ≤ H)
    (hJ : J ≤ N ^ (ε / 1000000)) (hK : K ≤ N ^ e) (hH : H ≤ N ^ (A / 4))
    (hconstant : 8 ≤ N ^ (ε / 1000000)) :
    (2 * N ^ e) * H ≤ N ^ (A + ε) ∧ J * H ≤ N ^ (A + ε) ∧
      8 * J * K * N ^ g * H ≤ N ^ (A + ε) := by
  have hN0 : 0 < N := by linarith
  have htwo : 2 ≤ N ^ (ε / 1000000) := by linarith
  have hgpow : N ^ g ≤ N ^ e := Real.rpow_le_rpow_of_exponent_le hN hg
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ (N ^ (ε / 1000000) * N ^ e) * N ^ (A / 4) := by gcongr
      _ = N ^ (ε / 1000000 + e + A / 4) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  · calc
      _ ≤ N ^ (ε / 1000000) * N ^ (A / 4) := by gcongr
      _ = N ^ (ε / 1000000 + A / 4) := (Real.rpow_add hN0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  · calc
      _ ≤ N ^ (ε / 1000000) * N ^ (ε / 1000000) * N ^ e * N ^ e * N ^ (A / 4) := by
        gcongr
      _ = N ^ (ε / 1000000 + ε / 1000000 + e + e + A / 4) := by
        repeat rw [← Real.rpow_add hN0]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)

end Submission.Obl.k4_finite_affine_candidate_return
