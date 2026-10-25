import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripDensity
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripNumerics
import Submission.Obl.k4_finite_positive_mixed_cover_realization.ActualPairCharge

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_forest_width_selection
open scoped RealInnerProductSpace

/-- Summing actual-pair charges uses the original probability mixture and
the original density laws, with no loss in the number of worlds. -/
theorem CoverData.Valid.strip_angular_mass
    {N K : ℕ → ℝ} {L d S η b ζ : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure Trajectory}
    {E : (k : ℕ) → Fin (W k) → Set Incidence}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → Observation × (Fin 2 → ℤ) → ENNReal}
    (hprob : prob N K L d S η W ω ν E P B f g G)
    {k m Mp Dp Mg Dg j : ℕ} {p : PathData (W k)} {c : CoverData p}
    {ℓ κ₁ δ₀ σ d₁ ρ gain ε : ℝ} {s : ℕ → ℝ}
    (hc : c.Valid (N k) L (ω k) (ν k) (B k) d₁ ρ gain m Mg Dg ε)
    (ht : c.time = false)
    (hp : p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ)
    (hrj : 0 ≤ p.r j) (hrjL : p.r j ≤ L)
    (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ) (hn : ∀ d, ‖normal d‖ = 1)
    (hdeep : ∀ d, p.lev d = j → ∀ l ∈ p.assigned d,
      |inner ℝ (((2 : ℝ) ^ p.T c.level)⁻¹ • Matrix.toEuclideanLin
        (p.frame (forestAncestor p.lev p.par d c.level))⁻¹
        (gv l - p.velocity (forestAncestor p.lev p.par d c.level))) (normal d) - bias d| ≤
          2 * p.κ * N k ^ (-ℓ * c.gain * L / 4))
    (hb : 0 < b) (hbη : b ≤ η) (hh : 0 < c.gain)
    (hgeom : StripEstimates (N k) p.κ b c.gain L ℓ ρ ε)
    (hκN : p.κ ≤ N k ^ ζ) (hconst : 1242 ≤ N k ^ ζ)
    (hζ : 0 ≤ ζ) (hρ : ρ ≤ S * b / 128) (hε : ε ≤ ζ)
    (hmargin : 128 * ζ ≤ S * b * c.gain * L) :
    (∑ w, ENNReal.ofReal (ω k w) * ∑ bd : Fin c.n × Fin p.C,
      (((ν k w).prod volume).restrict (E k w))
        (c.misalignedPair normal bias (N k ^ (-b * c.gain * L / 8)) j w bd ∩
          stripGood (N k) L (f L) S b c.gain ζ (B k) (fun w => g k w L)
            (fun w => G k w (b * c.gain * L / 4)) w)) ≤
      ENNReal.ofReal (N k ^ (-(S * b * c.gain * L / 8))) := by
  classical
  have hN : 1 ≤ N k := by linarith [hprob.1 k]
  have hN0 : 0 < N k := zero_lt_one.trans_le hN
  have hL : 0 < L := hprob.2.2.2.1
  have hu : 0 < b * c.gain * L / 4 := by positivity
  have huη : b * c.gain * L / 4 ≤ η * L := by
    have h1 := mul_le_mul_of_nonneg_left hc.2.2.1 (mul_nonneg hb.le hL.le)
    have h2 := mul_le_mul_of_nonneg_right hbη hL.le
    nlinarith
  obtain ⟨M, D, hdata⟩ := hprob.2.2.2.2.2.2.2.2.1
  have hglaw := hprob.2.2.2.2.2.2.2.2.2.1
  have hGlaw := hprob.2.2.2.2.2.2.2.2.2.2.1
  have hcoef := strip_angular_coefficient hN hp.one_le_slack hκN hconst hζ
    (mul_nonneg hh.le hL.le) hρ hε hmargin (fL := f L)
  have hworld (w : Fin (W k)) :
      (∑ bd : Fin c.n × Fin p.C, (((ν k w).prod volume).restrict (E k w))
        (c.misalignedPair normal bias (N k ^ (-b * c.gain * L / 8)) j w bd ∩
          stripGood (N k) L (f L) S b c.gain ζ (B k) (fun w => g k w L)
            (fun w => G k w (b * c.gain * L / 4)) w)) ≤
        ENNReal.ofReal (N k ^ (-(S * b * c.gain * L / 8))) *
          (((ν k w).prod volume).restrict (E k w)) univ := by
    have hd := hdata k
    have hg := hglaw k w L hL.le le_rfl
    have hG := hGlaw k w (b * c.gain * L / 4) hu huη
    have hcharge := hc.misaligned_pair_charge ht hp hN hrj hrjL normal bias hn
      (fun d hd l hl => (hdeep d hd l hl).trans hgeom.deep) hgeom.candidate
      (gδ_pos _ _) (Real.rpow_pos_of_pos hN0 _) hgeom.small hgeom.scale
      w (hd.2.2.2.1 w).1 (hd.2.2.2.1 w).2.2.2.2.2.2.2.2.1
      (g k w L) hg.1 hg.2 (G k w (b * c.gain * L / 4)) hG.1 hG.2
      (a := N k ^ (-f L - S * (b * c.gain * L / 4) + ζ))
      (b := N k ^ (-f L - ζ)) (by positivity) (by positivity)
    apply hcharge.trans
    apply mul_le_mul' _ le_rfl
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hcoef
  calc
    _ ≤ ∑ w, ENNReal.ofReal (ω k w) *
        (ENNReal.ofReal (N k ^ (-(S * b * c.gain * L / 8))) *
          (((ν k w).prod volume).restrict (E k w)) univ) :=
      Finset.sum_le_sum fun w _ => mul_le_mul' le_rfl (hworld w)
    _ = ENNReal.ofReal (N k ^ (-(S * b * c.gain * L / 8))) *
        ∑ w, ENNReal.ofReal (ω k w) * (((ν k w).prod volume).restrict (E k w)) univ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ ≤ _ := by
      simpa only [mul_one] using
        mul_le_mul' (le_rfl : ENNReal.ofReal (N k ^ (-(S * b * c.gain * L / 8))) ≤ _)
          (prob_original_mass_le_one hprob k)

end Submission.Obl.k4_finite_positive_mixed_cover_realization
