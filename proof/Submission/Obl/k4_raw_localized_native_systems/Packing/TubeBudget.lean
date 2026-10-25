/- Adapted from this LOT tree, o197, session x0690, Packing/TubeBudget.lean,
   commit e679a859 (the preceding turn of this session). -/
import Submission.Obl.k4_raw_localized_native_systems.Packing.WitnessWindow

namespace Submission.Obl.k4_raw_localized_native_systems.Packing

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Uniform radii for the common physical tube. The factor `E` contains the
small major-axis cutoff and angular losses; the earlier minor width is not
discarded in the normal radius. -/
theorem scalar_window_radii_budget {K q g E κ σ major minor θ U V r₀ : ℝ}
    (hK : 1 ≤ K) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hg : 0 ≤ g) (hE : 1 ≤ E)
    (_hκ : 0 ≤ κ) (hκK : κ ≤ K) (hσ : σ ≤ q)
    (hmajor0 : 0 ≤ major) (hmajor : major ≤ K * q)
    (hminor0 : 0 ≤ minor) (hminor : minor ≤ q * g * E)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 32 * K * g * E ^ 2)
    (hU : U ≤ 3 * K ^ 2) (hV : V ≤ 64 * K ^ 2 * g * E ^ 2)
    (hr₀ : r₀ ≤ K * q * g * E ^ 2) :
    q + σ ≤ 2 * q ∧
      σ + 4 * κ * major + q * U ≤ 8 * K ^ 2 * q ∧
      r₀ + 2 * κ * (minor + 2 * major * θ) + q * V ≤
        256 * K ^ 3 * q * g * E ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hE2 : E ≤ E ^ 2 := by nlinarith
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have hK12 : K ≤ K ^ 2 := by nlinarith
  have hK23 : K ^ 2 ≤ K ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK)]
  have hK13 : K ≤ K ^ 3 := hK12.trans hK23
  let B := g * E ^ 2
  let R := q * g * E ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hminR : minor ≤ R := hminor.trans
    (mul_le_mul_of_nonneg_left hE2 (mul_nonneg hq hg))
  have hθB : θ ≤ 32 * K * B := by simpa only [B, mul_assoc] using hθ
  have hVB : V ≤ 64 * K ^ 2 * B := by simpa only [B, mul_assoc] using hV
  have hrR : r₀ ≤ K * R := by simpa only [R, mul_assoc] using hr₀
  have hprod : major * θ ≤ K * (32 * K * R) := by
    calc
      major * θ ≤ (K * q) * (32 * K * B) :=
        mul_le_mul hmajor hθB hθ0 (by positivity)
      _ = _ := by dsimp [B, R]; ring
  have hinner : minor + 2 * major * θ ≤ R + 2 * K * (32 * K * R) := by
    nlinarith
  have hterm : 2 * κ * (minor + 2 * major * θ) ≤
      2 * K * (R + 2 * K * (32 * K * R)) := by
    apply mul_le_mul (by linarith) hinner
    · positivity
    · positivity
  have hqV : q * V ≤ 64 * K ^ 2 * R := by
    calc
      q * V ≤ q * (64 * K ^ 2 * B) := mul_le_mul_of_nonneg_left hVB hq
      _ = _ := by dsimp [B, R]; ring
  have hmajorTerm : 4 * κ * major ≤ 4 * K ^ 2 * q := by
    calc
      4 * κ * major ≤ 4 * K * major :=
        mul_le_mul_of_nonneg_right (by linarith) hmajor0
      _ ≤ 4 * K * (K * q) := mul_le_mul_of_nonneg_left hmajor (by positivity)
      _ = _ := by ring
  have hqU : q * U ≤ 3 * K ^ 2 * q := by
    nlinarith [mul_le_mul_of_nonneg_left hU hq]
  refine ⟨by linarith, ?_, ?_⟩
  · nlinarith [mul_nonneg hq (sub_nonneg.mpr hK2)]
  · calc
      _ ≤ 256 * K ^ 3 * R := by
        nlinarith [mul_le_mul_of_nonneg_right hK13 hR,
          mul_le_mul_of_nonneg_right hK23 hR, mul_nonneg (pow_nonneg hK0 3) hR]
      _ = _ := by dsimp [R]; ring

theorem scalar_window_tube_volume_polynomial (K q g E : ℝ) :
    8 * Real.pi * (2 * q) * (8 * K ^ 2 * q) *
        (256 * K ^ 3 * q * g * E ^ 2) =
      32768 * Real.pi * K ^ 5 * q ^ 3 * g * E ^ 2 := by ring

/-- The original short-list bound, common native base ceiling, and uniform
frame scales give a full witness-mass bound with the common `q³ g` factor.
No event is intersected with the scalar window in this sum. -/
theorem witness_window_mass_le_polynomial {p : Data} {k M D : ℕ}
    (W : Atlas p k) {κ r K q g E d₀ : ℝ}
    (hc : ∀ e, Window.WChart p k W M D κ r e) (hκ : 0 ≤ κ) (hκK : κ ≤ K)
    (hK : 1 ≤ K) (hqtime : q = 1 / (2 : ℝ) ^ W.T) (hg : 0 < g) (hE : 1 ≤ E)
    (hd₀ : 0 ≤ d₀) (γ : Fin (p.W k)) (I : Finset (Fin W.C))
    (hworld : ∀ e ∈ I, W.γ e = γ)
    (hknown : ∀ e z, z ∈ W.F e →
      e ∈ W.lst (W.γ e) (obs (p.B k (W.γ e)) (δ (p.N k) p.L) z))
    (hcard : ∀ o, ((W.lst γ o).card : ℝ) ≤ K)
    (μ : Measure Point)
    (hcap : Measure.map Window.basePt μ ≤ ENNReal.ofReal (64 * K ^ 2 * d₀) • volume)
    {n : Plane} (hn : ‖n‖ = 1) {t y₀ α β σ r₀ : ℝ} (hσ : σ ≤ q)
    (hmajor : ∀ e ∈ I, ‖Pairing.longCol (W.Q e)‖ ≤ K * q)
    (hminor : ∀ e ∈ I, Pairing.minorWidth (W.Q e) ≤ q * g * E)
    (hangle : ∀ e ∈ I, min ‖n - Pairing.minorNormal (W.Q e)‖
      ‖n + Pairing.minorNormal (W.Q e)‖ ≤ 32 * K * g * E ^ 2)
    (hU : ∀ e ∈ I, ‖W.u e‖ ≤ 3 * K ^ 2)
    (hV : ∀ e ∈ I, |inner ℝ (W.u e - β • n) n| ≤ 64 * K ^ 2 * g * E ^ 2)
    (hr₀ : r₀ ≤ K * q * g * E ^ 2)
    (hanchor : ∀ e ∈ I, ∃ z ∈ W.F e, |z.2 - t| ≤ σ ∧
      |tangentValue (tangentOfNormal n) z.1 z.2 - y₀| ≤ σ ∧
      |inner ℝ (y z.1 z.2 - α • n - z.2 • (β • n)) n| ≤ r₀) :
    (∑ e ∈ I, μ (W.F e)) ≤
      ENNReal.ofReal (2097152 * Real.pi * K ^ 8 * d₀ * q ^ 3 * g * E ^ 2) := by
  have hq : 0 < q := by rw [hqtime]; positivity
  have hq1 : q ≤ 1 := by
    rw [hqtime, div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hK0 : 0 ≤ K := by linarith
  have hE0 : 0 < E := by linarith
  have hbudget (e : Fin W.C) (he : e ∈ I) :=
    scalar_window_radii_budget hK hq.le hq1 hg.le hE hκ hκK hσ
      (norm_nonneg _) (hmajor e he) (Pairing.minorWidth_nonneg _) (hminor e he)
      (by positivity : 0 ≤ 32 * K * g * E ^ 2) le_rfl le_rfl le_rfl hr₀
  have ht : 1 / (2 : ℝ) ^ W.T + σ ≤ 2 * q := by rw [← hqtime]; linarith
  have hy : ∀ e ∈ I,
      σ + 4 * κ * ‖Pairing.longCol (W.Q e)‖ +
        1 / (2 : ℝ) ^ W.T * (3 * K ^ 2) ≤ 8 * K ^ 2 * q := by
    intro e he
    simpa only [← hqtime] using (hbudget e he).2.1
  have hn' : ∀ e ∈ I,
      r₀ + 2 * κ * (Pairing.minorWidth (W.Q e) +
        2 * ‖Pairing.longCol (W.Q e)‖ * (32 * K * g * E ^ 2)) +
        1 / (2 : ℝ) ^ W.T * (64 * K ^ 2 * g * E ^ 2) ≤
          256 * K ^ 3 * q * g * E ^ 2 := by
    intro e he
    simpa only [← hqtime] using (hbudget e he).2.2
  have h := witness_window_mass_le W hc γ I hworld hknown K hcard μ
    (ENNReal.ofReal (64 * K ^ 2 * d₀)) hcap hn hangle hU hV hanchor ht hy hn'
    (by positivity) (by positivity)
  refine h.trans_eq ?_
  rw [scalar_window_tube_volume_polynomial,
    ← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end
end Submission.Obl.k4_raw_localized_native_systems.Packing
