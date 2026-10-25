import Submission.Obl.k4_finite_positive_mixed_cover_realization.Cover
import Submission.Obl.k4_fixed_menu_density_pruning.SampleClean

/-!
# A time cover is o209's greedy cover at its actual gain

A valid `CoverData` with `time = true`, at the requested gain `gain` and menu ratio `ρ`, is
o209's unpacked greedy cover `gcBody` at the requested gain `gain' := h` (its actual gain,
menu index `0`) and any ratio `ρ₀ ≥ ρ`: o209's allowances `4 ρ₀ gain' L` dominate the cover's
`4 ρ h L`, and its floors and counts are weaker.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set
open Submission.Obl.k4_fixed_menu_density_pruning (gcBody)

theorem gcBody_of_timeCover {W : ℕ} {p : PathData W} (c : CoverData p)
    {Nk L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory} {B : Fin W → ℝ}
    {d₁ ρ ρ₀ gain : ℝ} {m Mg Dg : ℕ} {ε : ℝ}
    (hN : 1 ≤ Nk) (hL : 0 < L) (hgainpos : 0 < gain) (hB : ∀ w, 0 < B w) (hρ : 0 ≤ ρ) (hρρ₀ : ρ ≤ ρ₀)
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε) (htime : c.time = true) :
    gcBody Nk L W ω ν B d₁ ρ₀ c.gain m p.r p.T p.C p.lev p.world p.bin p.assigned
      p.counted Mg Dg ε c.level c.gain c.n c.old c.test c.assigned c.counted := by
  obtain ⟨hlevel, hgg, hg8, hmenu, hroom, hn, hcand, hdisjA, hcount, hdisjV, hmass⟩ := hc
  have hgain0 : 0 ≤ c.gain := le_trans hgainpos.le hgg
  have hN0 : 0 < Nk := by linarith
  -- the allowance and exponent comparisons
  have hH : Nk ^ (4 * ρ * c.gain * L + 4 * ε) ≤ Nk ^ (4 * ρ₀ * c.gain * L + 4 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hN
    have : ρ * (c.gain * L) ≤ ρ₀ * (c.gain * L) :=
      mul_le_mul_of_nonneg_right hρρ₀ (mul_nonneg hgain0 hL.le)
    linarith
  have hHpos : 0 < Nk ^ (4 * ρ * c.gain * L + 4 * ε) := Real.rpow_pos_of_pos hN0 _
  refine ⟨hlevel, le_rfl, hg8, ⟨0, by simp⟩, hroom, hn, ?_, hdisjA, ?_, hdisjV, hmass⟩
  · intro a
    obtain ⟨hlev, hν, hAm, hAsub, hfmt, hVm, hVsub, htest⟩ := hcand a
    simp only [htime, ↓reduceIte] at htest
    obtain ⟨hdeg, hcoef, hfits, hlower, hfloor⟩ := htest
    refine ⟨hlev, hν, hdeg, hcoef, hAm, hAsub, hfmt, ?_, hVm, ?_, ?_⟩
    · intro l hl t ht
      obtain ⟨h1, h2, h3⟩ := hfits l hl t ht
      have hδ : 0 < δ Nk (p.r c.level + c.gain * L) := zpow_pos (by norm_num) _
      refine ⟨h1.trans (mul_le_mul_of_nonneg_right hH hδ.le),
        h2.trans (mul_le_mul_of_nonneg_right hH (hB _).le), ?_⟩
      refine h3.trans ?_
      apply div_le_div_of_nonneg_right _ hδ.le
      exact mul_le_mul_of_nonneg_right hH (sq_nonneg _)
    · intro z hz
      obtain ⟨hzT, hz1, hz2⟩ := hVsub hz
      refine ⟨hzT, hz1, hz2, ?_⟩
      refine le_trans ?_ (hlower z hz)
      exact div_le_div_of_nonneg_left (hB _).le hHpos hH
    · refine le_trans ?_ hfloor
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN ?_)
          (by positivity))) le_rfl
      have : ρ * (c.gain * L) ≤ ρ₀ * (c.gain * L) :=
        mul_le_mul_of_nonneg_right hρρ₀ (mul_nonneg hgain0 hL.le)
      nlinarith
  · intro b
    refine (hcount b).trans ?_
    simp only [htime, ↓reduceIte]
    apply Real.rpow_le_rpow_of_exponent_le hN
    have : ρ * (c.gain * L) ≤ ρ₀ * (c.gain * L) :=
      mul_le_mul_of_nonneg_right hρρ₀ (mul_nonneg hgain0 hL.le)
    nlinarith

end Submission.Obl.k4_finite_positive_mixed_cover_realization
