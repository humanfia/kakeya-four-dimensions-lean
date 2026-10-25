import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeSourceCaps
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeBasePalette
import Mathlib.Analysis.SpecialFunctions.Log.Base

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/NativeBandCaps.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The primitive native caps control every real band thickness above a
fixed minimum. Bands wider than one are covered by the pure original base
cap, so this also supplies every dyadic scale of discrepancy matching. -/
theorem native_band_box_cap (hbase : p.Basic)
    {k : ℕ} {r m smax Δ radius L : ℝ}
    (hN : 1 < p.N k) (hK : 1 ≤ p.K k) (hd : 0 ≤ p.d)
    (hsmax : 0 ≤ smax) (hΔ : 0 < Δ) (hmin : p.N k ^ (-smax) ≤ Δ)
    (hmesh : p.N k ^ (-r) ≤ radius) (hL : 0 ≤ L)
    (time : ℝ) (center velocity width : Fin 2 → ℝ)
    (hv : ∀ i, |velocity i| ≤ L) (hdw : ∀ i, p.N k ^ (-r) ≤ width i)
    (hmove : ∀ i, L * p.N k ^ (-r) ≤ width i)
    (v₀ : ℤ) (G : (Fin 3 → ℝ) → ℝ)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.μ k) (E : Set (α × ℝ))
    (hbox : ∀ ω ∈ E,
      ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] ∈
        Submission.Lib.K4MovingMeshBoxes.movingBox time radius center velocity width)
    (hvel : ∀ ω ∈ E, ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₀)
    (hfit : ∀ ω ∈ E,
      |eval (p.x k ω.1 ω.2) (p.P k) -
        G ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2]| ≤ Δ)
    (hvariation : ∀ ω ∈ E, ∀ y : Fin 3 → ℝ,
      (∀ i, |(![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] : Fin 3 → ℝ) i - y i| ≤
        p.N k ^ (-r)) →
      |G ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] - G y| ≤ p.N k ^ (-smax))
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ smax → ∀ (q : Fin 3 → ℤ) (a v' : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = q ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s))⌋ = a ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v'} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v'}) :
    σ E ≤ ENNReal.ofReal (4200 * p.K k ^ 2 * Δ ^ p.d *
      radius * width 0 * width 1) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₀} := by
  have hNp : 0 < p.N k := by linarith
  have hK0 : 0 ≤ p.K k := by linarith
  have hrad : 0 ≤ radius := (Real.rpow_pos_of_pos hNp (-r)).le.trans hmesh
  have hw0 : 0 ≤ width 0 := (Real.rpow_pos_of_pos hNp (-r)).le.trans (hdw 0)
  have hw1 : 0 ≤ width 1 := (Real.rpow_pos_of_pos hNp (-r)).le.trans (hdw 1)
  have hKsq : p.K k ≤ p.K k ^ 2 := by nlinarith
  by_cases hsmall : Δ ≤ 1
  · let s : ℝ := -Real.logb (p.N k) Δ
    have hscale : p.N k ^ (-s) = Δ := by
      dsimp only [s]
      rw [neg_neg]
      exact Real.rpow_logb hNp (ne_of_gt hN) hΔ
    have hs0 : 0 ≤ s := neg_nonneg.mpr (Real.logb_nonpos hN hΔ.le hsmall)
    have hss : s ≤ smax := by
      have he := (Real.rpow_le_rpow_left_iff hN).mp (hmin.trans_eq hscale.symm)
      linarith
    have hc := native_source_box_cap p hNp hK0 hmesh hL time center velocity width
      hv hdw hmove v₀ G σ hσ E hbox hvel
      (by intro ω hω; rw [hscale]; exact hfit ω hω)
      (by
        intro ω hω y hy
        rw [hscale]
        exact (hvariation ω hω y hy).trans hmin)
      (fun q a => hcap s hs0 hss q a v₀)
    have hpow : p.N k ^ (-p.d * s) = Δ ^ p.d := by
      rw [← hscale, ← Real.rpow_mul hNp.le]
      congr 1
      ring
    rw [hpow] at hc
    apply hc.trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    gcongr
  · have hlarge : 1 ≤ Δ := (lt_of_not_ge hsmall).le
    have hΔd : 1 ≤ Δ ^ p.d := Real.one_le_rpow hlarge hd
    have hpow3 : p.N k ^ (-3 * r) = (p.N k ^ (-r)) ^ 3 := by
      rw [← Real.rpow_mul_natCast hNp.le]
      congr 1
      ring
    have hc := native_source_box_base_cap p hbase hNp hK hmesh hL time center velocity width
      hv hdw hmove v₀ σ hσ E hbox hvel (by
        intro q a v'
        have hh := hcap 0 le_rfl hsmax q a v'
        simpa only [neg_zero, Real.rpow_zero, div_one, mul_zero, sub_zero, hpow3] using hh)
    apply hc.trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hweight : 3600 * p.K k ^ 2 ≤ 4200 * p.K k ^ 2 * Δ ^ p.d := by
      calc
        _ ≤ 4200 * p.K k ^ 2 := by nlinarith [sq_nonneg (p.K k)]
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hΔd
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hweight hrad) hw0) hw1

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
