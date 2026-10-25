import Submission.Obl.k4_general_wide_layer_offset_comparison.ComparisonBandCaps

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ShiftedBandCaps.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The original band cap is uniform in ANY real constant offset. Only the
original unshifted coefficients enter the resolution: the added constant
cancels in the query's mesh variation. -/
theorem comparisonBand_add_constant_cap (hbase : p.Basic)
    {k : ℕ} {m h g b r smax Δ B V : ℝ}
    (hN : 1 < p.N k) (hK : 1 ≤ p.K k) (hd : 0 ≤ p.d) (hsmax : 0 ≤ smax)
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hh : 0 < h) (hg : 0 < g) (hb : 0 < b)
    (hmove : h * g ≤ b) (hV : 0 ≤ V)
    (hdtime : p.N k ^ (-r) ≤ h)
    (hdχ : p.N k ^ (-r) ≤ 2 * p.N k ^ (-m)) (hdb : p.N k ^ (-r) ≤ 2 * b)
    (hmχ : V * p.N k ^ (-r) ≤ 2 * p.N k ^ (-m))
    (hmb : V * p.N k ^ (-r) ≤ 2 * b)
    (tag : Fin 2 → ℤ) (D : ℤ × ℤ × ℤ)
    (hv₀ : |(tag 0 : ℝ) * p.N k ^ (-m)| ≤ V) (hv : |domainVelocity g D| ≤ V)
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    (hcoeff : ∀ e, |G.coeff e| ≤ B)
    (offset : ℝ)
    (hresolution : 54 * B * (p.K k + 1) ^ 4 * p.N k ^ (-r) ≤ p.N k ^ (-smax))
    (hΔ : 0 < Δ) (hmin : p.N k ^ (-smax) ≤ Δ)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.μ k)
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ smax → ∀ (c : Fin 3 → ℤ) (j v₁ : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = c ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s))⌋ = j ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₁} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₁}) :
    σ (p.comparisonBand k m h g b tag D (G + C offset) Δ) ≤
      ENNReal.ofReal (16800 * p.K k ^ 2 * p.N k ^ (-m) * h * b * Δ ^ p.d) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = tag 0} := by
  have hc := p.native_band_box_cap hbase hN hK hd hsmax hΔ hmin hdtime hV
    (domainTime h D) ![(tag 1 : ℝ) * p.N k ^ (-m), domainIntercept h g b D]
    ![(tag 0 : ℝ) * p.N k ^ (-m), domainVelocity g D] ![2 * p.N k ^ (-m), 2 * b]
    (by intro i; fin_cases i; exact hv₀; exact hv)
    (by intro i; fin_cases i; exact hdχ; exact hdb)
    (by intro i; fin_cases i; exact hmχ; exact hmb)
    (tag 0) (fun x => eval ![x 0, x 2] G + offset) σ hσ
    (p.comparisonBand k m h g b tag D (G + C offset) Δ)
    (fun ω hω => p.comparisonCode_movingBox (zero_lt_one.trans hN) hh hg hb hmove hω.1 tag D hω.2.1)
    (fun _ hω => congrArg (fun c => c.1 0) hω.2.1)
    (fun _ hω => by simpa [eval_add, eval_C] using hω.2.2)
    (by
      intro ω hω y hy
      simp only [add_sub_add_right_eq_sub]
      exact p.projected_variation_on_good hN.le hK hr hB G hG hcoeff
        hresolution hω.1 y hy) hcap
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  convert hc using 1 <;> congr 2 <;> ring


end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
