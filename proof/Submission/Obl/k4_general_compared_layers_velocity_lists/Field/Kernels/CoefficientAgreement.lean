-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Kernels.CoefficientAgreement; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Adapted from this LOT tree: obligation o247 (k4_wide_common_field_velocity_lists), branch x0870, commit e81b750b34aa9824cd7568c0d87d020832257f81, file Submission/Obl/k4_wide_common_field_velocity_lists/CoefficientAgreement.lean (session x0870's work). -/
/- That file was itself adapted from this LOT tree: obligation o218, session x0764, commit 8864b003,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/CoefficientAgreement.lean. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Kernels.MatchingLength

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Coefficient agreement: the length test integrated against sources and palette

The core estimate of "Coefficient agreement at a fine state" in the proof of the wide-interval
proposition (paper `prop:wide-interval`).  Source entries `s` carry a law `μ s` of their transverse
coordinate `U ∈ [-L, L]` with density at most `W s` and a frozen quadratic `P s` (its offset
included); a target class `τ` (a target velocity bin, chart and coarse predictor) carries a quadratic
`Q τ`, at most `m` offsets `O τ`, and the palette weight `π τ` of its velocity bin.  The pair law
of a source event and a target class is dominated by `C π(τ) μ_s` (conditional palette
domination), and on it the two predictions agree up to an offset: `|P_s(U) - Q_τ(U) - c| ≤ w`
for some `c ∈ O_τ`.  Then the pairs whose nonconstant coefficient gap is `≥ e` carry total mass at
most `Σ_s C W_s Π_s (θ(4L+2)/e + 4 m w/θ)`, where `Π_s = Σ_τ π τ` (the paper's `K`).  With
`θ = e N^-τ`, `m = K N^{du}`, `w = K a₁` this is power-small times the summable reference
weights, which is the claimed agreement.  Rate-free.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels

open MeasureTheory Set Finset

/-- The nonconstant coefficient gap of two quadratics `(c₀, c₁, c₂)`. -/
def coeffGap (P Q : Fin 3 → ℝ) : ℝ := |P 1 - Q 1| + |P 2 - Q 2|

/-- The set of transverse coordinates where `P` and `Q` agree up to one of the offsets. -/
def matchSet (P Q : Fin 3 → ℝ) (O : Finset ℝ) (w L : ℝ) : Set ℝ :=
  {U ∈ Icc (-L) L | ∃ c ∈ O, |(P 0 + P 1 * U + P 2 * U ^ 2) - (Q 0 + Q 1 * U + Q 2 * U ^ 2) - c| ≤ w}

/-- The matching set of two quadratics with a nonconstant gap is short. -/
theorem volume_matchSet_le {P Q : Fin 3 → ℝ} {O : Finset ℝ} {w L e θ : ℝ} (hL : 0 ≤ L)
    (he : 0 < e) (hgap : e ≤ coeffGap P Q) (hθ : 0 < θ) (hθe : θ ≤ e / 2) (hw : 0 ≤ w) :
    volume (matchSet P Q O w L) ≤
      ENNReal.ofReal (θ * (4 * L + 2) / e + 4 * O.card * w / θ) := by
  have h := quadratic_offset_match_volume (δ₀ := P 0 - Q 0) (δ₁ := P 1 - Q 1)
    (δ₂ := P 2 - Q 2) O hL he hgap hθ hθe hw
  refine le_trans (measure_mono ?_) h
  intro U ⟨hU, c, hc, hv⟩
  refine ⟨hU, c, hc, ?_⟩
  have : (P 0 - Q 0) + (P 1 - Q 1) * U + (P 2 - Q 2) * U ^ 2 - c =
      (P 0 + P 1 * U + P 2 * U ^ 2) - (Q 0 + Q 1 * U + Q 2 * U ^ 2) - c := by ring
  rwa [this]

/-- **Coefficient agreement, integrated form.**  `Λ s τ` is the pair law of source entry `s`'s
transverse coordinate with target class `τ`. -/
theorem coefficient_disagreement_mass {Src Tgt : Type*} (Ssrc : Finset Src)
    (T : Src → Finset Tgt) (μ : Src → Measure ℝ) (Λ : Src → Tgt → Measure ℝ)
    (P : Src → Fin 3 → ℝ) (Q : Tgt → Fin 3 → ℝ) (O : Tgt → Finset ℝ) (π : Tgt → ℝ)
    (W : Src → ℝ) {C L e θ w : ℝ} {m : ℕ} (hC : 0 ≤ C) (hL : 0 ≤ L) (he : 0 < e) (hθ : 0 < θ)
    (hθe : θ ≤ e / 2) (hw : 0 ≤ w) (hπ : ∀ τ, 0 ≤ π τ) (hW : ∀ s, 0 ≤ W s)
    (hO : ∀ τ, (O τ).card ≤ m)
    (hdens : ∀ s ∈ Ssrc, ∀ E : Set ℝ, μ s E ≤ ENNReal.ofReal (W s) * volume E)
    (hdom : ∀ s ∈ Ssrc, ∀ τ ∈ T s, ∀ E : Set ℝ, Λ s τ E ≤ ENNReal.ofReal (C * π τ) * μ s E)
    (hagree : ∀ s ∈ Ssrc, ∀ τ ∈ T s, Λ s τ (matchSet (P s) (Q τ) (O τ) w L)ᶜ = 0) :
    ∑ s ∈ Ssrc, ∑ τ ∈ (T s).filter (fun τ => e ≤ coeffGap (P s) (Q τ)), Λ s τ univ ≤
      ENNReal.ofReal ((θ * (4 * L + 2) / e + 4 * m * w / θ) * C *
        ∑ s ∈ Ssrc, W s * ∑ τ ∈ T s, π τ) := by
  set ℓ := θ * (4 * L + 2) / e + 4 * m * w / θ with hℓ
  have hℓ0 : 0 ≤ ℓ := by positivity
  have hone : ∀ s ∈ Ssrc, ∀ τ ∈ (T s).filter (fun τ => e ≤ coeffGap (P s) (Q τ)),
      Λ s τ univ ≤ ENNReal.ofReal (ℓ * C * W s * π τ) := by
    intro s hs τ hτ
    obtain ⟨hτT, hgap⟩ := Finset.mem_filter.mp hτ
    have hsplit : Λ s τ univ ≤ Λ s τ (matchSet (P s) (Q τ) (O τ) w L) := by
      calc Λ s τ univ ≤ Λ s τ (matchSet (P s) (Q τ) (O τ) w L) +
            Λ s τ (matchSet (P s) (Q τ) (O τ) w L)ᶜ := by
            rw [← union_compl_self (matchSet (P s) (Q τ) (O τ) w L)]
            exact measure_union_le _ _
        _ = Λ s τ (matchSet (P s) (Q τ) (O τ) w L) := by rw [hagree s hs τ hτT, add_zero]
    have hlen := volume_matchSet_le (O := O τ) (P := P s) (Q := Q τ) hL he hgap hθ hθe hw
    have hlen' : volume (matchSet (P s) (Q τ) (O τ) w L) ≤ ENNReal.ofReal ℓ := by
      refine hlen.trans (ENNReal.ofReal_le_ofReal ?_)
      have : ((O τ).card : ℝ) ≤ m := by exact_mod_cast hO τ
      simp only [hℓ]
      gcongr
    calc Λ s τ univ ≤ Λ s τ (matchSet (P s) (Q τ) (O τ) w L) := hsplit
      _ ≤ ENNReal.ofReal (C * π τ) * μ s (matchSet (P s) (Q τ) (O τ) w L) :=
          hdom s hs τ hτT _
      _ ≤ ENNReal.ofReal (C * π τ) * (ENNReal.ofReal (W s) * ENNReal.ofReal ℓ) := by
          gcongr
          exact (hdens s hs _).trans (mul_le_mul' le_rfl hlen')
      _ = ENNReal.ofReal (ℓ * C * W s * π τ) := by
          rw [← ENNReal.ofReal_mul (hW s), ← ENNReal.ofReal_mul (mul_nonneg hC (hπ τ))]
          congr 1; ring
  calc ∑ s ∈ Ssrc, ∑ τ ∈ (T s).filter (fun τ => e ≤ coeffGap (P s) (Q τ)), Λ s τ univ
      ≤ ∑ s ∈ Ssrc, ∑ τ ∈ (T s).filter (fun τ => e ≤ coeffGap (P s) (Q τ)),
          ENNReal.ofReal (ℓ * C * W s * π τ) :=
        Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun τ hτ => hone s hs τ hτ
    _ ≤ ∑ s ∈ Ssrc, ∑ τ ∈ T s, ENNReal.ofReal (ℓ * C * W s * π τ) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum_of_subset
          (Finset.filter_subset (fun τ => e ≤ coeffGap (P s) (Q τ)) (T s))
    _ = ENNReal.ofReal (∑ s ∈ Ssrc, ∑ τ ∈ T s, ℓ * C * W s * π τ) := by
        have hnn : ∀ s, ∀ τ, 0 ≤ ℓ * C * W s * π τ := fun s τ =>
          mul_nonneg (mul_nonneg (mul_nonneg hℓ0 hC) (hW s)) (hπ τ)
        rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => Finset.sum_nonneg fun τ _ => hnn s τ)]
        apply Finset.sum_congr rfl; intro s _
        rw [ENNReal.ofReal_sum_of_nonneg (fun τ _ => hnn s τ)]
    _ = ENNReal.ofReal (ℓ * C * ∑ s ∈ Ssrc, W s * ∑ τ ∈ T s, π τ) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro τ _; ring

end Submission.Obl.k4_general_compared_layers_velocity_lists.Kernels
