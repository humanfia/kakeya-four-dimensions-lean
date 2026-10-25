-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.CountedGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.StrongAssemblyBody
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Gain
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.DyadicDepth
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file CountedGain.lean), namespace renamed.

/-!
# The frozen gain for prism covers with a global quadratic count

`countedGain_of_estimateE` proves the conclusion of the frozen obligation, from `E` alone (via
the accepted o065), for every family whose prism cover satisfies, besides the frozen
structure (C), the global quadratic count
`#{P_j ⊆ U} (ab)² ≤ δ^(-ζ₃) |U|²` for every convex `U`.
This count holds, for instance, when the prisms are not overfilled (`p·ab ≲ δ^(-ζ₃)`), by
Frostman above. It is NOT implied by the frozen (C) in general (axially staggered or thinly
staggered covers violate it).
-/

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory

/-- The frozen gain, for covers that also satisfy the global quadratic count. -/
abbrev CountedGain (σ ω ζ₂ : ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
    ∀ ζ₃ : ℝ, 0 < ζ₃ → ζ₃ ≤ ζ₀ → ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      FamilyHypotheses η δ n x v Y
        ((∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
          ∀ a b : ℝ, δ ≤ a → a ≤ δ ^ (ζ₂ / 200) * b → b ≤ 1 →
          ∀ (p : ℕ) (c e₁ e₂ e₃ : Fin p → Space),
          (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) →
          Factored (δ ^ (-ζ₃)) b (fun i => tube δ (x i) (v i))
            (fun j => prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) →
          (∀ U : Set Space, Convex ℝ U →
            ENNReal.ofReal (Set.ncard {j | prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ⊆ U}) *
              ENNReal.ofReal ((a * b) ^ 2) ≤ ENNReal.ofReal (δ ^ (-ζ₃)) * (volume U) ^ 2) →
          ENNReal.ofReal (A * δ ^ (ω - α + ε) * (n * δ ^ 4) ^ (σ / 2)) ≤
            volume (⋃ i, Y i))

theorem countedGain_of_estimateE {σ ω ζ₂ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 < ω)
    (hζ₂ : 0 < ζ₂) (hE : EstimateE σ ω) : CountedGain σ ω ζ₂ := by
  let α : ℝ := ζ₂ * ω / 400
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨A, hA, η, hη, ζ₀, hζ₀, d, hd, H⟩ := strong_prism_aspect_body hσ.le hσ1 hω hE α hα
  obtain ⟨dshape, hdshape, hshape⟩ := power_absorption 100 (by positivity : 0 < ζ₂ / 200)
  refine ⟨α, hα, ζ₀, hζ₀, ?_⟩
  intro ζ₃ hζ₃ hζ₃₀ ε hε
  refine ⟨A, hA, η, hη, min (min d 1) dshape,
    lt_min (lt_min hd zero_lt_one) hdshape, ?_⟩
  intro δ hδ hδd n x v Y hn hv hB hover hYm hYT hden hind a b hδa hflat hb1 p c e₁ e₂ e₃ he
    hfact hquad
  have hδd' : δ ≤ d := (hδd.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := (hδd.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hsmall := hshape δ hδ (hδd.trans (min_le_right _ _))
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := aspect_ratio_pos hδ hδa hflat
  have hab : a ≤ b := hflat.trans (by
    simpa using mul_le_mul_of_nonneg_right
      (Real.rpow_le_one hδ.le hδ1 (by positivity : 0 ≤ ζ₂ / 200)) hb.le)
  have ha100 : a ≤ 1 / 100 := by
    have hh := mul_le_mul_of_nonneg_left hb1 (Real.rpow_nonneg hδ.le (ζ₂ / 200))
    linarith
  have hbound := H ζ₃ δ hζ₃.le hζ₃₀ hδ hδd' a b hδa hab hb1 ha100 n x v Y
    hn hv hB hover hYm hYT hind p c e₁ e₂ e₃ he hfact hquad
  apply (ENNReal.ofReal_le_ofReal ?_).trans hbound
  have hgain := aspect_ratio_gain hδ ha hflat hω.le
  have hpow : δ ^ (ω - α + ε) ≤ δ ^ (ω + α) * (b / a) ^ ω := by
    calc
      _ ≤ δ ^ (ω - α) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ (ω + α) * δ ^ (-(ζ₂ / 200 * ω)) := by
        rw [← Real.rpow_add hδ]
        congr 1
        dsimp [α]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgain (Real.rpow_nonneg hδ.le _)
  calc
    _ ≤ A * (δ ^ (ω + α) * (b / a) ^ ω) * (n * δ ^ 4) ^ (σ / 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      exact mul_le_mul_of_nonneg_left hpow hA.le
    _ = _ := by ring

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
