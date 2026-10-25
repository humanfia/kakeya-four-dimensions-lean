-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.LocalizedCarrier.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/LocalizedCarrier.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0708 commit 170d089, LocalizedCarrier.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConvexEnclosure
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CappedPrismWidth

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory

/-- Localizing a dense convex carrier to the original block keeps its density
and gives an enclosure at the old length scale, regardless of the diameter of
the carrier before localization. -/
theorem localized_dense_convex_enclosure {a b c R D : ℝ} {W H : Set V}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hR : 0 < R) (hD : 0 ≤ D)
    (z z₀ : V) (e : V ≃ₗᵢ[ℝ] V) (hW : Convex ℝ W)
    (hwhole : P a b c z e ⊆ W ∩ ball z₀ (R*c))
    (hH : H ⊆ W ∩ ball z₀ (R*c)) (hden : O D * μ W ≤ μ H) :
    ∃ (A B : ℝ) (z' : V) (e' : V ≃ₗᵢ[ℝ] V),
      a ≤ A ∧ A ≤ B ∧ B ≤ 4*R*c ∧
      W ∩ ball z₀ (R*c) ⊆ P A B (4*R*c) z' e' ∧
      H ⊆ P A B (4*R*c) z' e' ∧
      μ (P A B (4*R*c) z' e') ≤ O (3456*R) * μ W ∧
      O (D/(3456*R)) * μ (P A B (4*R*c) z' e') ≤ μ H := by
  obtain ⟨A, B, z', e', haA, hAB, hBc, hbox, hvol⟩ :=
    convex_grain_enclosure ha hab hbc hR e (hW.inter (convex_ball _ _))
      inter_subset_right hwhole
  have hvol' : μ (P A B (4*R*c) z' e') ≤ O (3456*R) * μ W :=
    hvol.trans (mul_le_mul' le_rfl (measure_mono inter_subset_left))
  refine ⟨A, B, z', e', haA, hAB, hBc, hbox, hH.trans hbox, hvol', ?_⟩
  calc
    O (D/(3456*R)) * μ (P A B (4*R*c) z' e')
        ≤ O (D/(3456*R)) * (O (3456*R) * μ W) := mul_le_mul' le_rfl hvol'
    _ = O D * μ W := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ D/(3456*R)),
        div_mul_cancel₀ _ (by positivity : 3456*R ≠ 0)]
    _ ≤ μ H := hden

/-- A dense first carrier, cut back to its original block, lies in a physically
thin prism under the ambient ball-density cap. All fixed enclosure losses are
absorbed before the second angular selection. -/
theorem capped_localized_carrier_short {s t h₀ h₁ jump R : ℝ}
    (hs : 0 < s) (hh : h₀ < h₁) (hbudget : t+h₁ < jump*s) (hR : 0 < R) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ (a b c : ℝ) (z z₀ : V) (e : V ≃ₗᵢ[ℝ] V) (W H Γ : Set V),
      0 < a → a ≤ b → b ≤ c → 4*R*c ≤ 1 → Convex ℝ W →
      P a b c z e ⊆ W ∩ ball z₀ (R*c) →
      H ⊆ W ∩ ball z₀ (R*c) → H ⊆ Γ →
      O (δ^h₀) * μ W ≤ μ H →
      (∀ p ∈ Γ, ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ (Γ ∩ ball p r) ≤ O (δ^(-t) * (δ/r)^s * r^3)) →
      ∃ (A B : ℝ) (z' : V) (e' : V ≃ₗᵢ[ℝ] V),
        a ≤ A ∧ A ≤ B ∧ B ≤ 4*R*c ∧ A < δ^(1-jump) ∧
        W ∩ ball z₀ (R*c) ⊆ P A B (4*R*c) z' e' ∧
        H ⊆ P A B (4*R*c) z' e' ∧
        O (δ^h₁) * μ (P A B (4*R*c) z' e') ≤ μ H := by
  obtain ⟨dC, hdC, hdC1, HC⟩ := capped_dense_prism_short hs hbudget
  obtain ⟨dD, hdD, HD⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (sub_pos.mpr hh) (by positivity : 0 < 1/(3456*R))
  refine ⟨min dC dD, lt_min hdC hdD, (min_le_left _ _).trans hdC1, ?_⟩
  intro δ hδ hδd a b c z z₀ e W H Γ ha hab hbc hc1 hW hwhole hH hHΓ hden hcap
  obtain ⟨A, B, z', e', haA, hAB, hBc, hbox, hHP, _, hD⟩ :=
    localized_dense_convex_enclosure ha hab hbc hR (Real.rpow_nonneg hδ.le h₀)
      z z₀ e hW hwhole hH hden
  have hpow : δ^h₁ ≤ δ^h₀/(3456*R) := by
    calc
      δ^h₁ = δ^(h₁-h₀) * δ^h₀ := by rw [← Real.rpow_add hδ, sub_add_cancel]
      _ ≤ (1/(3456*R)) * δ^h₀ :=
        mul_le_mul_of_nonneg_right (HD δ hδ (hδd.trans (min_le_right _ _)))
          (Real.rpow_nonneg hδ.le h₀)
      _ = _ := by ring
  have hD' : O (δ^h₁) * μ (P A B (4*R*c) z' e') ≤ μ H :=
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) le_rfl).trans hD
  have hDreal : O (δ^h₁*(A*B*(4*R*c))) ≤ μ H := by
    have hvol : μ (P A B (4*R*c) z' e') = O (A*B*(4*R*c)) :=
      WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P
      (ha.le.trans haA) ((ha.le.trans haA).trans hAB)
      (((ha.le.trans haA).trans hAB).trans hBc) _ _
    rwa [hvol, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le h₁)] at hD'
  exact ⟨A, B, z', e', haA, hAB, hBc,
    HC δ hδ (hδd.trans (min_le_left _ _)) A B (4*R*c) z' e' H Γ
      (ha.trans_le haA) hAB hBc hc1 hHP hHΓ hDreal hcap,
    hbox, hHP, hD'⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
