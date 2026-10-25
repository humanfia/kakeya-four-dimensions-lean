-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AlignmentBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.PowerBudget
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TruncatedEnergy

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

noncomputable def alignmentKappa (ε : ℝ) : ℝ := ε ^ 2 / 1000

noncomputable def alignmentEta (ε : ℝ) : ℝ := alignmentKappa ε * ε / 100

noncomputable def alignmentConstant (ε : ℝ) : ℝ :=
  (160 : ℝ) ^ (1 - ε) * 8 * (8192 : ℝ) ^ (2 : ℕ) * energyConstant (1 - ε / 2) *
    (2 : ℝ) ^ (1 - ε / 2)

theorem alignment_parameter_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < alignmentKappa ε ∧ 0 < alignmentEta ε ∧
      alignmentEta ε ≤ alignmentKappa ε ∧ alignmentKappa ε < ε / 2 ∧
      2 * alignmentEta ε < alignmentKappa ε * ε ∧
      2 * alignmentEta ε < ε ^ 2 / 4 - 2 * alignmentEta ε - 2 * alignmentKappa ε := by
  have hκ : 0 < alignmentKappa ε := by unfold alignmentKappa; positivity
  have hη : 0 < alignmentEta ε := by unfold alignmentEta; positivity
  have hsq : ε ^ 2 ≤ ε := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε1)]
  have hηκ : alignmentEta ε ≤ alignmentKappa ε / 100 := by
    unfold alignmentEta
    nlinarith [mul_le_mul_of_nonneg_left hε1 hκ.le]
  refine ⟨hκ, hη, by linarith, ?_, ?_, ?_⟩
  · dsimp [alignmentKappa]
    nlinarith
  · dsimp [alignmentEta]
    nlinarith [mul_pos hκ hε]
  · dsimp [alignmentKappa] at hηκ ⊢
    nlinarith [sq_pos_of_pos hε]

structure AlignmentScaleBudget (δ ε η κ : ℝ) : Prop where
  scale_le_one : δ ≤ 1
  transverse_reserve : 576 ≤ δ ^ (2 * η - κ * ε)
  radial_scale : 32 * δ ^ (ε - κ) ≤ δ ^ (ε / 2)
  radial_reserve : alignmentConstant ε * δ ^ (ε ^ 2 / 4 - 2 * η - 2 * κ) ≤ δ ^ (2 * η)

theorem exists_alignment_scale_budget {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      AlignmentScaleBudget δ ε (alignmentEta ε) (alignmentKappa ε) := by
  obtain ⟨hκ, hη, hηκ, hκeps, htrans, hrad⟩ := alignment_parameter_bounds hε hε1
  obtain ⟨d₁, hd₁, hd₁1, hb₁⟩ := exists_power_bound 576 (sub_pos.mpr htrans)
  obtain ⟨d₂, hd₂, hd₂1, hb₂⟩ := exists_monomial_bound 32
    (a := ε - alignmentKappa ε) (b := ε / 2) (by linarith)
  obtain ⟨d₃, hd₃, hd₃1, hb₃⟩ := exists_monomial_bound (alignmentConstant ε) hrad
  refine ⟨min d₁ (min d₂ d₃), by positivity, ?_⟩
  intro δ hδ hsmall
  have hs₁ := hsmall.trans (min_le_left _ _)
  have hs₂ := (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs₃ := (hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨hs₁.trans hd₁1, ?_, hb₂ δ hδ hs₂, hb₃ δ hδ hs₃⟩
  simpa only [neg_sub] using hb₁ δ hδ hs₁

end WangZahlLot.Obl.wz_separated_projection_dichotomy
