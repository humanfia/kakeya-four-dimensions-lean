-- Adapted from this LOT tree, obligation o254, branch x0898, commit 00585850, file Submission/Obl/k4_general_parent_wide_layer_candidates/CommonNativeFamilies.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.ActualNativeSheets
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.TrueSourceFactory

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers
open Native.SheetComparison Native.CommonDomain

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The checked native atlas gives actual finite sheet families on every
literal common domain, with one unchanged original parent assignment. -/
theorem NativeSheetAtlas.true_source_factory {M : ℕ → ℝ} {k : ℕ} {s R : ℝ}
    (atlas : p.NativeSheetAtlas M k s) (hp : (p.withLoss M).Valid)
    (hat : (p.withLoss M).AtDepth k s R) (hs : 0 ≤ s) (hM : 0 < M k)
    {aT : ℝ} (Kc : NNReal)
    (hKc : 4 * nativeSheetLoss (M k) ≤ Kc)
    (herr : nativeSheetLoss (M k) * p.N k ^ (-s) ≤ aT / 4)
    {q χ w : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hχg : χ ≤ p.N k ^ (-p.ℓ * s)) (hw : 0 < w)
    (hqw : q * p.N k ^ (-p.ℓ * s) ≤ w)
    (hqsmall : q ≤ (nativeSheetLoss (M k))⁻¹ * p.toModel.q k s / 10000)
    (hχsmall : χ ≤ (nativeSheetLoss (M k))⁻¹ *
      (p.toModel.q k s * p.N k ^ (-p.ℓ * s)) / 10000)
    (hwsmall : w ≤ (nativeSheetLoss (M k))⁻¹ *
      (p.toModel.q k s * p.N k ^ (-p.ℓ * s)) / 10000) :
    ∃ assign : α × ℝ → Fin (p.n k s), Measurable assign ∧
      TrueSourceFactory (p.withLoss M).toParams p.toModel k s q χ w aT Kc
        atlas.bad assign atlas.sheet := by
  have hV : 0 < nativeSheetLoss (M k) := by
    unfold nativeSheetLoss
    positivity
  have hae : ∀ Q, ∀ᵐ ω ∂p.toModel.mu k, ω ∈ p.toModel.parentSet k s Q →
      ω ∉ atlas.bad →
      Native.SheetComparison.SheetOn (atlas.relation Q)
        (atlas.sheet Q (nativeBranch (p.withLoss M).toParams p.toModel k s Q ω))
        (p.nativeSheetBase M k s Q ω)
        (4 * (nativeSheetLoss (M k))⁻¹) (nativeSheetLoss (M k)) ∧
      |eval (p.x k ω.1 ω.2) (p.P k) -
        (atlas.sheet Q (nativeBranch (p.withLoss M).toParams p.toModel k s Q ω)
          (Native.SheetComparison.emb
            (p.nativeSheetBase M k s Q ω))).re| ≤
          nativeSheetLoss (M k) * p.N k ^ (-s) := by
    intro Q
    filter_upwards [atlas.stable Q] with ω hω hparent hbad
    exact hω hparent.1 hparent.2 hbad
  obtain ⟨assign, hassign, _, _, hfam⟩ := exists_true_source_families
    (p.withLoss M).toParams hp.toParams_valid p.toModel hp.toModel_common hs hat.toAtlasAt
    atlas.relation atlas.sheet atlas.bad atlas.bad_measurable
    (fun Q => ⟨atlas.relation_nonzero Q, atlas.relation_degree Q⟩)
    hae aT Kc hV.le hKc herr hq hχ hχ1 hχg hw hqw (inv_pos.mpr hV)
    hqsmall hχsmall hwsmall
  refine ⟨assign, hassign, ?_⟩
  intro μD D hac hbad hcode
  obtain ⟨f, decode, hinj, hwitness, hcanonical, hdecode⟩ := hfam μD D hac hbad hcode
  refine ⟨f, decode, hinj, ?_, hcanonical, hdecode⟩
  intro j ω hω
  have hd := hwitness j ω hω
  have hparent := hd.2.1.1
  have hlabel : (decode j).1 = assign ω := congrArg Prod.fst hd.1
  rw [hlabel]
  exact hparent

end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
