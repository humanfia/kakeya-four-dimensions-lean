-- Adapted from this LOT tree, obligation o254, branch x0898, commit 00585850, file Submission/Obl/k4_general_parent_wide_layer_candidates/ActualNativeParentListsAt.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeComparisonLosses
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeParentListAssembly

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open Native.SheetComparison
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The actual native comparison returns dense original parent lists
with the explicit loss used in the subpower sequence theorem. -/
theorem NativeSheetAtlas.parent_lists_at {M : ℕ → ℝ} {k : ℕ} {s Rhat m H ε C : ℝ}
    (atlas : p.NativeSheetAtlas M k s) (hp : p.Valid) (hpM : (p.withLoss M).Valid)
    (hat : (p.withLoss M).AtDepth k s Rhat) (hs : 0 ≤ s)
    (hM : 2 ≤ M k) (hH : 1 ≤ H) (hHM : H ≤ M k)
    (hprojected : projectedSheetConstant ≤ M k) (hC : 0 ≤ C) (hCM : C ≤ M k)
    (hε : 0 < ε) (Match : ComparisonEstimate 4 p.d ε C)
    (L : ProjectedLayer α) (hL : L.Valid p k s m H)
    (hχsmall : p.N k ^ (-m) ≤
      (p.toModel.q k s * p.N k ^ (-p.ℓ * s)) / (10000 * nativeSheetLoss (M k)))
    (hsmall : 3 * M k * p.N k ^ (-1 : ℝ) ≤ 1)
    (hcap : ∀ t : ℝ, 0 ≤ t → t ≤ s → ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ),
      p.μ k {ω | p.toModel.cell (p.N k) (m + s + 1) k ω = z ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / p.N k ^ (-t)⌋ = j ∧
        ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = v₀} ≤
      ENNReal.ofReal (M k * p.N k ^ (-3 * (m + s + 1) - p.d * t)) *
        p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = v₀})
    (source : Measure (α × ℝ)) (hsource : source ≤ p.ρ k)
    (hmass : ENNReal.ofReal ((M k)⁻¹) ≤ source univ) (hcovered : L.Covers source) :
    Nonempty (p.NativeParentLists k s m (nativeFinalListLoss (M k) H p.d ε C) L source) := by
  let B := commonNativeCapConstant (M k)
  let R := nativeReference (M k) H p.d
  let F := nativePruning (M k) R
  let Ls := nativeListParameter (M k) B R
  let Λ := nativeMatchingParameter (M k) B R C ε
  let J := nativeFinalListLoss (M k) H p.d ε C
  let q := p.nativeComparisonTime M k s
  let Q := p.toModel.q k s
  let g := p.N k ^ (-p.ℓ * s)
  let V := nativeSheetLoss (M k)
  have hM1 : 1 ≤ M k := by linarith
  have hMp : 0 < M k := by linarith
  have hNp : 0 < p.N k := by linarith [hp.scale k]
  have hB : 0 < B := by dsimp [B, commonNativeCapConstant]; positivity
  have hR : 0 < R := nativeReference_pos hMp
  obtain ⟨hF, hLs, hfloor, hΛ, hthreshold, hcut, hbad⟩ :=
    native_comparison_thresholds hM1 hB hR hC hCM hε
  obtain ⟨assign, _, ⟨cmp⟩⟩ := atlas.comparison_at p hp hpM hat hs hM hH hHM hprojected
    L hL hχsmall hsmall hcap hF hLs hfloor Match hC hthreshold hΛ source hsource hmass hcovered
  have hbefore := atlas.retained_mass p hp hMp source hsource hmass
  have hbudget := cmp.mass_budget
  rw [p.commonComparisonReference_native hNp] at hbudget
  have hmass₄ := retained_native_comparison_mass hMp hbefore hbudget hcut hbad
  have hbounds := nativeFinalListLoss_bounds (H := H) (d := p.d) hM1 hC hCM hε
  have hJ : 4 * M k ≤ J := hbounds.1
  have hmassJ : ENNReal.ofReal J⁻¹ ≤ cmp.law univ :=
    (ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity : 0 < 4 * M k) hJ)).trans hmass₄
  have hQ : 0 < Q := by
    dsimp [Q, Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q]
    positivity
  have hQ1 : Q ≤ 1 := by
    have hh : (1 : ℝ) ≤ (2 : ℝ) ^ p.T k s := one_le_pow₀ (by norm_num)
    simpa only [Q, Parent.toModel_q] using inv_le_one_of_one_le₀ hh
  have hg : 0 < g := by dsimp [g]; positivity
  have hV : 1 ≤ V := one_le_pow₀ hM1
  have hq : 0 < q := by
    change 0 < Q / (10000 * V)
    positivity
  have hqQ : q ≤ Q := by
    change Q / (10000 * V) ≤ Q
    exact div_le_self hQ.le (by linarith)
  have hχQg : p.N k ^ (-m) ≤ Q * g :=
    hχsmall.trans (div_le_self (mul_pos hQ hg).le (by linarith))
  have hχg : p.N k ^ (-m) ≤ g :=
    hχQg.trans (mul_le_of_le_one_left hg.le hQ1)
  have hforward : (1320 * M k ^ 2 * (p.toModel.q k s / q) ^ 2) *
      (2 * (Ls * Λ ^ p.d)) ≤ J := by
    simpa only [q, p.nativeComparisonTime_ratio] using hbounds.2.1
  have hreverse : (84 * (p.toModel.q k s / q) ^ 2) * (Ls * Λ ^ p.d) ≤ J := by
    simpa only [q, p.nativeComparisonTime_ratio] using hbounds.2.2
  obtain ⟨lists⟩ := native_parent_lists_of_comparison (p.withLoss M) hpM hat L hL
    (Measure.restrict_le_self : source.restrict atlas.badᶜ ≤ source)
    cmp hq hqQ hχg hχQg hLs hΛ hmassJ hforward hreverse
  exact ⟨{ lists with }⟩

end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
