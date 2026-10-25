-- Adapted from this LOT tree, obligation o254, branch x0898, commit 00585850, file Submission/Obl/k4_general_parent_wide_layer_candidates/ActualNativeComparisonAt.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.PreparedComparisonAt
import Submission.Obl.k4_general_wide_layer_offset_comparison.CommonNativeFamilies
import Submission.Obl.k4_general_wide_layer_offset_comparison.PreparedProjectedLayer
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeCommonNumerics
import Submission.Obl.k4_general_wide_layer_offset_comparison.BasicFacts

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers
open Native.SheetComparison
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

def nativeComparisonTime (M : ℕ → ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  p.toModel.q k s / (10000 * nativeSheetLoss (M k))

def nativeComparisonWidth (M : ℕ → ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  p.nativeComparisonTime M k s * p.N k ^ (-p.ℓ * s)

def nativeComparisonTolerance (M : ℕ → ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  8 * nativeSheetLoss (M k) * p.N k ^ (-s)

/-- The native atlas and literal primitive caps instantiate the entire
prepared comparison. Its source is the original source outside the
single native exception; there is no additional graph or density input. -/
theorem NativeSheetAtlas.comparison_at {M : ℕ → ℝ} {k : ℕ} {s R m H : ℝ}
    (atlas : p.NativeSheetAtlas M k s) (hp : p.Valid) (hpM : (p.withLoss M).Valid)
    (hat : (p.withLoss M).AtDepth k s R) (hs : 0 ≤ s)
    (hM : 2 ≤ M k) (hH : 1 ≤ H) (hHM : H ≤ M k)
    (hprojected : projectedSheetConstant ≤ M k)
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
    {Fprune Llist ε C Λ : ℝ}
    (hFprune : 0 < Fprune) (hLlist : 1 ≤ Llist)
    (hLfloor : 14 * commonNativeCapConstant (M k) * Fprune ≤ Llist)
    (Match : ComparisonEstimate 4 p.d ε C) (hC : 0 ≤ C)
    (hΛ : C * Llist ^ (1 / ε) ≤ Λ) (hΛ1 : 1 ≤ Λ)
    (source : Measure (α × ℝ)) (hsource : source ≤ p.ρ k)
    (hmass : ENNReal.ofReal ((M k)⁻¹) ≤ source univ)
    (hcovered : L.Covers source) :
    ∃ assign : α × ℝ → Fin (p.n k s), Measurable assign ∧
      Nonempty (PreparedComparison (p.withLoss M).toParams p.toModel k s H
        (p.nativeComparisonTime M k s) (p.N k ^ (-m)) (p.nativeComparisonWidth M k s)
        (p.nativeComparisonTolerance M k s) Fprune Llist ε C Λ L.toPrepared
        (source.restrict atlas.badᶜ) assign atlas.sheet) := by
  let Q := p.toModel.q k s
  let g := p.N k ^ (-p.ℓ * s)
  let V := nativeSheetLoss (M k)
  let a := p.N k ^ (-s)
  let χ := p.N k ^ (-m)
  let q := p.nativeComparisonTime M k s
  let w := p.nativeComparisonWidth M k s
  let aT := p.nativeComparisonTolerance M k s
  have hNp : 0 < p.N k := by linarith [hp.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [hp.scale k]
  have hM1 : 1 ≤ M k := by linarith
  have hMp : 0 < M k := by linarith
  have hC4 : 4 ≤ nativeSheetExponent := by dsimp [nativeSheetExponent]; omega
  have hV4 : M k ^ 4 ≤ V := pow_le_pow_right₀ hM1 hC4
  have hMV : M k ≤ V := by
    change M k ≤ M k ^ nativeSheetExponent
    simpa only [pow_one] using pow_le_pow_right₀ hM1 (show 1 ≤ nativeSheetExponent by omega)
  have hV1 : 1 ≤ V := hM1.trans hMV
  have hVp : 0 < V := zero_lt_one.trans_le hV1
  have hQ : 0 < Q := by dsimp [Q, PreparedModel.q]; positivity
  have hQ1 : Q ≤ 1 := by
    have hh : (1 : ℝ) ≤ (2 : ℝ) ^ p.T k s := one_le_pow₀ (by norm_num)
    simpa only [Q, Parent.toModel_q] using inv_le_one_of_one_le₀ hh
  have hg : 0 < g := by dsimp [g]; positivity
  have hg1 : g ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1
    (by nlinarith [hp.transverse_pos])
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hχ : 0 < χ := by dsimp [χ]; positivity
  have hβ : g / M k ≤ L.β :=
    (div_le_div_of_nonneg_left hg.le (zero_lt_one.trans_le hH) hHM).trans hL.2.1
  obtain ⟨hq, hw, hqQ, hq1, hχ1, hχg, hχQ, hχQg, hwQg, hwβ, hχw, hqsmall, hwsmall⟩ :=
    native_common_scale_bounds hM1 hMV hQ hQ1 hg hg1 hχ hχsmall hβ
  have hwq : w ≤ q := by
    change q * g ≤ q
    exact mul_le_of_le_one_right hq.le hg1
  have hχq : χ ≤ q := hχw.trans hwq
  have hqw : q * g ≤ w := le_rfl
  let Kchart : NNReal := ⟨4 * V, by positivity⟩
  have hprojV : projectedSheetConstant * H ^ 3 ≤ V := by
    calc
      _ ≤ M k * M k ^ 3 := mul_le_mul hprojected
        (pow_le_pow_left₀ (by linarith) hHM 3) (by positivity)
        (by positivity)
      _ = M k ^ 4 := by ring
      _ ≤ V := hV4
  have hKchart : 4 * (projectedSheetConstant * H ^ 3) ≤ Kchart := by
    exact mul_le_mul_of_nonneg_left hprojV (by norm_num)
  have hHerr : H * a ≤ V * a :=
    mul_le_mul_of_nonneg_right (hHM.trans hMV) ha.le
  have hprojerr : 4 * (H * a) ≤ aT := by
    dsimp [aT, nativeComparisonTolerance]
    nlinarith [mul_nonneg hVp.le ha.le]
  have hnativerr : V * a ≤ aT / 4 := by
    dsimp [aT, nativeComparisonTolerance]
    nlinarith [mul_nonneg hVp.le ha.le]
  obtain ⟨assign, hassign, hfactory⟩ := atlas.true_source_factory p hpM hat hs hMp
    Kchart le_rfl hnativerr hq hχ hχ1 hχg hw hqw hqsmall (hχw.trans hwsmall) hwsmall
  let ζ := source.restrict atlas.badᶜ
  have hζ : ζ ≤ p.μ k :=
    Measure.restrict_le_self.trans (hsource.trans (hp.basic k).2.2.2.2.1)
  have hret := atlas.retained_mass p hp hMp source hsource hmass
  have hζpos : ζ univ ≠ 0 := ne_of_gt
    ((ENNReal.ofReal_pos.mpr (by positivity : 0 < (2 * M k)⁻¹)).trans_le hret)
  have hζbad : ζ atlas.bad = 0 := by
    rw [Measure.restrict_apply atlas.bad_measurable]
    simp
  letI : IsFiniteMeasure ζ :=
    ⟨(hζ univ).trans_lt ((Basic.mass_le p hp.basic k).trans_lt ENNReal.ofReal_lt_top)⟩
  have hζcovered : ∀ᵐ ω ∂ζ, ω ∈ L.toPrepared.covered :=
    ae_restrict_of_ae (L.covers_toPrepared source hcovered)
  have hσ : 0 < a / 100 := by positivity
  have hσsmall : a / 100 ≤ 1 / 24 := by linarith
  have hδq := native_common_mesh_resolution (s := s) (m := m) hNp hM1 hχq hsmall
  have hδχ := native_common_mesh_resolution (s := s) (m := m) hNp hM1 (le_rfl : χ ≤ χ) hsmall
  have hδw := native_common_mesh_resolution (s := s) (m := m) hNp hM1 hχw hsmall
  have hmesh : 2 * (Kchart : ℝ) * (3 * (a / 100)) ≤ aT / 2 :=
    native_common_jitter_resolution hVp.le ha.le
  have haMin : a ≤ aT := by
    dsimp [aT, nativeComparisonTolerance]
    nlinarith [mul_le_mul_of_nonneg_right hV1 ha.le]
  refine ⟨assign, hassign, ?_⟩
  exact prepared_comparison_at (p.withLoss M).toParams hpM.toParams_valid p.toModel
    hpM.toModel_common hs hat.toAtlasAt L.toPrepared (L.valid_toPrepared p hL) hH hq hqQ hχ
    hχQ hχQg hw hwQg hwβ hqw (by dsimp [aT, nativeComparisonTolerance]; positivity)
    Kchart hKchart hprojerr atlas.bad assign atlas.sheet hfactory rfl hs haMin
    hσ hσsmall hδq hδχ hδw hmesh hcap hFprune hLlist hLfloor Match hC hΛ hΛ1
    ζ hζ hζpos hζbad hζcovered

end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
