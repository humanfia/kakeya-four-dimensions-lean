-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.MiddleGlue.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.PolyMain
import Submission.WZ.Obl.wz_intermediate_twist_normalization.LargeOffsets

/-!
# Reduction of `wz_intermediate_twist_normalization` to its middle offset range

Two ranges of the obligation are proved:

* `poly_estimate` (from the bounded offset estimate `B`): offsets `|f 0| ≤ δ^(-κ)`, where
  `κ = η_B(ε) / 24` depends on `ε` through `B`;
* `uniform_large_intermediate` (without `B`): offsets `δ^(-1/3 + min ε 1 / 4) ≤ |f 0|`.

`MiddleRange` is the remaining statement, for every `κ > 0`: offsets
`δ^(-κ) < |f 0| < δ^(-1/3 + min ε 1 / 4)` (together with `100 < |f 0|` and `δ (f 0)² < 1`).
`estimate_of_middle` proves the frozen conclusion of the obligation from `B` and
`MiddleRange B`; only the case split on the offset, minima of the exponents and monotonicity
are used besides the two proved ranges.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_compact_offset_normalization (Space Family Frostman Slope Projection
  Estimate)

/-- The conclusion of the obligation: the projection estimate for `100 < |f 0|` and
`δ (f 0)² < 1`. -/
def IntermediateEstimate : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
      Frostman η δ n x v → ∀ f : ℝ → ℝ, Slope f →
      (100 < |f 0| ∧ δ * (f 0) ^ 2 < 1) →
      ENNReal.ofReal (δ ^ ε) ≤ volume (Projection f (⋃ i, Y i))

/-- The middle offset range, for every `κ > 0`: the part of the obligation not covered by
`poly_estimate` and `uniform_large_intermediate`. -/
def MiddleRange : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
      Frostman η δ n x v → ∀ f : ℝ → ℝ, Slope f →
      100 < |f 0| → δ * (f 0) ^ 2 < 1 → δ ^ (-κ) < |f 0| →
      |f 0| < δ ^ (-(1 / 3 : ℝ) + min ε 1 / 4) →
      ENNReal.ofReal (δ ^ ε) ≤ volume (Projection f (⋃ i, Y i))

theorem family_le {η η' δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Family η δ n x v Y) : Family η' δ n x v Y :=
  WangZahlLot.Obl.wz_normalized_projection_iteration.family_mono hδ hδ1 hη h

theorem frostman_le {η η' δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    {n : ℕ} {x v : Fin n → Space} (h : Frostman η δ n x v) : Frostman η' δ n x v :=
  WangZahlLot.Obl.wz_normalized_projection_iteration.frostman_mono hδ hδ1 hη h

/-- **Glue.** The bounded offset estimate and the middle range give the obligation. -/
theorem estimate_of_middle (hB : Estimate (fun c => |c| ≤ 1)) (hmid : MiddleRange) :
    IntermediateEstimate := by
  intro ε hε
  obtain ⟨κ, hκ, ηp, hηp, dp, hdp, hpoly⟩ := poly_estimate hB ε hε
  obtain ⟨ηm, hηm, dm, hdm, hmidε⟩ := hmid κ hκ ε hε
  obtain ⟨ηl, hηl, dl, hdl, hlarge⟩ := uniform_large_intermediate ε hε
  refine ⟨min ηp (min ηm ηl), lt_min hηp (lt_min hηm hηl),
    min dp (min dm dl), lt_min hdp (lt_min hdm hdl), ?_⟩
  intro δ hδ hd0 hδ100 n x v Y hfam htrans hF f hf hc
  have hδ1 : δ ≤ 1 := by linarith
  have hdp' : δ ≤ dp := hd0.trans (min_le_left _ _)
  have hdm' : δ ≤ dm := hd0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdl' : δ ≤ dl := hd0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hηp' : min ηp (min ηm ηl) ≤ ηp := min_le_left _ _
  have hηm' : min ηp (min ηm ηl) ≤ ηm := (min_le_right _ _).trans (min_le_left _ _)
  have hηl' : min ηp (min ηm ηl) ≤ ηl := (min_le_right _ _).trans (min_le_right _ _)
  by_cases hsmall : |f 0| ≤ δ ^ (-κ)
  · exact hpoly δ hδ hdp' hδ100 n x v Y (family_le hδ hδ1 hηp' hfam) htrans
      (frostman_le hδ hδ1 hηp' hF) f hf hsmall
  push Not at hsmall
  by_cases hbig : δ ^ (-(1 / 3 : ℝ) + min ε 1 / 4) ≤ |f 0|
  · exact hlarge δ hδ hdl' hδ100 n x v Y (family_le hδ hδ1 hηl' hfam) htrans
      (frostman_le hδ hδ1 hηl' hF) f hf hc.1 hc.2.le hbig
  push Not at hbig
  exact hmidε δ hδ hdm' hδ100 n x v Y (family_le hδ hδ1 hηm' hfam) htrans
    (frostman_le hδ hδ1 hηm' hF) f hf hc.1 hc.2 hsmall hbig

end WangZahlLot.Obl.wz_intermediate_twist_normalization
