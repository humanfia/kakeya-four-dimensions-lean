-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.LocalGridLinearity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.GridParity
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.ShadingHeight
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.VerticalRestrictions
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.PowerFromLinearity

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory
open scoped ENNReal

/-- All heights in one grid cell at which an affine function fits the slope. -/
def affineFitHeights (f : ℝ → ℝ) (h ρ : ℝ) (j : ℤ) (a b : ℝ) : Set ℝ :=
  Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h) ∩ {z | |f z - (a + b * z)| ≤ ρ}

theorem isCompact_affineFitHeights {f : ℝ → ℝ} (hf : Continuous f)
    (h ρ : ℝ) (j : ℤ) (a b : ℝ) :
    IsCompact (affineFitHeights f h ρ j a b) := by
  apply isCompact_Icc.inter_right
  exact isClosed_le (by fun_prop) continuous_const

/-- The geometric input can be confined to independent affine fits on finitely
many height cells and a lower bound for their retained shading mass. -/
def LocalGridLinearity (σ : ℝ) : Prop :=
  ∀ ε θ : ℝ, 0 < ε → 0 < θ → ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ ρ : ℝ, δ ^ (1 - θ) ≤ ρ → ρ ≤ δ ^ θ →
      ∀ (G : SlopeGeometry) (Y : Fin G.n → Set Space),
        RegularGrainFamily σ η δ G Y →
        ∃ (J : Finset ℤ) (a b : ℤ → ℝ),
          ENNReal.ofReal (δ ^ ε) * (∑ i, volume (Y i)) ≤
            shadingHeightMeasure Y
              (⋃ j ∈ J, affineFitHeights G.f (Real.sqrt ρ) ρ j (a j) (b j))

theorem shadings_from_local_grid_fits {ρ : ℝ} (hρ : 0 < ρ)
    {n : ℕ} (Y : Fin n → Set Space) (hY : ∀ i, IsCompact (Y i))
    (f : ℝ → ℝ) (hf : Continuous f) (J : Finset ℤ) (a b : ℤ → ℝ) :
    ∃ Z : Fin n → Set Space, (∀ i, Z i ⊆ Y i) ∧ (∀ i, IsCompact (Z i)) ∧
      shadingHeightMeasure Y
          (⋃ j ∈ J, affineFitHeights f (Real.sqrt ρ) ρ j (a j) (b j)) ≤
        2 * (∑ i, volume (Z i)) ∧ AffineSlopeFit ρ f Z := by
  let D := fun j => affineFitHeights f (Real.sqrt ρ) ρ j (a j) (b j)
  obtain ⟨D', L, hc, hsub, hmass, hgrid, hfit⟩ :=
    select_and_extend_grid_fits (shadingHeightMeasure Y) (Real.sqrt_pos.mpr hρ) f J D
      (fun j _ => isCompact_affineFitHeights hf _ _ j _ _)
      (fun _ _ => inter_subset_left)
      (fun j _ => ⟨a j, b j, fun _ hz => hz.2⟩)
  refine ⟨restrictShadingHeights Y D', restrictShadingHeights_subset Y D',
    restrictShadingHeights_compact hY hc, ?_, L, hgrid, ?_⟩
  · simpa only [shadingHeightMeasure_apply Y hc.measurableSet] using hmass
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hfit (p 2) hi.2

/-- A parity selection and a small additional power loss assemble independent
slab fits into the family-level input used by the smoothing hierarchy. -/
theorem singleScaleLinearity_of_localGridLinearity {σ : ℝ}
    (h : LocalGridLinearity σ) : SingleScaleLinearity σ := by
  intro ε θ hε hθ
  let α := ε / 4
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨η, d₁, hη, hηα, hd₁, hlocal⟩ := h α θ hα hθ
  obtain ⟨d₂, hd₂, hcut⟩ := cut_le_one hα 2
  have hηε : η ≤ ε := by dsimp [α] at hηα; linarith
  refine ⟨η, min d₁ d₂, hη, hηε, lt_min hd₁ hd₂, ?_⟩
  intro δ hδ hδd ρ hδρ hρδ G Y hY
  have hδ1 : δ ≤ 1 := by linarith [hY.1]
  have hρ : 0 < ρ := (Real.rpow_pos_of_pos hδ _).trans_le hδρ
  obtain ⟨J, a, b, hmass⟩ := hlocal δ hδ (hδd.trans (min_le_left _ _))
    ρ hδρ hρδ G Y hY
  obtain ⟨Z, hZY, hZc, hZmass, hfit⟩ := shadings_from_local_grid_fits hρ Y
    hY.2.1.2.2.1 G.f hY.2.2.2.1.continuous J a b
  have hhalf : ENNReal.ofReal (δ ^ α) ≤ (1 / 2 : ENNReal) := by
    have hcut' := hcut δ hδ (hδd.trans (min_le_right _ _))
    have hh : δ ^ α ≤ (1 / 2 : ℝ) := by linarith
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hh
  have hret : ENNReal.ofReal (δ ^ (2 * α)) * (∑ i, volume (Y i)) ≤
      ∑ i, volume (Z i) := by
    calc
      ENNReal.ofReal (δ ^ (2 * α)) * (∑ i, volume (Y i)) =
          ENNReal.ofReal (δ ^ α) *
            (ENNReal.ofReal (δ ^ α) * (∑ i, volume (Y i))) := by
              rw [two_mul, Real.rpow_add hδ,
                ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), mul_assoc]
      _ ≤ (1 / 2 : ENNReal) *
          shadingHeightMeasure Y
            (⋃ j ∈ J, affineFitHeights G.f (Real.sqrt ρ) ρ j (a j) (b j)) :=
          mul_le_mul' hhalf hmass
      _ ≤ (1 / 2 : ENNReal) * (2 * ∑ i, volume (Z i)) := mul_le_mul' le_rfl hZmass
      _ = ∑ i, volume (Z i) := by
        rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  refine ⟨Z, hZY, ⟨hY.1, ?_, ?_, hY.2.2.2⟩, hfit⟩
  · exact hY.2.1.restrict hδ hδ1 hηε (by dsimp [α] at *; linarith) hZY hZc hret
  · exact hY.2.2.1.restrict_mono hδ
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηε)) hZY

theorem smoothExamples_of_localGridLinearity {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (h : LocalGridLinearity σ)
    (hL : LipschitzExamples σ) : SmoothExamples σ :=
  smoothExamples_of_singleScaleLinearity hσ hσ1
    (singleScaleLinearity_of_localGridLinearity h) hL

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
