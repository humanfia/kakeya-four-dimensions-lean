/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeIntegratedBand.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeCellCaps

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_row_cell_regularization

noncomputable section

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- A graph band for any actual same-colour query sheet is bounded using the
original joint cap and the original palette. The coefficient includes the full
original time-block length and static-cell area. -/
theorem observed_integrated_band {k : ℕ} [IsFiniteMeasure (cfg.π k)]
    {s ε D a χ M R re w : ℝ} {m : ℕ}
    {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    {σ : Measure (α × ℝ)}
    (S : NativeComparisonSupport cfg k s σ AH)
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    (hdom : σ ≤ cfg.μ k)
    (caps : OriginalWidthCapsAt (cfg.N k) (cfg.K k) cfg.d R (cfg.μ k) (cfg.π k) (cfg.b k))
    (hre : R⁻¹ ≤ re) (hre' : re ≤ R)
    (he₀ : R⁻¹ ≤ cfg.e₀) (he₀' : cfg.e₀ ≤ R)
    (hw : cfg.N k ^ (-R) ≤ w) (hw1 : w ≤ 1)
    (frame : (Fin 3 → ℤ) × Fin (2 ^ cfg.T k s) → ComparisonFrame)
    (hframe : ∀ g j, (frame (g, j)).velocity = χ * (g 0 : ℝ))
    (L : Fin (cfg.n k s) → Fin 4 → ℝ) (hL : ∀ i (e : Fin 3), |L i e.succ| ≤ M)
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hM : 0 ≤ M)
    (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hχD : χ ≤ D)
    (hχeq : χ = cfg.N k ^ (-cfg.e₀))
    (hδq : cfg.N k ^ (-re) ≤ cfg.timeLength k s)
    (hδD : 3 * cfg.K k * cfg.N k ^ (-re) ≤ D)
    (hround : let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
      2 * (4 * B) * cfg.N k ^ (-re) + (6 * (4 * B) / D) *
        (χ + (3 * cfg.K k + 1) * cfg.N k ^ (-re)) ≤ w)
    (i : S.table.Index group (cfg.j k s)) :
    σ {p | p ∈ S.event ∧
      S.table.colour group (cfg.j k s) (S.table.source group (cfg.j k s) (S.table.mark p)) =
        S.table.colour group (cfg.j k s) i ∧
      |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
        predictor (S.table.physicalPredictors group (cfg.j k s) frame hH L i)
          p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ w} ≤
      ENNReal.ofReal (25200 * cfg.K k * w ^ cfg.d *
        binWeight (cfg.π k) χ ((S.table.colour group (cfg.j k s) i).1 0) *
          cfg.timeLength k s * D ^ 2) := by
  let T := S.table
  let f := T.physicalPredictors group (cfg.j k s) frame hH L i
  let lab := T.colour group (cfg.j k s) i
  let condition := fun p : α × ℝ => p ∈ S.event ∧
    T.colour group (cfg.j k s) (T.source group (cfg.j k s) (T.mark p)) = lab
  let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
  let C := cfg.K k * w ^ cfg.d * binWeight (cfg.π k) χ (lab.1 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hwp : 0 < w := (Real.rpow_pos_of_pos hN _).trans_le hw
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by linarith)
    (Real.rpow_nonneg hwp.le _)) (binWeight_nonneg _ _ _)
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hδ : 0 < cfg.N k ^ (-re) := Real.rpow_pos_of_pos hN _
  have hχ1 : χ ≤ 1 := hχD.trans hD1
  have hδD' : cfg.N k ^ (-re) ≤ D := by
    have hh := mul_le_mul_of_nonneg_right (by linarith : 1 ≤ 3 * cfg.K k) hδ.le
    nlinarith
  have hgrid (p : α × ℝ) (hp : condition p) :
      ⌊cfg.b k p.1 3 / χ⌋ = lab.1 0 ∧
      ⌊cfg.b k p.1 0 / D⌋ = lab.1 1 ∧ ⌊cfg.b k p.1 1 / D⌋ = lab.1 2 := by
    have hg := (H.2.2.1 (T.old (T.mark p))).1 p.1 (T.decode_old p hp.1).1
    have hl : group (T.old (T.mark p)) = lab.1 := congrArg Prod.fst hp.2
    rw [hl] at hg
    simpa only [hχeq] using hg
  have hcond : ∀ p, condition p → p.2 ∈ Icc (0 : ℝ) 1 ∧
      |cfg.b k p.1 3 - χ * (lab.1 0 : ℝ)| ≤ χ ∧
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ χ ∧ |cfg.b k p.1 0| ≤ 3 * cfg.K k ∧
      |predictorTimeSlope f (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ 2 * (4 * B) := by
    intro p hp
    have hd := cfg.observed_menu_derivatives H T frame hframe L hL hN hK hM hD hD1
      hχ hχ1 hχeq S.coefficients p hp.1 i hp.2.symm
      (show p.2 ∈ Icc (-1 : ℝ) 2 from ⟨by linarith [(S.unit p hp.1).1],
        by linarith [(S.unit p hp.1).2]⟩)
    refine ⟨S.unit p hp.1, ?_, ?_, (S.coefficients p hp.1 0).trans (by linarith), ?_⟩
    · simpa only [floorPoint, (hgrid p hp).1] using floorPoint_error hχ (cfg.b k p.1 3)
    · simpa only [hχeq] using S.contact p hp.1
    · exact hd.1.trans (by change 2 * B ≤ 2 * (4 * B); nlinarith)
  obtain ⟨p₀, hp₀, hc₀⟩ := S.index_has_colour_point H i
  have hgrad : ∀ t ∈ Icc (0 : ℝ) 1,
      |f 2 + f 3 * t| ≤ 2 * (4 * B) / D ∧ |f 4 + f 5 * t| ≤ 2 * (4 * B) / D := by
    intro t ht
    rw [show 2 * (4 * B) = 8 * B from by ring]
    exact (cfg.observed_menu_derivatives H T frame hframe L hL hN hK hM hD hD1
      hχ hχ1 hχeq S.coefficients p₀ hp₀ i hc₀
      (show t ∈ Icc (-1 : ℝ) 2 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)).2
  have href := cfg.observed_reference_bounds H T hK hD hD1 hχ hχ1 hχeq S.coefficients i
  have hcell (q : Fin 3 → ℤ) (j : ℤ) :
      σ {p | baseMesh (cfg.N k ^ (-re)) (physicalBase (cfg.b k p.1) p.2) = q ∧
        ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / w⌋ = j ∧ condition p} ≤
          ENNReal.ofReal (C * (cfg.N k ^ (-re)) ^ 3) := by
    have hh := joint_cell_cap_in_palette (cfg.μ k) σ hdom (cfg.π k) (cfg.b k)
      hN (by linarith) caps hre hre' he₀ he₀' hw hw1 condition (lab.1 0)
      (fun p hp => by simpa only [← hχeq] using (hgrid p hp).1) q j
    rw [← hχeq] at hh
    exact hh.trans_eq (ENNReal.ofReal_mul hC).symm
  have hb := integrated_parameter_graph_cap σ (cfg.b k) f condition hδ hwp hδq
    (by linarith : 0 ≤ 3 * cfg.K k) hC (by positivity : 0 ≤ 4 * B) hD
    ((lab.2 : ℕ) * cfg.timeLength k s) (D * (lab.1 1 : ℝ)) (D * (lab.1 2 : ℝ))
    (χ * (lab.1 0 : ℝ)) D 0 href.1 href.1 href.2.1
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hcond hgrad hround hcell
  apply le_trans (measure_mono ?_) (hb.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro p hp
    have hc : condition p := ⟨hp.1, hp.2.1⟩
    have hg := hgrid p hc
    have hblock : p.2 ∈ Icc (((lab.2 : ℕ) : ℝ) * cfg.timeLength k s)
        ((((lab.2 : ℕ) : ℝ) + 1) * cfg.timeLength k s) := by
      have hh := (T.decode_native p hp.1).2
      have hj : cfg.j k s (T.native (T.mark p)) = lab.2 := congrArg Prod.snd hc.2
      rw [hj] at hh
      simpa only [Data.I, Data.timeLength, div_eq_mul_inv] using hh
    refine ⟨?_, ?_, ?_, ?_, hc⟩
    · rw [abs_of_nonneg (by linarith [hblock.1])]
      nlinarith [hblock.2]
    · simpa only [floorPoint, hg.2.1] using floorPoint_error hD (cfg.b k p.1 0)
    · simpa only [floorPoint, hg.2.2] using floorPoint_error hD (cfg.b k p.1 1)
    · simpa only [add_zero] using hp.2.2
  · have hm : (D + χ) * (2 * D + χ) ≤ 6 * D ^ 2 := by
      exact (mul_le_mul (by linarith : D + χ ≤ 2 * D)
        (by linarith : 2 * D + χ ≤ 3 * D) (by positivity) (by positivity)).trans_eq (by ring)
    calc
      _ = 4200 * C * cfg.timeLength k s * ((D + χ) * (2 * D + χ)) := by ring
      _ ≤ 4200 * C * cfg.timeLength k s * (6 * D ^ 2) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by dsimp [C, lab]; ring

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
