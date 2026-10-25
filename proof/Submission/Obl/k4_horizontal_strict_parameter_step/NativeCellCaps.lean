/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeCellCaps.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeUniqueSupport
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeMenuBounds
import Submission.Obl.k4_horizontal_strict_parameter_step.NativePaletteCaps
import Submission.Obl.k4_horizontal_strict_parameter_step.PredictorCellCaps

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_row_cell_regularization

noncomputable section

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- The actual source or witness menu has original physical cell ceilings.
The coefficient uses the unchanged original velocity palette; observed pair
fibres are never normalized or given artificial mass floors. -/
theorem observed_tag_base_cell_cap {k : ℕ} [IsFiniteMeasure (cfg.π k)]
    {s ε D a χ M R re A : ℝ} {m : ℕ}
    {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    {σ : Measure (α × ℝ)}
    (S : NativeComparisonSupport cfg k s σ AH)
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    (hdom : σ ≤ cfg.μ k)
    (caps : OriginalWidthCapsAt (cfg.N k) (cfg.K k) cfg.d R (cfg.μ k) (cfg.π k) (cfg.b k))
    (hre : R⁻¹ ≤ re) (hre' : re ≤ R)
    (he₀ : R⁻¹ ≤ cfg.e₀) (he₀' : cfg.e₀ ≤ R)
    (hA : cfg.N k ^ (-R) ≤ A) (hA1 : A ≤ 1)
    (frame : (Fin 3 → ℤ) × Fin (2 ^ cfg.T k s) → ComparisonFrame)
    (hframe : ∀ g j, (frame (g, j)).velocity = χ * (g 0 : ℝ))
    (L : Fin (cfg.n k s) → Fin 4 → ℝ) (hL : ∀ i (e : Fin 3), |L i e.succ| ≤ M)
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hM : 0 ≤ M)
    (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hχeq : χ = cfg.N k ^ (-cfg.e₀))
    (tag : Fin S.table.count → S.table.Index group (cfg.j k s))
    (htag : ∀ r, S.table.colour group (cfg.j k s) (tag r) =
      S.table.colour group (cfg.j k s) (S.table.source group (cfg.j k s) r))
    (hnear : ∀ p ∈ S.event,
      |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
        predictor (S.table.physicalPredictors group (cfg.j k s) frame hH L
          (tag (S.table.mark p))) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ A)
    (hround : let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
      2 * (4 * B) * cfg.N k ^ (-re) + (6 * (4 * B) / D) *
        (χ + (3 * cfg.K k + 1) * cfg.N k ^ (-re)) ≤ A)
    (i : S.table.Index group (cfg.j k s)) (q : Fin 3 → ℤ) :
    σ {p | baseMesh (cfg.N k ^ (-re)) (physicalBase (cfg.b k p.1) p.2) = q ∧
      tag (S.table.mark p) = i} ≤
      ENNReal.ofReal (7 * (cfg.K k * A ^ cfg.d *
        binWeight (cfg.π k) χ ((S.table.colour group (cfg.j k s) i).1 0))) *
          ENNReal.ofReal ((cfg.N k ^ (-re)) ^ 3) := by
  let T := S.table
  let f := T.physicalPredictors group (cfg.j k s) frame hH L
  let B := cfg.N k ^ ε + M * (1 + 6 * cfg.K k)
  let v := (frame (T.colour group (cfg.j k s) i)).velocity
  let C := cfg.K k * A ^ cfg.d * binWeight (cfg.π k) χ
    ((T.colour group (cfg.j k s) i).1 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg
    ((Real.rpow_pos_of_pos hN _).trans_le hA).le _)) (binWeight_nonneg _ _ _)
  have hAp : 0 < A := (Real.rpow_pos_of_pos hN _).trans_le hA
  have hcolour (p : α × ℝ) (hi : tag (T.mark p) = i) :
      T.colour group (cfg.j k s) i =
        T.colour group (cfg.j k s) (T.source group (cfg.j k s) (T.mark p)) := by
    rw [← hi]
    exact htag _
  have hcode (p : α × ℝ) (hp : p ∈ S.event) (hi : tag (T.mark p) = i) :
      ⌊cfg.b k p.1 3 / cfg.N k ^ (-cfg.e₀)⌋ = (T.colour group (cfg.j k s) i).1 0 := by
    have hg := (H.2.2.1 (T.old (T.mark p))).1 p.1 (T.decode_old p hp).1
    rw [hcolour p hi]
    exact hg.1
  have hcond : ∀ᵐ p ∂σ, tag (T.mark p) = i →
      p.2 ∈ Icc (0 : ℝ) 1 ∧ |cfg.b k p.1 3 - v| ≤ χ ∧
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ χ ∧ |cfg.b k p.1 0| ≤ 3 * cfg.K k ∧
      |predictorTimeSlope (f i) (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ 2 * (4 * B) := by
    filter_upwards [S.conull] with p hp hi
    have hc := hcolour p hi
    have hvel : |cfg.b k p.1 3 - v| ≤ χ := by
      dsimp [v]
      rw [show T.colour group (cfg.j k s) i =
        ((T.colour group (cfg.j k s) i).1, (T.colour group (cfg.j k s) i).2) from rfl,
        hframe]
      have hh := hcode p hp hi
      rw [← hχeq] at hh
      simpa only [floorPoint, hh] using floorPoint_error hχ (cfg.b k p.1 3)
    have hd := cfg.observed_menu_derivatives H T frame hframe L hL hN hK hM hD hD1
      hχ hχ1 hχeq S.coefficients p hp i hc
      (show p.2 ∈ Icc (-1 : ℝ) 2 from ⟨by linarith [(S.unit p hp).1],
        by linarith [(S.unit p hp).2]⟩)
    refine ⟨S.unit p hp, hvel, ?_, (S.coefficients p hp 0).trans (by linarith), ?_⟩
    · simpa only [hχeq] using S.contact p hp
    · exact hd.1.trans (by change 2 * B ≤ 2 * (4 * B); nlinarith)
  have hfit : ∀ᵐ p ∂σ, tag (T.mark p) = i →
      |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
        predictor (f i) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ A := by
    filter_upwards [S.conull] with p hp hi
    have hh := hnear p hp
    change |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5 -
      predictor (f (tag (T.mark p))) p.2 (cfg.b k p.1 0) (cfg.b k p.1 1)| ≤ A at hh
    rwa [hi] at hh
  obtain ⟨p₀, hp₀, hc₀⟩ := S.index_has_colour_point H i
  have hgrad : ∀ t ∈ Icc (0 : ℝ) 1,
      |f i 2 + f i 3 * t| ≤ 2 * (4 * B) / D ∧
      |f i 4 + f i 5 * t| ≤ 2 * (4 * B) / D := by
    intro t ht
    have hd := (cfg.observed_menu_derivatives H T frame hframe L hL hN hK hM hD hD1
      hχ hχ1 hχeq S.coefficients p₀ hp₀ i hc₀
      (show t ∈ Icc (-1 : ℝ) 2 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)).2
    rw [show 2 * (4 * B) = 8 * B from by ring]
    exact hd
  have hv : |v| ≤ 3 * cfg.K k := by
    dsimp [v]
    rw [show T.colour group (cfg.j k s) i =
      ((T.colour group (cfg.j k s) i).1, (T.colour group (cfg.j k s) i).2) from rfl,
      hframe]
    exact (cfg.observed_reference_bounds H T hK hD hD1 hχ hχ1 hχeq S.coefficients i).1
  have hcell (q' : Fin 3 → ℤ) (j : ℤ) :
      σ {p | baseMesh (cfg.N k ^ (-re)) (physicalBase (cfg.b k p.1) p.2) = q' ∧
        ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / A⌋ = j ∧ tag (T.mark p) = i} ≤
          ENNReal.ofReal (C * (cfg.N k ^ (-re)) ^ 3) := by
    have hh := joint_cell_cap_in_palette_ae (cfg.μ k) σ hdom (cfg.π k) (cfg.b k)
      hN (by linarith) caps hre hre' he₀ he₀' hA hA1
      (fun p => tag (T.mark p) = i) ((T.colour group (cfg.j k s) i).1 0)
      (S.conull.mono (fun p hp => hcode p hp)) q' j
    rw [← hχeq] at hh
    exact hh.trans_eq (ENNReal.ofReal_mul hC).symm
  exact predictor_base_cell_cap σ (cfg.b k) (f i) (fun p => tag (T.mark p) = i)
    (Real.rpow_pos_of_pos hN _) hAp hC (by positivity : 0 ≤ 4 * B) hD hv
    hcond hfit hgrad hround hcell q

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
