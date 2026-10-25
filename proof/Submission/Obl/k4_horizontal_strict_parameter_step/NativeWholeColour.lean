/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at a5c0b1bcb6dacb66c2e29bec68dd8eae37c23e9d, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeWholeColour.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeCellCaps

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Lib.K4MovingMeshBoxes (measure_movingBox_of_cell_cap)
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_row_cell_regularization

noncomputable section

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- The entire original observed colour has a palette-weighted mass ceiling.
This handles matching bands wider than the unit scalar scale without asking
the original joint cap for an inadmissible scalar width. -/
theorem observed_whole_colour_cap {k : ℕ} [IsFiniteMeasure (cfg.π k)]
    {s ε D a χ R re : ℝ} {m : ℕ}
    {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ} {hH : Fin m → Fin 6 → ℝ}
    {σ : Measure (α × ℝ)}
    (S : NativeComparisonSupport cfg k s σ AH)
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D a m AH group hH)
    (hdom : σ ≤ cfg.μ k)
    (caps : OriginalWidthCapsAt (cfg.N k) (cfg.K k) cfg.d R (cfg.μ k) (cfg.π k) (cfg.b k))
    (hre : R⁻¹ ≤ re) (hre' : re ≤ R)
    (he₀ : R⁻¹ ≤ cfg.e₀) (he₀' : cfg.e₀ ≤ R)
    (hmin : cfg.N k ^ (-R) ≤ 1)
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k)
    (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hχD : χ ≤ D)
    (hχeq : χ = cfg.N k ^ (-cfg.e₀))
    (hδq : cfg.N k ^ (-re) ≤ cfg.timeLength k s)
    (hδD : 3 * cfg.K k * cfg.N k ^ (-re) ≤ D)
    (i : S.table.Index group (cfg.j k s)) :
    σ {p | p ∈ S.event ∧
      S.table.colour group (cfg.j k s) (S.table.source group (cfg.j k s) (S.table.mark p)) =
        S.table.colour group (cfg.j k s) i} ≤
      ENNReal.ofReal (64800 * cfg.K k ^ 2 *
        binWeight (cfg.π k) χ ((S.table.colour group (cfg.j k s) i).1 0) *
          cfg.timeLength k s * D ^ 2) := by
  let T := S.table
  let lab := T.colour group (cfg.j k s) i
  let condition := fun p : α × ℝ => p ∈ S.event ∧
    T.colour group (cfg.j k s) (T.source group (cfg.j k s) (T.mark p)) = lab
  let C := cfg.K k * binWeight (cfg.π k) χ (lab.1 0)
  let C' := (16 * cfg.K k + 2) * C
  have hC : 0 ≤ C := mul_nonneg (by linarith) (binWeight_nonneg _ _ _)
  have hC' : 0 ≤ C' := mul_nonneg (by linarith) hC
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
  have hcell (q : Fin 3 → ℤ) (j : ℤ) :
      σ {p | baseMesh (cfg.N k ^ (-re)) (physicalBase (cfg.b k p.1) p.2) = q ∧
        ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / 1⌋ = j ∧ condition p} ≤
          ENNReal.ofReal (C * (cfg.N k ^ (-re)) ^ 3) := by
    have hh := joint_cell_cap_in_palette (cfg.μ k) σ hdom (cfg.π k) (cfg.b k)
      hN (by linarith) caps hre hre' he₀ he₀' hmin le_rfl condition (lab.1 0)
      (fun p hp => by simpa only [← hχeq] using (hgrid p hp).1) q j
    rw [← hχeq, Real.one_rpow, mul_one] at hh
    exact hh.trans_eq (ENNReal.ofReal_mul hC).symm
  have hhidden : ∀ᵐ p ∂σ, condition p →
      |cfg.b k p.1 2 + p.2 * cfg.b k p.1 5| ≤ 4 * cfg.K k := by
    apply Filter.Eventually.of_forall
    intro p hp
    have ht : |p.2| ≤ 1 := by
      rw [abs_of_nonneg (S.unit p hp.1).1]
      exact (S.unit p hp.1).2
    calc
      _ ≤ |cfg.b k p.1 2| + |p.2 * cfg.b k p.1 5| := abs_add_le _ _
      _ ≤ 2 * cfg.K k + 1 * (2 * cfg.K k) := by
        rw [abs_mul]
        exact add_le_add (S.coefficients p hp.1 2)
          (mul_le_mul ht (S.coefficients p hp.1 5) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hpure (q : Fin 3 → ℤ) :
      σ {p | baseMesh (cfg.N k ^ (-re)) (physicalBase (cfg.b k p.1) p.2) = q ∧ condition p} ≤
        ENNReal.ofReal (C' * (cfg.N k ^ (-re)) ^ 3) := by
    have hh := base_cell_cap_of_bounded_signal σ
      (fun p => physicalBase (cfg.b k p.1) p.2)
      (fun p => cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) condition hδ
      (by norm_num : 0 < (1 : ℝ)) (by linarith : 0 ≤ 4 * cfg.K k) hC hhidden hcell q
    exact hh.trans_eq (by congr 1; dsimp [C']; ring)
  have href := cfg.observed_reference_bounds H T hK hD hD1 hχ hχ1 hχeq S.coefficients i
  have hb := measure_movingBox_of_cell_cap σ
    (fun p => physicalBase (cfg.b k p.1) p.2) condition hδ hδq
    (by linarith : 0 ≤ 3 * cfg.K k) hC'
    ((lab.2 : ℕ) * cfg.timeLength k s)
    ![D * (lab.1 1 : ℝ), D * (lab.1 2 : ℝ)]
    ![χ * (lab.1 0 : ℝ), -(D * (lab.1 1 : ℝ))]
    ![D + χ, 2 * D + χ]
    (by
      intro e
      fin_cases e
      · exact href.1
      · change |-(D * (lab.1 1 : ℝ))| ≤ 3 * cfg.K k
        simpa only [abs_neg] using href.2.1)
    (by intro e; fin_cases e <;> dsimp <;> linarith)
    (by intro e; fin_cases e <;> dsimp <;> linarith) hpure
  apply le_trans (measure_mono ?_) (hb.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro p hp
    have hc : condition p := hp
    have hg := hgrid p hc
    have hblock : p.2 ∈ Icc (((lab.2 : ℕ) : ℝ) * cfg.timeLength k s)
        ((((lab.2 : ℕ) : ℝ) + 1) * cfg.timeLength k s) := by
      have hh := (T.decode_native p hp.1).2
      have hj : cfg.j k s (T.native (T.mark p)) = lab.2 := congrArg Prod.snd hc.2
      rw [hj] at hh
      simpa only [Data.I, Data.timeLength, div_eq_mul_inv] using hh
    refine ⟨static_square_mem_movingBox (S.unit p hp.1) ?_ ?_ ?_ ?_ ?_, hc⟩
    · rw [abs_of_nonneg (by linarith [hblock.1])]
      nlinarith [hblock.2]
    · simpa only [floorPoint, hg.2.1] using floorPoint_error hD (cfg.b k p.1 0)
    · simpa only [floorPoint, hg.2.2] using floorPoint_error hD (cfg.b k p.1 1)
    · simpa only [floorPoint, hg.1] using floorPoint_error hχ (cfg.b k p.1 3)
    · simpa only [hχeq] using S.contact p hp.1
  · have hm : (D + χ) * (2 * D + χ) ≤ 6 * D ^ 2 :=
      (mul_le_mul (by linarith : D + χ ≤ 2 * D)
        (by linarith : 2 * D + χ ≤ 3 * D) (by positivity) (by positivity)).trans_eq (by ring)
    have hc : C' ≤ 18 * cfg.K k * C :=
      mul_le_mul_of_nonneg_right (by linarith : 16 * cfg.K k + 2 ≤ 18 * cfg.K k) hC
    change 600 * C' * cfg.timeLength k s * (D + χ) * (2 * D + χ) ≤ _
    calc
      _ = 600 * C' * cfg.timeLength k s * ((D + χ) * (2 * D + χ)) := by ring
      _ ≤ 600 * (18 * cfg.K k * C) * cfg.timeLength k s * (6 * D ^ 2) := by gcongr
      _ = _ := by dsimp [C, lab]; ring

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
