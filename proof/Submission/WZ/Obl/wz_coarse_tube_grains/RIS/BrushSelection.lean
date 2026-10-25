-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RelativeIncidence
import Submission.WZ.Obl.wz_transverse_brush_selection
import Submission.WZ.Obl.wz_transverse_stem_deletion.Geometry

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

/-- Explicit stem deletion, with the geometric coefficient kept visible so
that the angular scale can depend on the fine scale. -/
theorem stem_deletion_numeric {δ r b L : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hb : 0 < b)
    (hL : 0 ≤ L) {x v y w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hsep : b ≤ min ‖v - w‖ ‖v + w‖) {Y : Set Space}
    (hY : Y ⊆ Tube δ x v) (hdense : ENNReal.ofReal (L * δ ^ 2) ≤ volume Y)
    (hbudget : 128 * (8 * (δ + r) / b + δ) ≤ L / 2) :
    ENNReal.ofReal (L / 2 * δ ^ 2) ≤
      volume (Y \ Metric.thickening r (Set.range fun t : ℝ => y + t • w)) := by
  let H := Metric.thickening r (Set.range fun t : ℝ => y + t • w)
  have hremoved : volume (Y ∩ H) ≤ ENNReal.ofReal (L / 2 * δ ^ 2) := by
    refine (measure_mono (inter_subset_inter_left H hY)).trans
      ((wz_transverse_stem_deletion.tube_line_intersection_volume_le hδ hr hb hv hw hsep).trans ?_)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hbudget (sq_nonneg δ))
  calc
    _ = ENNReal.ofReal (L * δ ^ 2) - ENNReal.ofReal (L / 2 * δ ^ 2) := by
      rw [← ENNReal.ofReal_sub _ (by positivity : 0 ≤ L / 2 * δ ^ 2)]
      congr 1
      ring
    _ ≤ volume Y - volume (Y ∩ H) := tsub_le_tsub hdense hremoved
    _ ≤ volume (Y \ (Y ∩ H)) := le_measure_sdiff
    _ = _ := by congr 1; ext p; simp only [mem_sdiff, mem_inter_iff]; tauto

/-- A broad family with union volume at most `U * delta` contains an off-stem
brush of explicitly controlled average density. No incidence regularity is
required, and the original indexing is retained. -/
theorem selected_off_stem_brush :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      ∀ b δ lam U r : ℝ, 0 < b → b ≤ 1 → 0 < δ → δ ≤ 1 / 100 →
        0 < lam → lam ≤ 1 → 0 < U → 0 < r →
        128 * (8 * (δ + r) / b + δ) ≤ a * lam / 2 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
        (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
        (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
        ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i) →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (U * δ) →
        (∀ p u, ‖u‖ = 1 →
          ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
            (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ)) →
        ∃ (i₀ : Fin n) (Z : Fin n → Set Space),
          (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
          (∀ i, Z i ⊆ Tube δ (x i) (v i) \ Metric.thickening r
            (Set.range fun t : ℝ => x i₀ + t • v i₀)) ∧
          (∀ i, (Z i).Nonempty → (Tube δ (x i) (v i) ∩ Tube δ (x i₀) (v i₀)).Nonempty) ∧
          a ^ 2 * b * lam ^ 3 / (2 * U) * (n : ℝ) * δ ^ 2 ≤ shadingMass Z := by
  obtain ⟨a, ha, ha1, hselect⟩ := WangZahlLot.wz_transverse_brush_selection
  refine ⟨a, ha, ha1, ?_⟩
  intro b δ lam U r hb hb1 hδ hδ100 hlam hlam1 hU hr hbudget n x v Y hn hv hT hY hYT hdense hvol hbroad
  obtain ⟨i₀, F, hmeet, hsep, hFdense, hFcount⟩ :=
    hselect b δ lam hb hb1 hδ hδ100 hlam hlam1 n x v Y hn hv hT hY hYT hdense hbroad
  let H := Metric.thickening r (Set.range fun t : ℝ => x i₀ + t • v i₀)
  let Z := fun i => if i ∈ F then Y i \ H else ∅
  have hHm : MeasurableSet H := Metric.isOpen_thickening.measurableSet
  have hZm : ∀ i, MeasurableSet (Z i) := by
    intro i
    dsimp only [Z]
    split_ifs
    · exact (hY i).diff hHm
    · exact MeasurableSet.empty
  have hZY : ∀ i, Z i ⊆ Y i := by
    intro i
    dsimp only [Z]
    split_ifs
    · exact sdiff_subset
    · exact empty_subset _
  have hZfin : ∀ i, volume (Z i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono ((hZY i).trans ((hYT i).trans (hT i))))
  have hZout : ∀ i, Z i ⊆ Tube δ (x i) (v i) \ H := by
    intro i p hp
    by_cases hi : i ∈ F
    · have hp' : p ∈ Y i \ H := by simpa only [Z, ite_eq_left hi] using hp
      exact ⟨hYT i hp'.1, hp'.2⟩
    · simp only [Z, ite_eq_right hi, mem_empty_iff_false] at hp
  have hZdensity : ∀ i ∈ F, a * lam / 2 * δ ^ 2 ≤ (volume (Z i)).toReal := by
    intro i hi
    apply (ENNReal.ofReal_le_iff_le_toReal (hZfin i)).mp
    have hh := stem_deletion_numeric (y := x i₀) hδ hr hb (by positivity : 0 ≤ a * lam)
      (hv i) (hv i₀) (hsep i hi) (hYT i) (by simpa [mul_assoc] using hFdense i hi) hbudget
    simpa only [Z, ite_eq_left hi] using hh
  have hcard : a * b * lam ^ 2 * (n : ℝ) / U ≤ F.card := by
    apply (div_le_iff₀ hU).mpr
    apply (mul_le_mul_iff_left₀ hδ).mp
    have hq : (volume (⋃ i, Y i)).toReal ≤ U * δ :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hvol
    calc
      a * b * lam ^ 2 * (n : ℝ) * δ ≤ F.card * (volume (⋃ i, Y i)).toReal := hFcount
      _ ≤ F.card * (U * δ) := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
      _ = _ := by ring
  refine ⟨i₀, Z, fun i => ⟨hZm i, hZY i⟩, hZout, ?_, ?_⟩
  · intro i hi
    by_cases hiF : i ∈ F
    · exact hmeet i hiF
    · simp only [Z, ite_eq_right hiF, Set.not_nonempty_empty] at hi
  · calc
      _ = a * lam / 2 * δ ^ 2 * (a * b * lam ^ 2 * (n : ℝ) / U) := by ring
      _ ≤ a * lam / 2 * δ ^ 2 * F.card := mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = ∑ _i ∈ F, a * lam / 2 * δ ^ 2 := by simp [mul_comm]
      _ ≤ ∑ i ∈ F, (volume (Z i)).toReal := Finset.sum_le_sum fun i hi => hZdensity i hi
      _ ≤ shadingMass Z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
        (fun _ _ _ => ENNReal.toReal_nonneg)

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
