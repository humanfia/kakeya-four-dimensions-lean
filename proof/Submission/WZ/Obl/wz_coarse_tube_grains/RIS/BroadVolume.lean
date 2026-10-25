-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BroadVolume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RelativeIncidence

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

/-- Pointwise broadness and average shading density imply a quantitative
lower bound for the union volume, with no separation assumption. -/
theorem broad_union_volume_lower {δ b lam : ℝ} (hδ : 0 < δ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hlam : 0 < lam) {n : ℕ} (hn : 0 < n)
    (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hfin : volume (⋃ i, Y i) ≠ ⊤)
    (hdense : lam * (n : ℝ) * δ ^ 2 ≤ shadingMass Y)
    (hbroad : ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ)) :
    ENNReal.ofReal (b * lam ^ 2 * δ / 8192) ≤ volume (⋃ i, Y i) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hfin (measure_mono (subset_iUnion Y i))
  have hmass_bound : shadingMass Y ≤ (n : ℝ) * (volume (⋃ i, Y i)).toReal := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      ENNReal.toReal_mono hfin (measure_mono (subset_iUnion Y i)))
    simpa only [shadingMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hh
  have hpos : 0 < (volume (⋃ i, Y i)).toReal := by
    have hprod : 0 < lam * (n : ℝ) * δ ^ 2 := by positivity
    have hh := hdense.trans hmass_bound
    nlinarith
  let R : Fin n → Fin n → Prop := fun i j => b < min ‖v j - v i‖ ‖v j + v i‖
  have hcounts : ∀ i p, wz_transverse_brush_selection.multiplicity Y Finset.univ p ≤
      2 * wz_transverse_brush_selection.multiplicity Y (Finset.univ.filter (R i)) p := by
    intro i p
    have hnear := hbroad p (v i) (hv i)
    rw [wz_transverse_brush_selection.incidence_ncard] at hnear
    have hfull : ({j | p ∈ Y j}.ncard : ℝ) =
        wz_transverse_brush_selection.multiplicity Y Finset.univ p := by
      simpa using wz_transverse_brush_selection.incidence_ncard Y (fun _ => True) p
    rw [hfull] at hnear
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => min ‖v j - v i‖ ‖v j + v i‖ ≤ b)
      (fun j => wz_transverse_brush_selection.oneOn (Y j) p)
    simp only [not_le] at hsplit
    change wz_transverse_brush_selection.multiplicity Y
        (Finset.univ.filter fun j => min ‖v j - v i‖ ‖v j + v i‖ ≤ b) p +
      wz_transverse_brush_selection.multiplicity Y (Finset.univ.filter (R i)) p =
        wz_transverse_brush_selection.multiplicity Y Finset.univ p at hsplit
    linarith
  have hpair : ∀ i j, R i j → (volume (Y i ∩ Y j)).toReal ≤ 4096 * δ ^ 3 / b := by
    intro i j hR
    have hsep : b ≤ min ‖v i - v j‖ ‖v i + v j‖ := by
      dsimp [R] at hR
      rw [norm_sub_rev, add_comm]
      exact hR.le
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((measure_mono (inter_subset_inter (hYT i) (hYT j))).trans
        (wz_transverse_brush_selection.transverse_intersection_volume hδ hb hb1 (hv i) (hv j) hsep))
  obtain ⟨i, F, _, henergy⟩ := broad_neighbor_count hn Y R hY hfin hpos
    (by positivity : 0 ≤ 4096 * δ ^ 3 / b) hpair hcounts
  have hF : (F.card : ℝ) ≤ n := by exact_mod_cast (show F.card ≤ n by simpa using F.card_le_univ)
  have henergy' : shadingMass Y ^ 2 ≤
      (8192 * (n : ℝ) ^ 2 * δ ^ 3 / b) * (volume (⋃ i, Y i)).toReal := by
    calc
      _ ≤ 2 * (volume (⋃ i, Y i)).toReal * (n : ℝ) * F.card * (4096 * δ ^ 3 / b) := henergy
      _ ≤ 2 * (volume (⋃ i, Y i)).toReal * (n : ℝ) * n * (4096 * δ ^ 3 / b) := by gcongr
      _ = _ := by ring
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mpr
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 8192 * (n : ℝ) ^ 2 * δ ^ 3 / b)).mp
  calc
    _ = (lam * (n : ℝ) * δ ^ 2) ^ 2 := by field_simp
    _ ≤ shadingMass Y ^ 2 := pow_le_pow_left₀ (by positivity) hdense 2
    _ ≤ _ := henergy'

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
