-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BroadPieceEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.BroadVolume

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

/-- Broadness bounds the second moment using only the number of occupied
indices; unused indices in the ambient family do not cost anything. -/
theorem broad_occupied_energy {n : ℕ} (Y : Fin n → Set Space)
    (R : Fin n → Fin n → Prop) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, volume (Y i) ≠ ⊤) {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ i j, R i j → (volume (Y i ∩ Y j)).toReal ≤ B)
    (hbroad : ∀ i p, incidence Y p ≤
      2 * wz_transverse_brush_selection.multiplicity Y (Finset.univ.filter (R i)) p) :
    (∫ p, incidence Y p ^ 2) ≤ 2 * ({i | (Y i).Nonempty}.ncard : ℝ) ^ 2 * B := by
  let A : Finset (Fin n) := Finset.univ.filter fun i => (Y i).Nonempty
  have hAempty (i : Fin n) (hi : i ∉ A) : Y i = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    intro hh
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
  have hrow (i : Fin n) :
      (∑ j ∈ Finset.univ.filter (fun j => R j i), (volume (Y j ∩ Y i)).toReal) ≤
        if i ∈ A then (A.card : ℝ) * B else 0 := by
    by_cases hi : i ∈ A
    · rw [if_pos hi]
      calc
        _ ≤ ∑ j ∈ Finset.univ.filter (fun j => R j i), if j ∈ A then B else 0 := by
          apply Finset.sum_le_sum
          intro j hj
          by_cases hja : j ∈ A
          · simpa only [if_pos hja] using hpair j i (Finset.mem_filter.mp hj).2
          · simp only [if_neg hja, hAempty j hja, empty_inter, measure_empty, ENNReal.toReal_zero, le_refl]
        _ ≤ ∑ j : Fin n, if j ∈ A then B else 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => by split_ifs <;> positivity)
        _ = _ := by simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          nsmul_eq_mul]
    · simp only [if_neg hi, hAempty i hi, inter_empty, measure_empty, ENNReal.toReal_zero,
        Finset.sum_const_zero, le_refl]
  have htotal : (∑ i, ∑ j ∈ Finset.univ.filter (fun j => R j i),
      (volume (Y j ∩ Y i)).toReal) ≤ (A.card : ℝ) ^ 2 * B := by
    calc
      _ ≤ ∑ i : Fin n, if i ∈ A then (A.card : ℝ) * B else 0 :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = _ := by
        simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        ring
  have hcard : ({i | (Y i).Nonempty}.ncard : ℝ) = A.card := by
    congr 1
    rw [show {i | (Y i).Nonempty} = (A : Set (Fin n)) by ext i; simp [A], ncard_coe_finset]
  rw [hcard]
  exact (wz_transverse_brush_selection.broad_energy Y Finset.univ R hY hfin hbroad).trans
    (by nlinarith [htotal])

/-- A uniformly occupied broad piece has a quadratic tube-count bound. -/
theorem broad_piece_mass_bound {δ b M : ℝ} (hδ : 0 < δ) (hb : 0 < b) (hb1 : b ≤ 1)
    {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i)) (hfin : ∀ i, volume (Y i) ≠ ⊤)
    (hlower : ∀ p ∈ ⋃ i, Y i, M ≤ incidence Y p)
    (hbroad : ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ)) :
    M * shadingMass Y ≤ 8192 * δ ^ 3 / b * ({i | (Y i).Nonempty}.ncard : ℝ) ^ 2 := by
  let R : Fin n → Fin n → Prop := fun i j => b < min ‖v j - v i‖ ‖v j + v i‖
  have hcounts : ∀ i p, incidence Y p ≤
      2 * wz_transverse_brush_selection.multiplicity Y (Finset.univ.filter (R i)) p := by
    intro i p
    have hnear := hbroad p (v i) (hv i)
    rw [wz_transverse_brush_selection.incidence_ncard] at hnear
    have hfull : ({j | p ∈ Y j}.ncard : ℝ) = incidence Y p :=
      (incidence_eq_ncard Y p).symm
    rw [hfull] at hnear
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => min ‖v j - v i‖ ‖v j + v i‖ ≤ b)
      (fun j => wz_transverse_brush_selection.oneOn (Y j) p)
    simp only [not_le] at hsplit
    change wz_transverse_brush_selection.multiplicity Y
        (Finset.univ.filter fun j => min ‖v j - v i‖ ‖v j + v i‖ ≤ b) p +
      wz_transverse_brush_selection.multiplicity Y (Finset.univ.filter (R i)) p =
        incidence Y p at hsplit
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
  have henergy := broad_occupied_energy Y R hY hfin
    (by positivity : 0 ≤ 4096 * δ ^ 3 / b) hpair hcounts
  have hpoint (p : Space) : M * incidence Y p ≤ incidence Y p ^ 2 := by
    by_cases hp : p ∈ ⋃ i, Y i
    · have hh := hlower p hp
      nlinarith [incidence_nonneg Y p]
    · have hi : incidence Y p = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact wz_transverse_brush_selection.oneOn_of_notMem
          (fun h => hp (mem_iUnion.mpr ⟨i, h⟩))
      rw [hi]
      norm_num
  have hint := integral_mono ((integrable_incidence hY hfin).const_mul M)
    (wz_transverse_brush_selection.integrable_multiplicity_sq Y Finset.univ
      (fun i _ => hY i) (fun i _ => hfin i)) hpoint
  rw [integral_const_mul, wz_transverse_brush_selection.integral_multiplicity Y Finset.univ
    (fun i _ => hY i) (fun i _ => hfin i)] at hint
  change M * shadingMass Y ≤ _ at hint
  exact hint.trans (henergy.trans_eq (by ring))

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
