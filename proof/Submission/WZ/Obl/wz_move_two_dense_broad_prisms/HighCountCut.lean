-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.HighCountCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_broad_grains_initialization.PointwiseRefinement

/-! A common high-multiplicity cut preserves both incidence mass and density. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory
open scoped ENNReal
open wz_clustered_cover_volume_gain (bodyCount body_mass_le_mul_of_count)
open wz_broad_grains_initialization (measurable_body_count body_count_cut)

/-- An incidence density proportional to the maximum number of active tubes
produces a common cut with a comparable pointwise multiplicity and physical
union density. -/
theorem high_count_common_cut {n : ℕ} {D N : ℝ} {E : Set V}
    (hD : 0 < D) (hN : 0 < N) (hEm : MeasurableSet E) (hEfin : volume E ≠ ∞)
    (Y : Fin n → Set V) (hYm : ∀ i, MeasurableSet (Y i))
    (hYE : ∀ i, Y i ⊆ E) (hcount : ∀ p, bodyCount Y p ≤ N)
    (hmass : O (D*N)*volume E ≤ ∑ i, volume (Y i)) :
    ∃ C : Set V, MeasurableSet C ∧
      ((1/2 : ENNReal)*(∑ i, volume (Y i)) ≤ ∑ i, volume (Y i ∩ C)) ∧
      O (D/2)*volume E ≤ volume (⋃ i, Y i ∩ C) ∧
      ∀ p ∈ ⋃ i, Y i ∩ C, D*N/2 ≤ bodyCount (fun i => Y i ∩ C) p := by
  classical
  let C := {p | D*N/2 ≤ bodyCount Y p}
  have hCm : MeasurableSet C := measurableSet_le measurable_const (measurable_body_count hYm)
  let Q := fun i => Y i ∩ C
  let R := fun i => Y i ∩ Cᶜ
  have hQm (i) : MeasurableSet (Q i) := (hYm i).inter hCm
  have hRm (i) : MeasurableSet (R i) := (hYm i).inter hCm.compl
  have hQfin (i) : volume (Q i) ≠ ∞ := measure_ne_top_of_subset
    (inter_subset_left.trans (hYE i)) hEfin
  have hRfin (i) : volume (R i) ≠ ∞ := measure_ne_top_of_subset
    (inter_subset_left.trans (hYE i)) hEfin
  have hYfin (i) : volume (Y i) ≠ ∞ := measure_ne_top_of_subset (hYE i) hEfin
  have hUfin : volume (⋃ i, Q i) ≠ ∞ := measure_ne_top_of_subset
    (iUnion_subset (fun i => inter_subset_left.trans (hYE i))) hEfin
  have hlow : (∑ i, volume (R i)) ≤ O (D*N/2)*volume E := by
    have hb (p : V) : bodyCount R p ≤ (D*N/2)*bodyCount (fun _ : Fin 1 => E) p := by
      by_cases hp : p ∈ E
      · have hEcount : bodyCount (fun _ : Fin 1 => E) p = 1 := by simp [bodyCount, hp]
        rw [hEcount, mul_one]
        change bodyCount (fun i => Y i ∩ Cᶜ) p ≤ _
        rw [body_count_cut]
        by_cases hc : p ∈ C
        · simp only [mem_compl_iff, hc, not_true_eq_false, ite_false]
          positivity
        · simpa only [mem_compl_iff, hc, not_false_eq_true, ite_true] using
            (le_of_not_ge hc : bodyCount Y p ≤ D*N/2)
      · have he : {i | p ∈ R i} = ∅ := Set.eq_empty_iff_forall_notMem.mpr
          (fun i hi => hp (hYE i hi.1))
        simp only [bodyCount, he, Set.ncard_empty, Nat.cast_zero]
        positivity
    simpa only [Fin.sum_univ_one] using body_mass_le_mul_of_count hRm
      (fun _ : Fin 1 => hEm) (by positivity : 0 ≤ D*N/2) hb
  have hupper : (∑ i, volume (Q i)) ≤ O N*volume (⋃ i, Q i) := by
    have hb (p : V) : bodyCount Q p ≤ N*bodyCount (fun _ : Fin 1 => ⋃ i, Q i) p := by
      by_cases hp : p ∈ ⋃ i, Q i
      · have hUcount : bodyCount (fun _ : Fin 1 => ⋃ i, Q i) p = 1 := by simp [bodyCount, hp]
        rw [hUcount, mul_one]
        apply le_trans _ (hcount p)
        change (Set.ncard _ : ℝ) ≤ (Set.ncard _ : ℝ)
        exact_mod_cast Set.ncard_le_ncard (show {i | p ∈ Q i} ⊆ {i | p ∈ Y i} from
          fun i hi => hi.1) (Set.toFinite _)
      · have he : {i | p ∈ Q i} = ∅ := Set.eq_empty_iff_forall_notMem.mpr
          (fun i hi => hp (mem_iUnion.mpr ⟨i, hi⟩))
        simp only [bodyCount, he, Set.ncard_empty, Nat.cast_zero]
        positivity
    simpa only [Fin.sum_univ_one] using body_mass_le_mul_of_count hQm
      (fun _ : Fin 1 => MeasurableSet.iUnion hQm) hN.le hb
  have hsum : (∑ i, volume.real (Y i)) =
      (∑ i, volume.real (Q i)) + ∑ i, volume.real (R i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hh : volume (Q i)+volume (R i) = volume (Y i) := by
      simpa only [Q, R, ← sdiff_eq] using measure_inter_add_sdiff (Y i) hCm
    have hreal := congrArg ENNReal.toReal hh
    rw [ENNReal.toReal_add (hQfin i) (hRfin i)] at hreal
    exact hreal.symm
  have hlow' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin) hlow
  have hupper' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUfin) hupper
  have hmass' := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hYfin i)) hmass
  simp only [ENNReal.toReal_sum (fun i _ => hRfin i), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ D*N/2)] at hlow'
  simp only [ENNReal.toReal_sum (fun i _ => hQfin i), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hN.le] at hupper'
  simp only [ENNReal.toReal_sum (fun i _ => hYfin i), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ D*N)] at hmass'
  change (∑ i, volume.real (R i)) ≤ D*N/2*volume.real E at hlow'
  change (∑ i, volume.real (Q i)) ≤ N*volume.real (⋃ i, Q i) at hupper'
  change D*N*volume.real E ≤ ∑ i, volume.real (Y i) at hmass'
  refine ⟨C, hCm, ?_, ?_, ?_⟩
  · apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.sum_ne_top.mpr (fun i _ => hYfin i)))
      (ENNReal.sum_ne_top.mpr (fun i _ => hQfin i))).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, ENNReal.toReal_sum (fun i _ => hYfin i),
      ENNReal.toReal_sum (fun i _ => hQfin i)]
    change (1/2 : ℝ)*(∑ i, volume.real (Y i)) ≤ ∑ i, volume.real (Q i)
    nlinarith
  · apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin) hUfin).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ D/2)]
    change D/2*volume.real E ≤ volume.real (⋃ i, Q i)
    nlinarith
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    rw [body_count_cut, if_pos hi.2]
    exact hi.2

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
