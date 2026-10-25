-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_brush_selection.Energy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_transverse_brush_selection.Moments

namespace WangZahlLot.Obl.wz_transverse_brush_selection

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

theorem multiplicity_eq_card {ι : Type*} (Y : ι → Set Space) (s : Finset ι) (p : Space) :
    multiplicity Y s p = ((s.filter (fun i => p ∈ Y i)).card : ℝ) := by
  classical
  simp only [multiplicity, oneOn, Set.indicator, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, mul_one]

theorem incidence_ncard {ι : Type*} [Fintype ι] (Y : ι → Set Space) (P : ι → Prop)
    (p : Space) :
    ({i | p ∈ Y i ∧ P i}.ncard : ℝ) =
      multiplicity Y (Finset.univ.filter P) p := by
  classical
  rw [multiplicity_eq_card]
  have heq : {i | p ∈ Y i ∧ P i} =
      ((Finset.univ.filter P).filter (fun i => p ∈ Y i) : Set ι) := by
    ext i
    simp [and_comm]
  rw [heq, Set.ncard_coe_finset]

/-- Pointwise broadness for the original family bounds the second moment of any
subfamily by ordered transverse pairs, with just one index in that subfamily. -/
theorem broad_energy {ι : Type*} [Fintype ι] (Y : ι → Set Space) (D : Finset ι)
    (R : ι → ι → Prop)
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, volume (Y i) ≠ ⊤)
    (hbroad : ∀ j p, multiplicity Y Finset.univ p ≤
      2 * multiplicity Y (Finset.univ.filter (R j)) p) :
    (∫ p, multiplicity Y D p ^ 2) ≤
      2 * ∑ i, ∑ j ∈ D.filter (fun j => R j i), (volume (Y j ∩ Y i)).toReal := by
  classical
  let H : Space → ℝ := fun p =>
    ∑ i, ∑ j ∈ D.filter (fun j => R j i), oneOn (Y j ∩ Y i) p
  have hpair : ∀ i j, Integrable (oneOn (Y j ∩ Y i)) := fun i j =>
    integrable_oneOn ((hY j).inter (hY i))
      (ne_top_of_le_ne_top (hfin j) (measure_mono inter_subset_left))
  have hH : Integrable H :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hpair i j))
  have hpoint : ∀ p, multiplicity Y D p ^ 2 ≤ 2 * H p := by
    intro p
    have hgf := multiplicity_mono Y (Finset.subset_univ D) p
    calc
      multiplicity Y D p ^ 2 ≤ multiplicity Y D p * multiplicity Y Finset.univ p := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hgf (multiplicity_nonneg Y D p)
      _ = ∑ j ∈ D, oneOn (Y j) p * multiplicity Y Finset.univ p := by
        rw [multiplicity, Finset.sum_mul]
      _ ≤ ∑ j ∈ D, oneOn (Y j) p *
          (2 * multiplicity Y (Finset.univ.filter (R j)) p) := by
        exact Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hbroad j p) (oneOn_nonneg _ _))
      _ = 2 * H p := by
        simp only [H, multiplicity, Finset.sum_filter, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hR : R j i
        · simp only [ite_eq_left hR]
          rw [← oneOn_mul]
          ring
        · simp [hR]
  have hint := integral_mono (integrable_multiplicity_sq Y D (fun i _ => hY i)
    (fun i _ => hfin i)) (hH.const_mul 2) hpoint
  rw [integral_const_mul] at hint
  have hHI : (∫ p, H p) =
      ∑ i, ∑ j ∈ D.filter (fun j => R j i), (volume (Y j ∩ Y i)).toReal := by
    dsimp only [H]
    rw [integral_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => hpair i j))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum _ (fun j _ => hpair i j)]
    exact Finset.sum_congr rfl (fun j _ => integral_oneOn ((hY j).inter (hY i)))
  rwa [hHI] at hint

end WangZahlLot.Obl.wz_transverse_brush_selection
