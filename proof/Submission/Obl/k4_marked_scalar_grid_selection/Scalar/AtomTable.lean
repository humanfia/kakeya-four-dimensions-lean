/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/AtomTable.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.Atoms

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

local instance atomTablePropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance atomTableDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

abbrev AtomIndex (H J : ℕ) := Fin H × Fin J

noncomputable def markedAtoms {H J : ℕ} (mark : Fin H → Fin J → Bool) : Finset (AtomIndex H J) := by
  classical
  exact Finset.univ.filter (fun a => mark a.1 a.2 = true)

noncomputable def markOf {H J : ℕ} (T : Finset (AtomIndex H J)) : Fin H → Fin J → Bool := by
  classical
  exact fun j z => decide ((j, z) ∈ T)

abbrev cellWeight {H : ℕ} (J : ℕ) (w : Fin H → ℝ) (a : AtomIndex H J) : ℝ :=
  w a.1 / (J : ℝ)

noncomputable def tableMass {ι : Type*} (I : Finset ι) (w : ι → ℝ) : ℝ := ∑ a ∈ I, w a

noncomputable def tableMeasure {ι : Type*} [MeasurableSpace ι]
    (I : Finset ι) (w : ι → ℝ) : Measure ι :=
  ∑ a ∈ I, ENNReal.ofReal (w a) • Measure.dirac a

theorem tableMeasure_univ {ι : Type*} [MeasurableSpace ι]
    (I : Finset ι) (w : ι → ℝ) (hw : ∀ a ∈ I, 0 ≤ w a) :
    tableMeasure I w univ = ENNReal.ofReal (tableMass I w) := by
  simp only [tableMeasure, Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact (ENNReal.ofReal_sum_of_nonneg hw).symm

theorem tableMeasure_restrict_mass {ι : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (I : Finset ι) (w : ι → ℝ) (A : Set ι)
    (hA : MeasurableSet A) (hw : ∀ a ∈ I, 0 ≤ w a) :
    tableMeasure I w A = ENNReal.ofReal (tableMass (I.filter (fun a => a ∈ A)) w) := by
  classical
  simp only [tableMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hA, Set.indicator_apply, Pi.one_apply]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  exact (ENNReal.ofReal_sum_of_nonneg (fun a ha => hw a (Finset.mem_filter.mp ha).1)).symm

theorem markOf_mono {H J : ℕ} {mark : Fin H → Fin J → Bool}
    {T : Finset (AtomIndex H J)} (hT : T ⊆ markedAtoms mark) :
    ∀ j z, markOf T j z = true → mark j z = true := by
  classical
  intro j z hz
  have ha : (j, z) ∈ T := by simpa only [markOf, decide_eq_true_eq] using hz
  exact (Finset.mem_filter.mp (hT ha)).2

theorem law_mass_markOf {H J : ℕ} {σ : ℝ} (hσ : 0 < σ) (hJ : 0 < J)
    (b : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (T : Finset (AtomIndex H J)) :
    law σ H J b w (markOf T) univ = ENNReal.ofReal (tableMass T (cellWeight J w)) := by
  classical
  rw [law_mass hσ hJ]
  rw [← Fintype.sum_prod_type (f := fun a : AtomIndex H J =>
    if markOf T a.1 a.2 = true then ENNReal.ofReal (w a.1) * ENNReal.ofReal ((J : ℝ)⁻¹) else 0)]
  simp only [Finset.univ_product_univ, markOf, decide_eq_true_eq]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter (fun a : AtomIndex H J => a ∈ T)) = T := by ext; simp
  rw [hfilter]
  rw [tableMass, ENNReal.ofReal_sum_of_nonneg (fun a _ => div_nonneg (hw a.1) (Nat.cast_nonneg J))]
  apply Finset.sum_congr rfl
  intro a _
  simp only [cellWeight, div_eq_mul_inv, ENNReal.ofReal_mul (hw a.1)]

theorem law_eq_selected_atoms {H J : ℕ} {σ : ℝ} (hσ : 0 < σ) (hJ : 0 < J)
    (b : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (T : Finset (AtomIndex H J)) :
    law σ H J b w (markOf T) = ∑ a ∈ T,
      ENNReal.ofReal (w a.1) • atom σ J b a.1 a.2 := by
  classical
  rw [law_eq_atoms hσ hJ]
  rw [← Fintype.sum_prod_type (f := fun a : AtomIndex H J =>
    if markOf T a.1 a.2 = true then ENNReal.ofReal (w a.1) • atom σ J b a.1 a.2 else 0)]
  simp only [Finset.univ_product_univ, markOf, decide_eq_true_eq]
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp

/-- Pruning the atoms lighter than `δ` costs at most their number times `δ`. -/
theorem tableMass_prune {ι : Type*} (I : Finset ι) (w : ι → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    tableMass I w ≤ tableMass (I.filter (fun a => δ ≤ w a)) w + (I.card : ℝ) * δ := by
  classical
  calc
    _ ≤ ∑ a ∈ I, ((if δ ≤ w a then w a else 0) + δ) := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs with h
      · linarith
      · simpa only [zero_add] using (not_le.mp h).le
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_filter]; simp [tableMass]

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
