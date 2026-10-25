-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_brush_selection.Moments.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_transverse_brush_selection

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable def oneOn (A : Set Space) : Space → ℝ := A.indicator (fun _ => 1)

theorem oneOn_of_mem {A : Set Space} {p : Space} (hp : p ∈ A) : oneOn A p = 1 :=
  indicator_of_mem hp _

theorem oneOn_of_notMem {A : Set Space} {p : Space} (hp : p ∉ A) : oneOn A p = 0 :=
  indicator_of_notMem hp _

theorem oneOn_nonneg (A : Set Space) (p : Space) : 0 ≤ oneOn A p := by
  classical
  by_cases hp : p ∈ A <;> simp [oneOn, hp]

theorem oneOn_mul (A B : Set Space) (p : Space) :
    oneOn A p * oneOn B p = oneOn (A ∩ B) p := by
  classical
  by_cases hA : p ∈ A <;> by_cases hB : p ∈ B <;> simp [oneOn, hA, hB]

theorem integrable_oneOn {A : Set Space} (hA : MeasurableSet A) (hfin : volume A ≠ ⊤) :
    Integrable (oneOn A) := (integrable_indicator_iff hA).2 (integrableOn_const hfin)

theorem integral_oneOn {A : Set Space} (hA : MeasurableSet A) :
    ∫ p, oneOn A p = (volume A).toReal := by
  simpa [oneOn, measureReal_def] using
    (integral_indicator_const (μ := volume) (1 : ℝ) hA)

noncomputable def multiplicity {ι : Type*} (Y : ι → Set Space) (s : Finset ι) (p : Space) : ℝ :=
  ∑ i ∈ s, oneOn (Y i) p

theorem multiplicity_nonneg {ι : Type*} (Y : ι → Set Space) (s : Finset ι) (p : Space) :
    0 ≤ multiplicity Y s p := Finset.sum_nonneg (fun _ _ => oneOn_nonneg _ _)

theorem multiplicity_mono {ι : Type*} (Y : ι → Set Space) {s t : Finset ι} (hst : s ⊆ t)
    (p : Space) : multiplicity Y s p ≤ multiplicity Y t p :=
  Finset.sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ => oneOn_nonneg _ _)

theorem integrable_multiplicity {ι : Type*} (Y : ι → Set Space) (s : Finset ι)
    (hY : ∀ i ∈ s, MeasurableSet (Y i)) (hfin : ∀ i ∈ s, volume (Y i) ≠ ⊤) :
    Integrable (multiplicity Y s) :=
  integrable_finsetSum _ (fun i hi => integrable_oneOn (hY i hi) (hfin i hi))

theorem integral_multiplicity {ι : Type*} (Y : ι → Set Space) (s : Finset ι)
    (hY : ∀ i ∈ s, MeasurableSet (Y i)) (hfin : ∀ i ∈ s, volume (Y i) ≠ ⊤) :
    ∫ p, multiplicity Y s p = ∑ i ∈ s, (volume (Y i)).toReal := by
  change (∫ p, ∑ i ∈ s, oneOn (Y i) p) = _
  rw [integral_finsetSum s
    (fun i hi => integrable_oneOn (hY i hi) (hfin i hi))]
  exact Finset.sum_congr rfl (fun i hi => integral_oneOn (hY i hi))

theorem integrable_multiplicity_sq {ι : Type*} (Y : ι → Set Space) (s : Finset ι)
    (hY : ∀ i ∈ s, MeasurableSet (Y i)) (hfin : ∀ i ∈ s, volume (Y i) ≠ ⊤) :
    Integrable (fun p => multiplicity Y s p ^ 2) := by
  have heq : (fun p => multiplicity Y s p ^ 2) =
      (fun p => ∑ i ∈ s, ∑ j ∈ s, oneOn (Y i ∩ Y j) p) := by
    funext p
    simp only [multiplicity, pow_two, Finset.sum_mul, Finset.mul_sum, oneOn_mul]
    rw [Finset.sum_comm]
  rw [heq]
  exact integrable_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj =>
    integrable_oneOn ((hY i hi).inter (hY j hj))
      (ne_top_of_le_ne_top (hfin i hi) (measure_mono inter_subset_left))))

/-- Cauchy--Schwarz for an integrable function supported in a set of positive finite measure. -/
theorem integral_sq_bound {g : Space → ℝ} {E : Set Space}
    (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) (hq : 0 < (volume E).toReal)
    (hg : Integrable g) (hgg : Integrable (fun p => g p ^ 2))
    (hsupp : ∀ p, p ∉ E → g p = 0) :
    (∫ p, g p) ^ 2 ≤ (volume E).toReal * ∫ p, g p ^ 2 := by
  let q := (volume E).toReal
  let M := ∫ p, g p
  let t := M / q
  have hpoint : (fun p => 2 * t * g p) ≤
      (fun p => g p ^ 2 + t ^ 2 * oneOn E p) := by
    intro p
    dsimp only
    by_cases hp : p ∈ E
    · rw [oneOn_of_mem hp]
      nlinarith [sq_nonneg (g p - t)]
    · simp [hsupp p hp, oneOn_of_notMem hp]
  have hint := integral_mono (hg.const_mul (2 * t))
    (hgg.add ((integrable_oneOn hE hfin).const_mul (t ^ 2))) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add hgg ((integrable_oneOn hE hfin).const_mul (t ^ 2)),
    integral_const_mul, integral_const_mul, integral_oneOn hE] at hint
  change 2 * t * M ≤ (∫ p, g p ^ 2) + t ^ 2 * q at hint
  have hq0 : q ≠ 0 := ne_of_gt hq
  have e1 : (2 * t * M) * q = 2 * M ^ 2 := by dsimp [t]; field_simp
  have e2 : (t ^ 2 * q) * q = M ^ 2 := by dsimp [t]; field_simp
  have hi := mul_le_mul_of_nonneg_right hint hq.le
  rw [add_mul, e1, e2] at hi
  change M ^ 2 ≤ q * _
  nlinarith

end WangZahlLot.Obl.wz_transverse_brush_selection
