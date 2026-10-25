import Submission.Obl.k4_dyadic_crop_worlds.Definitions

namespace Submission.Obl.k4_dyadic_crop_worlds

open MeasureTheory Set
noncomputable section

lemma side_pos (N u : ℝ) : 0 < side N u := zpow_pos (by norm_num) _

lemma uncrop_cropCoeff {a : ℝ} (ha : a ≠ 0) (q : Label) (x : Coeff) :
    uncropCoeff a q (cropCoeff a q x) = x := by
  ext i
  fin_cases i <;> simp [cropCoeff, uncropCoeff, ha] <;> field_simp

lemma crop_uncropCoeff {a : ℝ} (ha : a ≠ 0) (q : Label) (x : Coeff) :
    cropCoeff a q (uncropCoeff a q x) = x := by
  ext i
  fin_cases i <;> simp [cropCoeff, uncropCoeff, ha] <;> field_simp

def coeffHomeomorph {a : ℝ} (ha : a ≠ 0) (q : Label) : Coeff ≃ₜ Coeff where
  toFun := cropCoeff a q
  invFun := uncropCoeff a q
  left_inv := uncrop_cropCoeff ha q
  right_inv := crop_uncropCoeff ha q
  continuous_toFun := by unfold cropCoeff; fun_prop
  continuous_invFun := by unfold uncropCoeff; fun_prop

def lineHomeomorph {a : ℝ} (ha : a ≠ 0) (q : Label) : Line ≃ₜ Line :=
  Homeomorph.prodCongr (Homeomorph.refl ℕ) (coeffHomeomorph ha q)

def pointHomeomorph {a : ℝ} (ha : a ≠ 0) (q : Label) : Incident ≃ₜ Incident :=
  Homeomorph.prodCongr (lineHomeomorph ha q) (Homeomorph.refl ℝ)

lemma continuous_cropLine (a : ℝ) (q : Label) : Continuous (cropLine a q) := by
  unfold cropLine cropCoeff
  fun_prop

lemma continuous_cropPoint (a : ℝ) (q : Label) : Continuous (cropPoint a q) := by
  unfold cropPoint cropLine cropCoeff
  fun_prop

lemma measurable_cell (a : ℝ) (q : Label) : MeasurableSet (cell a q) := by
  unfold cell
  measurability

lemma cropLine_injective {a : ℝ} (ha : a ≠ 0) (q : Label) :
    Function.Injective (cropLine a q) := (lineHomeomorph ha q).injective

lemma cropPoint_injective {a : ℝ} (ha : a ≠ 0) (q : Label) :
    Function.Injective (cropPoint a q) := (pointHomeomorph ha q).injective

lemma measurable_cropEvent {a : ℝ} (ha : a ≠ 0) (q : Label)
    {E : Set Incident} (hE : MeasurableSet E) : MeasurableSet (cropEvent E a q) := by
  exact (pointHomeomorph ha q).toMeasurableEquiv.measurableSet_image.2
    (hE.inter ((measurable_cell a q).prod MeasurableSet.univ))

lemma cropEvent_time {E : Set Incident} (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (a : ℝ) (q : Label) : cropEvent E a q ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨mem_univ _, (hE hz.1).2⟩

def planarCoord : Fin 4 → Fin 6 := ![0, 1, 3, 4]

lemma mem_cell_iff (a : ℝ) (q : Label) (l : Line) :
    l ∈ cell a q ↔ ∀ j, ⌊l.2 (planarCoord j) / a⌋ = q j := by
  simp only [cell, mem_setOf_eq]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ j
    fin_cases j <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩

lemma cropCoeff_planar (a : ℝ) (q : Label) (x : Coeff) (j : Fin 4) :
    cropCoeff a q x (planarCoord j) = x (planarCoord j) / a - (q j : ℝ) := by
  fin_cases j <;> rfl

lemma cropCoeff_planar_mem {a : ℝ} {q : Label} {l : Line} (hl : l ∈ cell a q)
    (j : Fin 4) : cropCoeff a q l.2 (planarCoord j) ∈ Ico (0 : ℝ) 1 := by
  rw [cropCoeff_planar]
  have h := Int.floor_eq_iff.mp ((mem_cell_iff a q l).mp hl j)
  constructor <;> linarith [h.1, h.2]

lemma cropCoeff_hidden (a : ℝ) (q : Label) (x : Coeff) :
    cropCoeff a q x 2 = x 2 ∧ cropCoeff a q x 5 = x 5 := ⟨rfl, rfl⟩

lemma cropCoeff_bound {a R : ℝ} {q : Label} {l : Line} (hR : 1 ≤ R)
    (hl : l ∈ cell a q) (hx : ∀ i, |l.2 i| ≤ R) :
    ∀ i, |cropCoeff a q l.2 i| ≤ R := by
  have h (j : Fin 4) : |cropCoeff a q l.2 (planarCoord j)| ≤ R := by
    have hm := cropCoeff_planar_mem hl j
    rw [abs_of_nonneg hm.1]
    exact hm.2.le.trans hR
  intro i
  fin_cases i
  · exact h 0
  · exact h 1
  · exact hx 2
  · exact h 2
  · exact h 3
  · exact hx 5

lemma cropEvent_bound {a R : ℝ} {q : Label} {E : Set Incident} (hR : 1 ≤ R)
    (hE : ∀ z ∈ E, (z.1.1 : ℝ) ≤ R ∧ ∀ i, |z.1.2 i| ≤ R) :
    ∀ z ∈ cropEvent E a q, (z.1.1 : ℝ) ≤ R ∧ ∀ i, |z.1.2 i| ≤ R := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨(hE z hz.1).1, cropCoeff_bound hR hz.2.1 (hE z hz.1).2⟩

end
end Submission.Obl.k4_dyadic_crop_worlds
