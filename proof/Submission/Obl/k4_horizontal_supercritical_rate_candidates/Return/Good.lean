import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.CrossD

/-!
# Good points of a sample

`G0`: native bounds, non-dyadic times at the three depths, coverage by labels at the three
depths and by slices. It carries the whole of `ρs`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Time not a dyadic point of level `T`. -/
def NonDyadic (T : ℕ) (p : α × ℝ) : Prop := ∀ k : ℕ, p.2 ≠ (k : ℝ) / 2 ^ T

/-- Covered by a label of the family. -/
def Covered (f : Fam α) (p : α × ℝ) : Prop := ∃ j, p.1 ∈ f.B j ∧ p.2 ∈ f.I j

namespace CoreData

variable (D : CoreData α)

/-- Good points. -/
def G0 : Set (α × ℝ) :=
  {p | NativeOK D p ∧ NonDyadic D.f₀.T p ∧ NonDyadic D.fc.T p ∧ NonDyadic D.fe.T p ∧
    Covered D.f₀ p ∧ Covered D.fc p ∧ Covered D.fe p ∧ ∃ i, p.1 ∈ D.Ly.C i}

end CoreData

theorem measurableSet_nativeOK (D : CoreData α) (hb : Measurable D.b) :
    MeasurableSet {p : α × ℝ | NativeOK D p} := by
  have hc : ∀ e : Fin 6, Measurable (fun p : α × ℝ => D.b p.1 e) :=
    fun e => (measurable_pi_apply e).comp (hb.comp measurable_fst)
  have h1 : MeasurableSet {p : α × ℝ | p.2 ∈ Icc (0 : ℝ) 1} := measurable_snd measurableSet_Icc
  have h2 : MeasurableSet {p : α × ℝ | ∀ e, |D.b p.1 e| ≤ 2 * D.K} := by
    rw [setOf_forall]
    exact MeasurableSet.iInter (fun e => measurableSet_le (hc e).abs measurable_const)
  have h3 : MeasurableSet {p : α × ℝ |
      |D.b p.1 0| + |D.b p.1 1| + |D.b p.1 3| + |D.b p.1 4| ≤ D.K} :=
    measurableSet_le ((((hc 0).abs.add (hc 1).abs).add (hc 3).abs).add (hc 4).abs)
      measurable_const
  exact h1.inter (h2.inter h3)

theorem measurableSet_nonDyadic (T : ℕ) : MeasurableSet {p : α × ℝ | NonDyadic T p} := by
  unfold NonDyadic
  rw [setOf_forall]
  exact MeasurableSet.iInter (fun k => measurable_snd (measurableSet_singleton _).compl)

theorem measurableSet_covered (f : Fam α) (hB : ∀ j, MeasurableSet (f.B j)) :
    MeasurableSet {p : α × ℝ | Covered f p} := by
  unfold Covered
  rw [setOf_exists]
  refine MeasurableSet.iUnion (fun j => ?_)
  have hI : MeasurableSet (f.I j) := by unfold Fam.I blk; exact measurableSet_Icc
  exact (hB j).prod hI

theorem measurableSet_G0 (D : CoreData α) (H : CoreHyp D) : MeasurableSet D.G0 := by
  have hsl : MeasurableSet {p : α × ℝ | ∃ i, p.1 ∈ D.Ly.C i} := by
    rw [setOf_exists]
    exact MeasurableSet.iUnion (fun i => measurable_fst (H.lygood.meas i))
  exact (measurableSet_nativeOK D H.bmeas).inter ((measurableSet_nonDyadic _).inter
    ((measurableSet_nonDyadic _).inter ((measurableSet_nonDyadic _).inter
    ((measurableSet_covered _ H.f₀good.measB).inter ((measurableSet_covered _ H.fcgood.measB).inter
    ((measurableSet_covered _ H.fegood.measB).inter hsl))))))

/-- A property of lines holding `ν`-a.e. holds `μ`-a.e. on incidences. -/
theorem ae_line_of_dom (ν : Measure α) (μ : Measure (α × ℝ)) (C : ℝ≥0∞)
    (hdom : μ ≤ C • ν.prod volume) {P : α → Prop} (hP : ∀ᵐ l ∂ν, P l) :
    ∀ᵐ p ∂μ, P p.1 := by
  have hnull : (ν.prod volume) {p : α × ℝ | ¬ P p.1} = 0 := by
    have heq : {p : α × ℝ | ¬ P p.1} = ({l | ¬ P l} ×ˢ (univ : Set ℝ)) := by
      ext p; simp only [mem_ofPred_eq, mem_prod, mem_univ, and_true]
    rw [heq, Measure.prod_prod, ae_iff.mp hP, zero_mul]
  rw [ae_iff]
  refine le_antisymm ((hdom _).trans ?_) zero_le
  rw [Measure.smul_apply, hnull, smul_zero]

theorem ae_nativeOK (D : CoreData α) (H : CoreHyp D) : ∀ᵐ p ∂D.μ, NativeOK D p := by
  have ht : ∀ᵐ p ∂D.μ, p.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) H.μsupp
    exact fun h => hp h.2
  have hs := ae_line_of_dom D.ν D.μ (ENNReal.ofReal D.K) H.μdom H.bbd
  filter_upwards [ht, hs, H.x3bd] with p h1 h3 h4
  refine ⟨h1, fun e => ?_, h3⟩
  have hK0 : 0 ≤ D.K := le_trans (by positivity) h3
  have h2 : |D.b p.1 2| ≤ D.K := by simpa [x3] using h4 0 (by norm_num)
  have h25 : |D.b p.1 2 + D.b p.1 5| ≤ D.K := by simpa [x3] using h4 1 (by norm_num)
  have h5 : |D.b p.1 5| ≤ 2 * D.K := by
    have := abs_sub (D.b p.1 2 + D.b p.1 5) (D.b p.1 2)
    simp only [add_sub_cancel_left] at this
    linarith
  have a0 := abs_nonneg (D.b p.1 0); have a1 := abs_nonneg (D.b p.1 1)
  have a3 := abs_nonneg (D.b p.1 3); have a4 := abs_nonneg (D.b p.1 4)
  fin_cases e <;> simp <;> linarith

theorem ae_G0 (D : CoreData α) (H : CoreHyp D) : ∀ᵐ p ∂D.ρs, p ∈ D.G0 := by
  haveI := H.νprob
  have hac : D.ρs ≪ D.μ := Measure.absolutelyContinuous_of_le (H.ρsρ.trans H.ρμ)
  have hμ : ∀ᵐ p ∂D.μ, NativeOK D p ∧ NonDyadic D.f₀.T p ∧ NonDyadic D.fc.T p ∧
      NonDyadic D.fe.T p ∧ Covered D.f₀ p ∧ Covered D.fc p ∧ Covered D.fe p := by
    filter_upwards [ae_nativeOK D H, ae_not_dyadic D.ν D.μ _ H.μdom D.f₀.T,
      ae_not_dyadic D.ν D.μ _ H.μdom D.fc.T, ae_not_dyadic D.ν D.μ _ H.μdom D.fe.T,
      H.f₀good.cover, H.fcgood.cover, H.fegood.cover] with p h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  filter_upwards [hac.ae_le hμ, H.ρscov] with p h1 h2
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2, h2⟩

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
