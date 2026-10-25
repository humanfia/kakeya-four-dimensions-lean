import Mathlib

set_option autoImplicit false

/-!
# Polynomial witnesses for trajectory qualification

The auxiliary rational witnesses make a measurable failure set available without
requiring measurability of an uncountable union of real polynomial witnesses.
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory

local instance : Countable (Polynomial ℚ) :=
  Polynomial.toFinsupp_injective.countable

abbrev RowPolynomial := Fin 2 → Polynomial ℝ

/-- The degree and coefficient allowance in the frozen qualification predicate. -/
def Admissible (M : ℕ) (C : ℝ) (P : RowPolynomial) : Prop :=
  ∀ e, (P e).natDegree ≤ M ∧ ∀ a : ℕ, |(P e).coeff a| ≤ C

/-- Times witnessing one fixed row polynomial on the same trajectory and block. -/
def witnessTimes {α : Type*} (E : Set (α × ℝ))
    (f : α × ℝ → Fin 2 → ℝ) (I : Set ℝ) (δ : ℝ) (P : RowPolynomial) : Set (α × ℝ) :=
  {p | p ∈ E ∧ p.2 ∈ I ∧ ∀ e, |f p e - (P e).eval p.2| ≤ δ}

/-- Qualification by a prescribed polynomial; the duration uses ordinary time. -/
def FitsWith {α : Type*} (E : Set (α × ℝ)) (f : α × ℝ → Fin 2 → ℝ)
    (I : Set ℝ) (M : ℕ) (C δ τ : ℝ) (p : α × ℝ) (P : RowPolynomial) : Prop :=
  Admissible M C P ∧ (∀ e, |f p e - (P e).eval p.2| ≤ δ) ∧
    ENNReal.ofReal τ ≤ volume (Prod.mk p.1 ⁻¹' witnessTimes E f I δ P)

def Fits {α : Type*} (E : Set (α × ℝ)) (f : α × ℝ → Fin 2 → ℝ)
    (I : Set ℝ) (M : ℕ) (C δ τ : ℝ) (p : α × ℝ) : Prop :=
  ∃ P : RowPolynomial, FitsWith E f I M C δ τ p P

/-- Countably many candidate polynomials suffice once the discovery has slack. -/
def RationalFits {α : Type*} (E : Set (α × ℝ)) (f : α × ℝ → Fin 2 → ℝ)
    (I : Set ℝ) (M : ℕ) (C δ τ : ℝ) (p : α × ℝ) : Prop :=
  ∃ Q : Fin 2 → Polynomial ℚ,
    FitsWith E f I M C δ τ p (fun e => (Q e).map (algebraMap ℚ ℝ))

theorem RationalFits.fits {α : Type*} {E : Set (α × ℝ)}
    {f : α × ℝ → Fin 2 → ℝ} {I : Set ℝ} {M : ℕ} {C δ τ : ℝ} {p : α × ℝ}
    (h : RationalFits E f I M C δ τ p) : Fits E f I M C δ τ p := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨_, hQ⟩

section Measurability

variable {α : Type*} [MeasurableSpace α]
  {E : Set (α × ℝ)} {f : α × ℝ → Fin 2 → ℝ} {I : Set ℝ}

theorem measurableSet_rowError (hf : Measurable f) (P : RowPolynomial) (δ : ℝ) :
    MeasurableSet {p : α × ℝ | ∀ e, |f p e - (P e).eval p.2| ≤ δ} := by
  have he (e : Fin 2) : MeasurableSet {p : α × ℝ |
      |f p e - (P e).eval p.2| ≤ δ} := measurableSet_le
    (((measurable_pi_apply e).comp hf).sub
      ((P e).continuous.measurable.comp measurable_snd)).abs measurable_const
  simpa only [Set.ofPred_forall] using MeasurableSet.iInter he

theorem measurableSet_witnessTimes (hE : MeasurableSet E) (hf : Measurable f)
    (hI : MeasurableSet I) (P : RowPolynomial) (δ : ℝ) :
    MeasurableSet (witnessTimes E f I δ P) :=
  hE.inter ((measurable_snd hI).inter (measurableSet_rowError hf P δ))

theorem measurableSet_fitsWith (hE : MeasurableSet E) (hf : Measurable f)
    (hI : MeasurableSet I) (M : ℕ) (C δ τ : ℝ) (P : RowPolynomial) :
    MeasurableSet {p | FitsWith E f I M C δ τ p P} := by
  have htime : Measurable (fun p : α × ℝ =>
      volume (Prod.mk p.1 ⁻¹' witnessTimes E f I δ P)) := (measurable_measure_prodMk_left
    (ν := volume) (measurableSet_witnessTimes hE hf hI P δ)).comp measurable_fst
  exact .inter (.const _) ((measurableSet_rowError hf P δ).inter
    (measurableSet_le measurable_const htime))

theorem measurableSet_rationalFits (hE : MeasurableSet E) (hf : Measurable f)
    (hI : MeasurableSet I) (M : ℕ) (C δ τ : ℝ) :
    MeasurableSet {p | RationalFits E f I M C δ τ p} := by
  have hQ := MeasurableSet.iUnion fun Q : Fin 2 → Polynomial ℚ =>
    measurableSet_fitsWith hE hf hI M C δ τ (fun e => (Q e).map (algebraMap ℚ ℝ))
  simpa only [Set.ofPred_exists, RationalFits] using hQ

end Measurability

/-- Enlarging the coefficient and error budgets, or reducing the duration,
preserves a witness and all its original witness times. -/
theorem FitsWith.mono {α : Type*} {E E' : Set (α × ℝ)}
    {f : α × ℝ → Fin 2 → ℝ} {I I' : Set ℝ} {M M' : ℕ}
    {C C' δ δ' τ τ' : ℝ} {p : α × ℝ} {P : RowPolynomial}
    (h : FitsWith E f I M C δ τ p P) (hE : E ⊆ E') (hI : I ⊆ I')
    (hM : M ≤ M') (hC : C ≤ C') (hδ : δ ≤ δ') (hτ : τ' ≤ τ) :
    FitsWith E' f I' M' C' δ' τ' p P := by
  refine ⟨fun e => ⟨(h.1 e).1.trans hM, fun a => ((h.1 e).2 a).trans hC⟩,
    fun e => (h.2.1 e).trans hδ, ?_⟩
  refine (ENNReal.ofReal_le_ofReal hτ).trans (h.2.2.trans (measure_mono ?_))
  intro t ht
  exact ⟨hE ht.1, hI ht.2.1, fun e => (ht.2.2 e).trans hδ⟩

end Submission.Obl.k4_scalar_grid_polynomial_qualification
