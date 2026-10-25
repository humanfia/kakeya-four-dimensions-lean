/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/InterceptAssignments.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: o062/x0511,49634d4, InterceptAssignments.lean.
The adapted generic prerequisite proofs retain their credits in Interpolation, ScalarResidual and Format.
-/

import Submission.Lib.K4ScalarCoreTools.Finalization.Interpolation
import Submission.Lib.K4ScalarCoreTools.Finalization.ScalarResidual
import Submission.Lib.K4ScalarCoreTools.Finalization.Format

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

/-- The midpoint of the physical intercept bin. -/
def interceptCenter (scale : ℝ) (C : ℤ) : ℝ := scale * ((C : ℝ) + 1 / 2)

/-- A midpoint bin differs from its center by at most half its width. -/
theorem interceptCenter_sub_bound {r scale : ℝ} (hscale : 0 < scale) (C : ℤ)
    (hlabel : ⌊r / scale⌋ = C) : |interceptCenter scale C - r| ≤ scale / 2 := by
  obtain ⟨hl, hu⟩ := Int.floor_eq_iff.mp hlabel
  have hl' := (le_div_iff₀ hscale).mp hl
  have hu' := (div_lt_iff₀ hscale).mp hu
  dsimp [interceptCenter]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem interceptCenter_bound {r scale R : ℝ} (hscale : 0 < scale) (C : ℤ)
    (hlabel : ⌊r / scale⌋ = C) (hr : |r| ≤ R) :
    |interceptCenter scale C| ≤ R + scale / 2 := by
  calc
    |interceptCenter scale C| = |r + (interceptCenter scale C - r)| := by ring_nf
    _ ≤ |r| + |interceptCenter scale C - r| := abs_add_le _ _
    _ ≤ R + scale / 2 := add_le_add hr (interceptCenter_sub_bound hscale C hlabel)

/-- Adding the intercept changes no nonconstant coefficient. -/
def interceptPredictor (Q : MvPolynomial (Fin 2) ℝ) (scale : ℝ) (C : ℤ) :
    MvPolynomial (Fin 2) ℝ := Q + MvPolynomial.C (interceptCenter scale C)

theorem interceptPredictor_degree (Q : MvPolynomial (Fin 2) ℝ)
    (hQ : Q.totalDegree ≤ 2) (scale : ℝ) (C : ℤ) :
    (interceptPredictor Q scale C).totalDegree ≤ 2 := by
  exact (totalDegree_add _ _).trans (by simpa [interceptPredictor] using hQ)

/-- The three fixed sample times in a block. -/
def interceptSample (a h : ℝ) (j : Fin 3) : ℝ := a + (j : ℝ) * h / 2

/-- Final assignments depend only on the original coefficient vector. -/
def interceptAssignment (U : Set (Fin 5 → ℝ)) (Q : MvPolynomial (Fin 2) ℝ)
    (a h scale E : ℝ) (C : ℤ) : Set (Fin 5 → ℝ) :=
  U ∩ {b | ⌊eval b (scalarErrorPolynomial Q (a + h / 2)) / scale⌋ = C ∧
    ∀ j : Fin 3, |eval b (scalarErrorPolynomial Q (interceptSample a h j)) -
      interceptCenter scale C| ≤ E}

theorem interceptAssignment_disjoint (U : Set (Fin 5 → ℝ))
    (Q : MvPolynomial (Fin 2) ℝ) (a h scale E : ℝ) :
    Pairwise (fun C C' : ℤ => Disjoint (interceptAssignment U Q a h scale E C)
      (interceptAssignment U Q a h scale E C')) := by
  intro C C' hCC'
  apply Set.disjoint_left.mpr
  intro b hb hb'
  exact hCC' (hb.2.1.symm.trans hb'.2.1)

theorem measurableSet_interceptAssignment (U : Set (Fin 5 → ℝ))
    (hU : MeasurableSet U) (Q : MvPolynomial (Fin 2) ℝ)
    (a h scale E : ℝ) (C : ℤ) : MeasurableSet (interceptAssignment U Q a h scale E C) := by
  apply hU.inter
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      (((scalarErrorPolynomial Q (a + h / 2)).continuous_eval.measurable.div_const scale).floor)
      measurable_const
  · change MeasurableSet {b : Fin 5 → ℝ | ∀ j : Fin 3,
        |eval b (scalarErrorPolynomial Q (interceptSample a h j)) -
          interceptCenter scale C| ≤ E}
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le
      (((scalarErrorPolynomial Q (interceptSample a h j)).continuous_eval.measurable.sub_const
        (interceptCenter scale C)).abs) measurable_const

/-- Interpolation within the same block costs a numerical constant only. -/
theorem quadratic_bound_on_block (f : ℝ → ℝ) (hf : Quadratic f)
    {a h E : ℝ} (hh : 0 < h)
    (h₀ : |f a| ≤ E) (h₁ : |f (a + h / 2)| ≤ E) (h₂ : |f (a + h)| ≤ E)
    {t : ℝ} (ht : t ∈ Icc a (a + h)) : |f t| ≤ 8 * E := by
  obtain ⟨A, B, C, hf⟩ := hf
  have hg : Quadratic (fun s => f (a + h * s)) := by
    refine ⟨A * h ^ 2, (2 * A * a + B) * h, A * a ^ 2 + B * a + C, fun s => ?_⟩
    dsimp only
    rw [hf]
    ring
  have hs : (t - a) / h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hh.le
    · apply (div_le_iff₀ hh).mpr
      linarith [ht.2]
  have hb := quadratic_extrapolate (fun s => f (a + h * s)) hg
    (a := 0) (q := 1) (E := E) (by norm_num) (by norm_num) (by norm_num)
    (by simpa using h₀) (by simpa [div_eq_mul_inv] using h₁)
    (by simpa using h₂) hs
  have heq : a + h * ((t - a) / h) = t := by field_simp; ring
  simpa [heq] using hb

/-- Every assigned trajectory fits its actual shifted quadratic for the whole block. -/
theorem interceptAssignment_fit (U : Set (Fin 5 → ℝ)) (Q : MvPolynomial (Fin 2) ℝ)
    (hQ : Q.totalDegree ≤ 2) {a h scale E : ℝ} (hh : 0 < h) (C : ℤ)
    {b : Fin 5 → ℝ} (hb : b ∈ interceptAssignment U Q a h scale E C)
    {t : ℝ} (ht : t ∈ Icc a (a + h)) :
    |scalarX b t - eval ![t, scalarY b t] (interceptPredictor Q scale C)| ≤ 8 * E := by
  have hf := quadratic_scalar_residual (interceptPredictor Q scale C)
    (interceptPredictor_degree Q hQ scale C) (b 0) (b 1) (b 2) (b 3) (b 4)
  change Quadratic (fun t => scalarX b t -
    eval ![t, scalarY b t] (interceptPredictor Q scale C)) at hf
  apply quadratic_bound_on_block _ hf hh _ _ _ ht
  all_goals
    first
    | simpa [interceptSample, eval_scalarErrorPolynomial, interceptPredictor, sub_add_eq_sub_sub]
        using hb.2.2 (0 : Fin 3)
    | simpa [interceptSample, eval_scalarErrorPolynomial, interceptPredictor, sub_add_eq_sub_sub]
        using hb.2.2 (1 : Fin 3)
    | simpa [interceptSample, eval_scalarErrorPolynomial, interceptPredictor, sub_add_eq_sub_sub]
        using hb.2.2 (2 : Fin 3)

/-- A full geometric fit with the same midpoint label is always assigned. -/
theorem mem_interceptAssignment_of_block_fit (U : Set (Fin 5 → ℝ))
    (Q : MvPolynomial (Fin 2) ℝ) {a h scale E : ℝ} (hh : 0 ≤ h) (C : ℤ)
    {b : Fin 5 → ℝ} (hb : b ∈ U)
    (hlabel : ⌊eval b (scalarErrorPolynomial Q (a + h / 2)) / scale⌋ = C)
    (hfit : ∀ t ∈ Icc a (a + h),
      |scalarX b t - eval ![t, scalarY b t] (interceptPredictor Q scale C)| ≤ E) :
    b ∈ interceptAssignment U Q a h scale E C := by
  refine ⟨hb, hlabel, fun j => ?_⟩
  have hj : 0 ≤ (j : ℝ) ∧ (j : ℝ) ≤ 2 := by
    constructor
    · positivity
    · exact_mod_cast (show j.val ≤ 2 by omega)
  have hs : interceptSample a h j ∈ Icc a (a + h) := by
    dsimp [interceptSample]
    constructor
    · nlinarith [mul_nonneg hj.1 hh]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hj.2) hh]
  simpa [eval_scalarErrorPolynomial, interceptPredictor, sub_add_eq_sub_sub] using hfit _ hs

/-- Any original-law floor on discovery fits is a floor for the final assignment. -/
theorem interceptAssignment_original_mass {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → Fin 5 → ℝ)
    (U : Set (Fin 5 → ℝ)) (Q : MvPolynomial (Fin 2) ℝ)
    {a h scale E : ℝ} (hh : 0 ≤ h) (C : ℤ) (S : Set (α × ℝ))
    (hS : ∀ p ∈ S, b p.1 ∈ U ∧
      ⌊eval (b p.1) (scalarErrorPolynomial Q (a + h / 2)) / scale⌋ = C ∧
      ∀ t ∈ Icc a (a + h), |scalarX (b p.1) t -
        eval ![t, scalarY (b p.1) t] (interceptPredictor Q scale C)| ≤ E)
    (htime : S ⊆ univ ×ˢ Icc a (a + h)) :
    μ S ≤ μ ((b ⁻¹' interceptAssignment U Q a h scale E C) ×ˢ Icc a (a + h)) := by
  apply measure_mono
  intro p hp
  obtain ⟨hu, hl, hf⟩ := hS p hp
  exact ⟨mem_interceptAssignment_of_block_fit U Q hh C hu hl hf, (htime hp).2⟩

/-- Every occupied label belongs to an explicit finite interval of integers. -/
theorem interceptAssignment_label_mem (U : Set (Fin 5 → ℝ))
    (Q : MvPolynomial (Fin 2) ℝ) {a h scale E R : ℝ} (hscale : 0 < scale)
    (hbound : ∀ b ∈ U, |eval b (scalarErrorPolynomial Q (a + h / 2))| ≤ R)
    (C : ℤ) (hC : (interceptAssignment U Q a h scale E C).Nonempty) :
    C ∈ Finset.Icc ⌊-R / scale⌋ ⌊R / scale⌋ := by
  obtain ⟨b, hb⟩ := hC
  obtain ⟨hl, hu⟩ := abs_le.mp (hbound b hb.1)
  rw [Finset.mem_Icc, ← hb.2.1]
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hl hscale.le),
    Int.floor_mono (div_le_div_of_nonneg_right hu hscale.le)⟩

/-- The adapted norm of the final predictor includes the actual intercept. -/
theorem interceptPredictor_bound (Q : MvPolynomial (Fin 2) ℝ)
    {scale r R H : ℝ} (hscale : 0 < scale) (C : ℤ)
    (hlabel : ⌊r / scale⌋ = C) (hr : |r| ≤ R) (x : Fin 2 → ℝ)
    (hQ : |eval x Q| ≤ H) :
    |eval x (interceptPredictor Q scale C)| ≤ H + R + scale / 2 := by
  calc
    |eval x (interceptPredictor Q scale C)| = |eval x Q + interceptCenter scale C| := by
      simp [interceptPredictor]
    _ ≤ |eval x Q| + |interceptCenter scale C| := abs_add_le _ _
    _ ≤ H + (R + scale / 2) := add_le_add hQ (interceptCenter_bound hscale C hlabel hr)
    _ = H + R + scale / 2 := by ring

/-- Three sample tests use six weak polynomial comparisons, uniformly in the coefficients. -/
theorem intercept_sample_format (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q.totalDegree ≤ 2)
    (a h center E : ℝ) :
    Fmt 6 2 {b : Fin 5 → ℝ | ∀ j : Fin 3,
      |eval b (scalarErrorPolynomial Q (interceptSample a h j)) - center| ≤ E} := by
  have htest (j : Fin 3) :
      Fmt 2 2
        {b | |eval b (scalarErrorPolynomial Q (interceptSample a h j)) - center| ≤ E} := by
    have ht : Fmt 2 2 {b : Fin 5 → ℝ |
        |eval b (scalarErrorPolynomial Q (interceptSample a h j) - MvPolynomial.C center)| ≤ E} :=
      format_abs_le
        (scalarErrorPolynomial Q (interceptSample a h j) - MvPolynomial.C center)
        ((totalDegree_sub_C_le _ _).trans (scalarErrorPolynomial_degree Q hQ _)) E
    exact ht.congr (by ext b; simp)
  have hs := fmt_rule_uniform
    (fun j : Fin 3 => {b | |eval b (scalarErrorPolynomial Q (interceptSample a h j)) - center| ≤ E})
    2 htest (fun p => ∀ j, p j)
  norm_num at hs
  exact hs

/-- Final assignment format has eight additional degree-two tests. -/
theorem interceptAssignment_format (U : Set (Fin 5 → ℝ)) {H : ℝ} {D : ℕ}
    (hU : Fmt H D U) (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q.totalDegree ≤ 2)
    (a h scale E : ℝ) (C : ℤ) :
    Fmt (H + 8) (max D 2) (interceptAssignment U Q a h scale E C) := by
  have hfloor : Fmt 2 2 {b : Fin 5 → ℝ |
      ⌊eval b (scalarErrorPolynomial Q (a + h / 2)) / scale⌋ = C} := by
    have hf : Fmt 2 2 {b : Fin 5 → ℝ |
        ⌊eval b (MvPolynomial.C scale⁻¹ * scalarErrorPolynomial Q (a + h / 2))⌋ = C} :=
      fmt_floor_eq
        (MvPolynomial.C scale⁻¹ * scalarErrorPolynomial Q (a + h / 2))
        ((Submission.Lib.K4ScalarSwitching.PolynomialDegree.degree_C_mul_le _ _).trans
          (scalarErrorPolynomial_degree Q hQ _)) C
    exact hf.congr (by ext b; simp [div_eq_mul_inv, mul_comm])
  have hs := intercept_sample_format Q hQ a h (interceptCenter scale C) E
  have hf := hU.inter (hfloor.inter hs)
  norm_num at hf
  exact hf.congr (by ext b; simp [interceptAssignment])

end

end Submission.Lib.K4ScalarCoreTools.Finalization
