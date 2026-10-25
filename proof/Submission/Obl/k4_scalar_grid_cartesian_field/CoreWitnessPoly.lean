-- From this LOT obligation o230, session x0803, commit 872bba82,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CoreWitnessPoly.lean.
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreWitness
import Submission.Obl.k4_scalar_grid_cartesian_field.LongRowField
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.CoefficientBounds

/-!
# Normalized witness polynomials and their time rows

A qualified witness carries a polynomial fit `P` of the graph row along its
line. In normalized block time `τ = (t - a) / h` it becomes `P(a + h τ)`, with
coefficients bounded by the sup norm, and its fitting row (with the null code
classes removed, which costs nothing on a good line) has length `≥ 1 / Λ`.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set Polynomial
open scoped ENNReal

/-- The normalized-time version of a raw-time polynomial. -/
noncomputable def normPoly (a h : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  p.comp (C a + C h * X)

theorem eval_normPoly (a h : ℝ) (p : Polynomial ℝ) (τ : ℝ) :
    (normPoly a h p).eval τ = p.eval (a + h * τ) := by
  simp [normPoly]

theorem natDegree_normPoly_le (a h : ℝ) (p : Polynomial ℝ) (M : ℕ) (hp : p.natDegree ≤ M) :
    (normPoly a h p).natDegree ≤ M := by
  unfold normPoly
  apply natDegree_comp_le.trans
  have h1 : (C a + C h * X).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le h X).trans natDegree_X_le))
  calc p.natDegree * (C a + C h * X).natDegree ≤ M * 1 := Nat.mul_le_mul hp h1
    _ = M := mul_one M

/-- A raw polynomial with bounded coefficients is bounded on `[0,1]`. -/
theorem abs_eval_le_of_coeff (p : Polynomial ℝ) (M : ℕ) (hp : p.natDegree ≤ M) (Λ : ℝ)
    (hc : ∀ i, |p.coeff i| ≤ Λ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |p.eval t| ≤ ((M : ℝ) + 1) * Λ := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  calc |∑ i ∈ Finset.range (M + 1), p.coeff i * t ^ i|
      ≤ ∑ i ∈ Finset.range (M + 1), |p.coeff i * t ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (M + 1), Λ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_pow, abs_of_nonneg ht.1]
        calc |p.coeff i| * t ^ i ≤ Λ * 1 :=
              mul_le_mul (hc i) (pow_le_one₀ ht.1 ht.2) (pow_nonneg ht.1 i)
                ((abs_nonneg _).trans (hc i))
          _ = Λ := mul_one Λ
    _ = ((M : ℝ) + 1) * Λ := by simp

/-- Coefficient bound of the normalized polynomial, through the sup norm. -/
theorem exists_normPoly_coeff_constant (M : ℕ) :
    ∃ Cu : ℝ, 0 < Cu ∧ ∀ (p : Polynomial ℝ), p.natDegree ≤ M → ∀ Λ : ℝ, 0 ≤ Λ →
      (∀ i, |p.coeff i| ≤ Λ) → ∀ a h : ℝ, 0 ≤ a → 0 ≤ h → a + h ≤ 1 →
      ∀ k, |(normPoly a h p).coeff k| ≤ Cu * (((M : ℝ) + 1) * Λ) := by
  obtain ⟨Cu, hCu, hcoef⟩ := Cart.Switching.exists_univariate_coefficient_constant M
  refine ⟨Cu, hCu, ?_⟩
  intro p hp Λ hΛ hc a h ha hh hah k
  apply hcoef (normPoly a h p) (natDegree_normPoly_le a h p M hp) _ (by positivity)
  intro τ hτ
  rw [eval_normPoly]
  apply abs_eval_le_of_coeff p M hp Λ hc
  constructor
  · nlinarith [hτ.1]
  · nlinarith [hτ.2]

/-- The normalized fitting row of a witness line. -/
def witnessRow (ρ : Measure Incidence) (E : Set Incidence) (N B rT a h ε : ℝ)
    (G : (Fin 3 → ℤ) → Fin 2 → ℝ) (l : Trajectory) (P : Fin 2 → Polynomial ℝ) : Set ℝ :=
  {τ | τ ∈ Icc (0 : ℝ) 1 ∧ (l, a + h * τ) ∈ E ∧
    (∀ e, |G (physCube N B (l, a + h * τ)) e - (P e).eval (a + h * τ)| ≤ ε) ∧
    (l, a + h * τ) ∉ nullCodeSet ρ E (coreCode N B rT)}

theorem measurableSet_witnessRow (ρ : Measure Incidence) (E : Set Incidence)
    (hE : MeasurableSet E) (N B rT a h ε : ℝ) (G : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (l : Trajectory) (P : Fin 2 → Polynomial ℝ) :
    MeasurableSet (witnessRow ρ E N B rT a h ε G l P) := by
  have hpt : Measurable fun τ : ℝ => ((l, a + h * τ) : Incidence) :=
    measurable_const.prodMk (measurable_const.add (measurable_const.mul measurable_id))
  have hZ := measurableSet_nullCodeSet ρ E (coreCode N B rT) (measurable_coreCode N B rT)
  have hGm : ∀ e : Fin 2, Measurable fun τ : ℝ =>
      |G (physCube N B (l, a + h * τ)) e - (P e).eval (a + h * τ)| := by
    intro e
    have h1 : Measurable fun τ : ℝ => G (physCube N B (l, a + h * τ)) e :=
      (measurable_of_countable (fun q : Fin 3 → ℤ => G q e)).comp
        ((measurable_physCube N B).comp hpt)
    have h2 : Measurable fun τ : ℝ => (P e).eval (a + h * τ) :=
      (Polynomial.continuous (P e)).measurable.comp
        (measurable_const.add (measurable_const.mul measurable_id))
    exact (h1.sub h2).abs
  have hset : witnessRow ρ E N B rT a h ε G l P =
      Icc (0 : ℝ) 1 ∩ ((fun τ : ℝ => ((l, a + h * τ) : Incidence)) ⁻¹' E) ∩
        (⋂ e : Fin 2, {τ | |G (physCube N B (l, a + h * τ)) e - (P e).eval (a + h * τ)| ≤ ε}) ∩
        ((fun τ : ℝ => ((l, a + h * τ) : Incidence)) ⁻¹' (nullCodeSet ρ E (coreCode N B rT)))ᶜ := by
    ext τ
    simp [witnessRow, and_assoc]
  rw [hset]
  refine ((measurableSet_Icc.inter (hpt hE)).inter ?_).inter (hpt hZ).compl
  exact MeasurableSet.iInter fun e => measurableSet_le (hGm e) measurable_const

/-- On a good line, the normalized fitting row keeps relative length `≥ 1 / Λ`. -/
theorem volume_witnessRow_ge (ρ : Measure Incidence) (E : Set Incidence)
    (N B rT a h ε Λ : ℝ) (hh : 0 < h) (hΛ : 0 < Λ) (G : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (l : Trajectory) (P : Fin 2 → Polynomial ℝ)
    (hl : l ∉ badLines ρ E (coreCode N B rT))
    (hrow : ENNReal.ofReal (h / Λ) ≤ volume {t | (l, t) ∈ E ∧ t ∈ Icc a (a + h) ∧
      ∀ e, |G (physCube N B (l, t)) e - (P e).eval t| ≤ ε}) :
    ENNReal.ofReal Λ⁻¹ ≤ volume (witnessRow ρ E N B rT a h ε G l P) := by
  set T := {t | (l, t) ∈ E ∧ t ∈ Icc a (a + h) ∧
      ∀ e, |G (physCube N B (l, t)) e - (P e).eval t| ≤ ε} with hT
  have hTE : T ⊆ {t | (l, t) ∈ E} := fun t ht => ht.1
  have hdiff := volume_diff_null_of_not_bad ρ E (coreCode N B rT) l hl T hTE
  have hpre : witnessRow ρ E N B rT a h ε G l P =
      (fun τ : ℝ => a + h * τ) ⁻¹' (T \ {t | (l, t) ∈ nullCodeSet ρ E (coreCode N B rT)}) := by
    ext τ
    simp only [witnessRow, mem_ofPred_eq, mem_preimage, mem_diff, hT, mem_Icc]
    constructor
    · rintro ⟨hτ, hE', hfit, hZ⟩
      refine ⟨⟨hE', ⟨?_, ?_⟩, hfit⟩, hZ⟩
      · nlinarith [hτ.1]
      · nlinarith [hτ.2]
    · rintro ⟨⟨hE', hI, hfit⟩, hZ⟩
      refine ⟨⟨?_, ?_⟩, hE', hfit, hZ⟩
      · by_contra hneg
        push_neg at hneg
        nlinarith [hI.1]
      · by_contra hneg
        push_neg at hneg
        nlinarith [hI.2]
  rw [hpre, volume_affine_time_preimage a hh, hdiff]
  calc ENNReal.ofReal Λ⁻¹ = ENNReal.ofReal h⁻¹ * ENNReal.ofReal (h / Λ) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal h⁻¹ * volume T := mul_le_mul' le_rfl hrow

end Submission.Obl.k4_scalar_grid_cartesian_field
