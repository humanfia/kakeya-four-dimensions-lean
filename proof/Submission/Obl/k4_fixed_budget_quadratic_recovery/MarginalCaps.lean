import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps
import Submission.Obl.k4_fixed_budget_quadratic_recovery.RecoveryInterface

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set

/-- The two continuous coordinates retained by scalar projection. -/
def scalarBase {α : Type*} (b : α → Fin 5 → ℝ) (p : α × ℝ) :
    EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2]

/-- Whole-time scalar fits inherit an index/base marginal cap from the original
continuous scalar-bin cap. Its cost depends on fit width, not on polynomial range. -/
theorem scalarFit_marginal_cap
    {N η d s m S U δ : ℝ} (hN : 0 < N) (hs : 0 ≤ s)
    {ν : Measure (ℕ × (Fin 6 → ℝ))}
    {μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ}
    (hlaw : ProjectedScalarLaw N η d s m S U ν μ b)
    (P : MvPolynomial (Fin 2) ℝ) (A : Set (Fin 5 → ℝ))
    (hA : A ⊆ scalarFit P (N ^ δ * N ^ (-s)))
    (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : MeasurableSet E) :
    μ {p | b p.1 ∈ A ∧ scalarBase b p ∈ E} ≤
      ENNReal.ofReal (2 * N ^ δ + 5) *
        ENNReal.ofReal (N ^ η * (N ^ (-s)) ^ d) * volume E := by
  have htime : ∀ᵐ p ∂μ, p.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    have heq : {p : ((ℕ × (Fin 6 → ℝ)) × ℝ) | ¬p.2 ∈ Icc (0 : ℝ) 1} =
        (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by ext p; simp
    rw [heq]
    exact hlaw.1.2.2.2.1
  let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => MvPolynomial.eval ![q 0, q 1] P
  have hf : Measurable f := P.continuous_eval.measurable.comp (by fun_prop)
  have hcap : ∀ j E', MeasurableSet E' →
      μ {p | scalarBase b p ∈ E' ∧ ⌊scalarX (b p.1) p.2 / N ^ (-s)⌋ = j} ≤
        ENNReal.ofReal (N ^ η * (N ^ (-s)) ^ d) * volume E' := by
    intro j E' hE'
    exact hlaw.2 s j E' hs le_rfl hE'
  have hmove := moving_interval_cap μ volume (scalarBase b)
    (fun p => scalarX (b p.1) p.2) (Real.rpow_pos_of_pos hN (-s))
    (Real.rpow_nonneg hN.le δ) _ hcap f hf E hE
  apply le_trans (measure_mono_ae ?_) hmove
  filter_upwards [htime] with p hp
  intro h
  refine ⟨h.2, ?_⟩
  exact (hA h.1) p.2 hp

/-- A convenient power form of the same cap, with a fixed factor seven. -/
theorem scalarFit_marginal_cap_power
    {N η d s m S U δ : ℝ} (hN : 1 ≤ N) (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    {ν : Measure (ℕ × (Fin 6 → ℝ))}
    {μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ}
    (hlaw : ProjectedScalarLaw N η d s m S U ν μ b)
    (P : MvPolynomial (Fin 2) ℝ) (A : Set (Fin 5 → ℝ))
    (hA : A ⊆ scalarFit P (N ^ δ * N ^ (-s)))
    (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : MeasurableSet E) :
    μ {p | b p.1 ∈ A ∧ scalarBase b p ∈ E} ≤
      ENNReal.ofReal (7 * N ^ (η + δ - d * s)) * volume E := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  apply (scalarFit_marginal_cap hN0 hs hlaw P A hA E hE).trans
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply ENNReal.ofReal_le_ofReal
  have hpow : 1 ≤ N ^ δ := Real.one_le_rpow hN hδ
  calc
    (2 * N ^ δ + 5) * (N ^ η * (N ^ (-s)) ^ d) ≤
        (7 * N ^ δ) * (N ^ η * (N ^ (-s)) ^ d) := by gcongr; linarith
    _ = 7 * N ^ (η + δ - d * s) := by
      rw [← Real.rpow_mul hN0.le]
      rw [mul_assoc, ← mul_assoc (N ^ δ), ← Real.rpow_add hN0,
        ← Real.rpow_add hN0]
      congr 2
      ring

end Submission.Obl.k4_fixed_budget_quadratic_recovery
