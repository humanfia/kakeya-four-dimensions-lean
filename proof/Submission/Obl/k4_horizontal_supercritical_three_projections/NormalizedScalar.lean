import Submission.Obl.k4_horizontal_supercritical_three_projections.Conditioning
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MeasureTheory
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- The scalar input needs a coefficient bound on every point of its type.
Padding by zero outside the original chart supplies exactly that bound. -/
noncomputable def padCoefficients {α : Type} (A : Set α) (b : α → Fin 5 → ℝ) :
    α → Fin 5 → ℝ := by
  classical
  exact fun l => if l ∈ A then b l else 0

theorem measurable_padCoefficients {α : Type} [MeasurableSpace α]
    {A : Set α} (hA : MeasurableSet A) {b : α → Fin 5 → ℝ} (hb : Measurable b) :
    Measurable (padCoefficients A b) := by
  classical
  exact Measurable.ite hA hb measurable_const

theorem padCoefficients_eq {α : Type} {A : Set α} (b : α → Fin 5 → ℝ)
    {l : α} (hl : l ∈ A) : padCoefficients A b l = b l := by
  classical
  simp only [padCoefficients, ite_eq_left hl]

theorem measurable_scalar_cell {α : Type} [MeasurableSpace α]
    {b : α → Fin 5 → ℝ} (hb : Measurable b) (σ : ℝ) :
    Measurable (fun p : α × ℝ => scalarCell (b p.1) p.2 σ) := by
  apply Measurable.of_eval
  intro i
  fin_cases i
  · change Measurable (fun p : α × ℝ => ⌊p.2 / σ⌋)
    exact (measurable_snd.div_const σ).floor
  · change Measurable (fun p : α × ℝ => ⌊scalarY (b p.1) p.2 / σ⌋)
    have hy : Measurable (fun p : α × ℝ => scalarY (b p.1) p.2) := by
      unfold scalarY
      fun_prop
    exact (hy.div_const σ).floor

theorem measurable_scalar_signal {α : Type} [MeasurableSpace α]
    {b : α → Fin 5 → ℝ} (hb : Measurable b) :
    Measurable (fun p : α × ℝ => scalarX (b p.1) p.2) := by
  unfold scalarX
  fun_prop

/-- Pure, angular and terminal-support hypotheses are transported from the
original chart law using only its unchanged original prior denominator. -/
theorem normalized_scalar_admissible {α : Type} [MeasurableSpace α]
    {N η d s m C S U W : ℝ} (hN : 0 < N)
    (ν : Measure α) [IsProbabilityMeasure ν] (ζ μ : Measure (α × ℝ))
    (A : Set α) (hA : MeasurableSet A) (hA₀ : ν A ≠ 0) (hζ : ζ ≤ μ)
    (b : α → Fin 5 → ℝ) (hb : Measurable b)
    (hdom : ζ ≤ ENNReal.ofReal (N ^ η) • (ν.prod volume))
    (hsupp : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hcoeff : ∀ l ∈ A, ∀ i, |b l i| ≤ N ^ η)
    (hc₁ : N ^ (-C) ≤ W / (ν A).toReal) (hc₂ : W / (ν A).toReal ≤ N ^ C)
    (hcap : ∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s →
      μ {p | p.1 ∈ A ∧ scalarCell (b p.1) p.2 (N ^ (-m)) = q ∧
        ⌊scalarX (b p.1) p.2 / (N ^ (-r))⌋ = j} ≤
        ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * (N ^ (-r)) ^ d * W))
    (hsupport : ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      (F.card : ℝ) * (N ^ (-m)) ^ 2 ≤
        N ^ η * (W / (ν A).toReal)⁻¹ * (N ^ (-s)) ^ (-d) ∧
      ∀ᵐ p ∂μ, p.1 ∈ A →
        (scalarCell (b p.1) p.2 (N ^ (-m)), ⌊scalarX (b p.1) p.2 / N ^ (-s)⌋) ∈ F)
    (hang : ∀ (r : ℝ) (q : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U →
      μ {p | p.1 ∈ A ∧ scalarCell (b p.1) p.2 (N ^ (-m)) = q ∧
        ⌊scalarX (b p.1) p.2 / (N ^ (-s))⌋ = j ∧ ⌊b p.1 1 / N ^ (-r)⌋ = k} ≤
        ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * (N ^ (-s)) ^ d * N ^ (-S * r) * W)) :
    ScalarAdmissible N η d s m C S U (W / (ν A).toReal)
      (ProbabilityTheory.cond ν A) (padCoefficients A b) (chartLaw ν ζ A) := by
  classical
  let b' := padCoefficients A b
  have hb' : Measurable b' := measurable_padCoefficients hA hb
  have hcell := measurable_scalar_cell hb' (N ^ (-m))
  have hsignal := measurable_scalar_signal hb'
  have hevent (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ) :
      MeasurableSet {p : α × ℝ | scalarCell (b' p.1) p.2 (N ^ (-m)) = q ∧
        ⌊scalarX (b' p.1) p.2 / N ^ (-r)⌋ = j} :=
    (measurableSet_eq_fun hcell measurable_const).inter
      (measurableSet_eq_fun (hsignal.div_const _).floor measurable_const)
  refine ⟨hb', ProbabilityTheory.cond_isProbabilityMeasure hA₀,
    chartLaw_domination ν ζ A _ hdom, chartLaw_time_support ν ζ A hsupp,
    ?_, hc₁, hc₂, ?_, ?_, ?_⟩
  · intro l i
    by_cases hl : l ∈ A
    · simpa only [padCoefficients_eq b hl] using hcoeff l hl i
    · simp only [padCoefficients, ite_eq_right hl, Pi.zero_apply, abs_zero]
      exact Real.rpow_nonneg hN.le _
  · intro r q j hr hrs
    have hid : {p : α × ℝ | scalarCell (b' p.1) p.2 (N ^ (-m)) = q ∧
        ⌊scalarX (b' p.1) p.2 / N ^ (-r)⌋ = j} ∩ (A ×ˢ univ) =
        {p | p.1 ∈ A ∧ scalarCell (b p.1) p.2 (N ^ (-m)) = q ∧
          ⌊scalarX (b p.1) p.2 / N ^ (-r)⌋ = j} := by
      ext p
      by_cases hp : p.1 ∈ A
      · simp [b', padCoefficients_eq b hp, hp]
      · simp [hp]
    have hc := chartLaw_real_cap ν ζ μ A hA₀ hζ (hevent r q j)
      (N ^ η * (N ^ (-m)) ^ 2 * (N ^ (-r)) ^ d) W (hid ▸ hcap r q j hr hrs)
    convert hc using 1; congr 1; ring
  · obtain ⟨F, hcard, hF⟩ := hsupport
    refine ⟨F, hcard, ?_⟩
    have hF' : ∀ᵐ p ∂chartLaw ν ζ A, p.1 ∈ A →
        (scalarCell (b p.1) p.2 (N ^ (-m)), ⌊scalarX (b p.1) p.2 / N ^ (-s)⌋) ∈ F :=
      Measure.ae_smul_measure (ae_restrict_of_ae (ae_mono hζ hF)) _
    filter_upwards [hF', chartLaw_supported ν ζ hA] with p hp hpa
    simpa only [padCoefficients_eq b hpa] using hp hpa
  · intro r q j k hr hrU
    have hvel : Measurable (fun p : α × ℝ => ⌊b' p.1 1 / N ^ (-r)⌋) := by
      apply Measurable.floor
      fun_prop
    have hE := (hevent s q j).inter (measurableSet_eq_fun hvel
      (measurable_const : Measurable (fun _ : α × ℝ => k)))
    have hid : {p : α × ℝ | scalarCell (b' p.1) p.2 (N ^ (-m)) = q ∧
        ⌊scalarX (b' p.1) p.2 / N ^ (-s)⌋ = j ∧ ⌊b' p.1 1 / N ^ (-r)⌋ = k} ∩
        (A ×ˢ univ) =
        {p | p.1 ∈ A ∧ scalarCell (b p.1) p.2 (N ^ (-m)) = q ∧
          ⌊scalarX (b p.1) p.2 / N ^ (-s)⌋ = j ∧ ⌊b p.1 1 / N ^ (-r)⌋ = k} := by
      ext p
      by_cases hp : p.1 ∈ A
      · simp [b', padCoefficients_eq b hp, hp]
      · simp [hp]
    have hE' : MeasurableSet {p : α × ℝ | scalarCell (b' p.1) p.2 (N ^ (-m)) = q ∧
        ⌊scalarX (b' p.1) p.2 / N ^ (-s)⌋ = j ∧ ⌊b' p.1 1 / N ^ (-r)⌋ = k} := by
      convert hE using 1
      ext p
      exact and_assoc.symm
    have hc := chartLaw_real_cap ν ζ μ A hA₀ hζ hE'
      (N ^ η * (N ^ (-m)) ^ 2 * (N ^ (-s)) ^ d * N ^ (-S * r)) W
      (hid ▸ hang r q j k hr hrU)
    convert hc using 1; congr 1; ring

end Submission.Obl.k4_horizontal_supercritical_three_projections
