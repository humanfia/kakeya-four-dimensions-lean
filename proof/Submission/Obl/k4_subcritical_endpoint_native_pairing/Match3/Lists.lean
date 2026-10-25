/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/Lists.lean.
   Original source attributions are retained below. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.DomainCaps

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

open Set MeasureTheory

/-- Whole-box comparison controls every normalized coefficient difference. -/
theorem normCoeffs_sub_le_of_box {t₀ τ p₀ q₀ D M : ℝ} (hτ : 0 < τ) (hD : 0 < D)
    (h h' : Fin 6 → ℝ)
    (hbox : ∀ t ∈ Icc t₀ (t₀ + τ), ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |parameterPredictor h t p q - parameterPredictor h' t p q| ≤ M) :
    ∀ k, |normCoeffs t₀ τ p₀ q₀ D h k - normCoeffs t₀ τ p₀ q₀ D h' k| ≤ 512 * M := by
  have hdiff : ∀ t ∈ Icc t₀ (t₀ + τ), ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |parameterPredictor (h - h') t p q| ≤ M := by
    intro t ht p hp q hq
    convert hbox t ht p hp q hq using 1 <;> congr 1 <;> dsimp [parameterPredictor] <;> ring
  intro k
  have hc := abs_normCoeffs_le hτ hD hdiff k
  rw [← normCoeffs_sub] at hc
  exact hc

/-- The native list near a specified endpoint predictor on the ORIGINAL box. -/
noncomputable def parameterComparisonList {ι : Type} [Fintype ι]
    (h : ι → Fin 6 → ℝ) (h₀ : Fin 6 → ℝ) (t₀ τ p₀ q₀ D M : ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => ∀ t ∈ Icc t₀ (t₀ + τ), ∀ p ∈ Icc p₀ (p₀ + D),
    ∀ q ∈ Icc q₀ (q₀ + D), |parameterPredictor (h i) t p q - parameterPredictor h₀ t p q| ≤ M)

theorem mem_parameterComparisonList {ι : Type} [Fintype ι]
    (h : ι → Fin 6 → ℝ) (h₀ : Fin 6 → ℝ) (t₀ τ p₀ q₀ D M : ℝ) (i : ι) :
    i ∈ parameterComparisonList h h₀ t₀ τ p₀ q₀ D M ↔
      ∀ t ∈ Icc t₀ (t₀ + τ), ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
        |parameterPredictor (h i) t p q - parameterPredictor h₀ t p q| ≤ M := by
  classical
  simp only [parameterComparisonList, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Extend the jet count to all radii by using the total bounded-coefficient
list at radii larger than its coefficient ceiling. The same argument appears
inside x0764's DomainComparison (commit2b232aca); this exports it separately. -/
theorem jet_count_all_scales {Ω : Type*} [MeasurableSpace Ω] (lam : Measure Ω)
    {ι : Type} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (f : Ω → ι) (T P Q X : Ω → ℝ) (c : ι → Fin 10 → ℝ)
    {t₀ τ p₀ q₀ D δ δm V E d A₀ : ℝ}
    (hf : Measurable f) (hτ : 0 < τ) (hD : 0 < D) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδm : 0 < δm)
    (hV : 0 < V) (hE : 1 ≤ E) (hA₀ : 0 < A₀) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hmτ : 15360 * E * δm ≤ δ * τ) (hmD : 15360 * E * δm ≤ δ * D)
    (hgood : ∀ᵐ ω ∂lam, T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧
      Q ω ∈ Icc q₀ (q₀ + D) ∧
      |X ω - q3 (c (f ω)) (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω))| ≤ δ / 2)
    (hc : ∀ i k, |c i k| ≤ 512 * E)
    (hfloor : ∀ i, ENNReal.ofReal (τ * D ^ 2 * V * δ ^ d / A₀) ≤ lam {ω | f ω = i})
    (hcap : ∀ σ, δ ≤ σ → σ ≤ 1 → ∀ (cc : Fin 3 → ℤ) (j : ℤ),
      lam {ω | (fun k => ⌊(![T ω, P ω, Q ω] : Fin 3 → ℝ) k / δm⌋) = cc ∧ ⌊X ω / σ⌋ = j} ≤
        ENNReal.ofReal (V * σ ^ d * δm ^ 3))
    (g : Fin 10 → ℝ) {M : ℝ} (hδM : δ ≤ M) :
    ((Finset.univ.filter (fun i => ∀ k, |c i k - g k| ≤ M)).card : ℝ) ≤
      2000000 * A₀ * E * (M / δ) ^ d := by
  classical
  by_cases hME : M ≤ 512 * E
  · exact jet_count lam f T P Q X c hf hτ hD hδ hδ1 hδm hV hE hA₀ hd0 hd1 hmτ hmD
      hgood hc hfloor hcap g hδM hME
  · have hME' : 512 * E < M := lt_of_not_ge hME
    have hall : (Finset.univ.filter (fun i => ∀ k, |c i k - g k| ≤ M)).card ≤
        (Finset.univ.filter (fun i => ∀ k, |c i k - (0 : Fin 10 → ℝ) k| ≤ 512 * E)).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.zero_apply, sub_zero]
      exact hc i
    have hbase := jet_count lam f T P Q X c hf hτ hD hδ hδ1 hδm hV hE hA₀ hd0 hd1 hmτ hmD
      hgood hc hfloor hcap (0 : Fin 10 → ℝ) (M := 512 * E) (by linarith) le_rfl
    calc
      _ ≤ ((Finset.univ.filter (fun i => ∀ k, |c i k - (0 : Fin 10 → ℝ) k| ≤ 512 * E)).card : ℝ) :=
        by exact_mod_cast hall
      _ ≤ 2000000 * A₀ * E * (512 * E / δ) ^ d := hbase
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hME'.le hδ.le) hd0)
        (by positivity)

/-- Marginal floors are used on the pre-matching law. A later restriction
may use this same finite list without needing any new floor for its contacts. -/
theorem parameter_comparison_list_count {Ω : Type*} [MeasurableSpace Ω] (lam : Measure Ω)
    {ι : Type} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (f : Ω → ι) (T P Q X : Ω → ℝ) (h : ι → Fin 6 → ℝ) (h₀ : Fin 6 → ℝ)
    {t₀ τ p₀ q₀ D δ δm V E d A₀ M : ℝ}
    (hf : Measurable f) (hτ : 0 < τ) (hD : 0 < D) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδm : 0 < δm)
    (hV : 0 < V) (hE : 1 ≤ E) (hA₀ : 0 < A₀) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hmτ : 15360 * E * δm ≤ δ * τ) (hmD : 15360 * E * δm ≤ δ * D)
    (hgood : ∀ᵐ ω ∂lam, T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧
      Q ω ∈ Icc q₀ (q₀ + D) ∧ |X ω - parameterPredictor (h (f ω)) (T ω) (P ω) (Q ω)| ≤ δ / 2)
    (hnorm : ∀ i, ∀ t ∈ Icc t₀ (t₀ + τ), ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |parameterPredictor (h i) t p q| ≤ E)
    (hfloor : ∀ i, ENNReal.ofReal (τ * D ^ 2 * V * δ ^ d / A₀) ≤ lam {ω | f ω = i})
    (hcap : ∀ σ, δ ≤ σ → σ ≤ 1 → ∀ (cc : Fin 3 → ℤ) (j : ℤ),
      lam {ω | (fun k => ⌊(![T ω, P ω, Q ω] : Fin 3 → ℝ) k / δm⌋) = cc ∧ ⌊X ω / σ⌋ = j} ≤
        ENNReal.ofReal (V * σ ^ d * δm ^ 3))
    (hδM : δ ≤ M) :
    ((parameterComparisonList h h₀ t₀ τ p₀ q₀ D M).card : ℝ) ≤
      2000000 * A₀ * E * ((512 * M) / δ) ^ d := by
  classical
  let c : ι → Fin 10 → ℝ := fun i => normCoeffs t₀ τ p₀ q₀ D (h i)
  have hg : ∀ᵐ ω ∂lam, T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧
      Q ω ∈ Icc q₀ (q₀ + D) ∧
      |X ω - q3 (c (f ω)) (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω))| ≤ δ / 2 := by
    filter_upwards [hgood] with ω hp
    simpa only [c, q3_normCoeffs_normVec hτ.ne' hD.ne'] using hp
  have hsub : parameterComparisonList h h₀ t₀ τ p₀ q₀ D M ⊆
      Finset.univ.filter (fun i => ∀ k, |c i k - normCoeffs t₀ τ p₀ q₀ D h₀ k| ≤ 512 * M) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      normCoeffs_sub_le_of_box hτ hD (h i) h₀ ((mem_parameterComparisonList _ _ _ _ _ _ _ _ _).mp hi)⟩
  exact (show ((parameterComparisonList h h₀ t₀ τ p₀ q₀ D M).card : ℝ) ≤
      ((Finset.univ.filter (fun i => ∀ k, |c i k - normCoeffs t₀ τ p₀ q₀ D h₀ k| ≤ 512 * M)).card : ℝ)
      by exact_mod_cast Finset.card_le_card hsub).trans
    (jet_count_all_scales lam f T P Q X c hf hτ hD hδ hδ1 hδm hV hE hA₀ hd0 hd1 hmτ hmD
      hg (fun i k => abs_normCoeffs_le hτ hD (hnorm i) k) hfloor hcap
      (normCoeffs t₀ τ p₀ q₀ D h₀) (by linarith))

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
