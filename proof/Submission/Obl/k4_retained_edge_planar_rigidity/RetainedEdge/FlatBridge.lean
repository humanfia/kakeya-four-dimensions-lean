-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/FlatBridge.lean;
-- only the namespace and module paths were renamed to o071's.
import Mathlib

/-!
# Discrete laws in the Fourier-decay input

The decay input T4 (`k4_oss_decay`, paper display `re:oss-input` in the special case used by
Lemma 7.4) is stated for an arbitrary probability measure on `ℝ` and its `n`-fold product. For a
finite law `∑ᵢ νᵢ δ_{yᵢ}` the product measure is the finite sum of Dirac masses at the tuples, so the
integral in T4 is a finite exponential sum. This file records that identification and the resulting
form of T4 for finite laws.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The finite law `∑ᵢ νᵢ δ_{yᵢ}` on `ℝ`. -/
def discLaw (ν : ι → ℝ) (y : ι → ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (ν i) • Measure.dirac (y i)

theorem discLaw_apply (ν y : ι → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    discLaw ν y s = ∑ i, ENNReal.ofReal (ν i) * s.indicator 1 (y i) := by
  simp [discLaw, Finset.sum_apply, Measure.dirac_apply' _ hs]

theorem discLaw_univ (ν y : ι → ℝ) : discLaw ν y Set.univ = ∑ i, ENNReal.ofReal (ν i) := by
  rw [discLaw_apply ν y MeasurableSet.univ]
  simp

scoped instance discLaw_isFiniteMeasure (ν y : ι → ℝ) : IsFiniteMeasure (discLaw ν y) := by
  constructor
  rw [discLaw_univ]
  exact ENNReal.sum_lt_top.mpr fun i _ => ENNReal.ofReal_lt_top

theorem discLaw_isProbability {ν : ι → ℝ} (hν : ∀ i, 0 ≤ ν i) (hν1 : ∑ i, ν i = 1) (y : ι → ℝ) :
    IsProbabilityMeasure (discLaw ν y) := by
  constructor
  rw [discLaw_univ, ← ENNReal.ofReal_sum_of_nonneg fun i _ => hν i, hν1, ENNReal.ofReal_one]

theorem discLaw_Icc (ν y : ι → ℝ) (hν : ∀ i, 0 ≤ ν i) (a b : ℝ) :
    discLaw ν y (Set.Icc a b) = ENNReal.ofReal (∑ i, if y i ∈ Set.Icc a b then ν i else 0) := by
  rw [discLaw_apply ν y measurableSet_Icc, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : y i ∈ Set.Icc a b
    · simp [hi]
    · simp [hi]
  · intro i _; split_ifs <;> simp [hν i]

theorem discLaw_compl_Icc {ν y : ι → ℝ} (hy : ∀ i, y i ∈ Set.Icc (-1 : ℝ) 1) :
    discLaw ν y (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  rw [discLaw_apply ν y measurableSet_Icc.compl]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [hy i]

theorem pi_discLaw [DecidableEq ι] {ν : ι → ℝ} (hν : ∀ i, 0 ≤ ν i) (y : ι → ℝ) (n : ℕ) :
    Measure.pi (fun _ : Fin n => discLaw ν y) =
      ∑ U : Fin n → ι, ENNReal.ofReal (∏ j, ν (U j)) • Measure.dirac (fun j => y (U j)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp only [discLaw_apply ν y (hs _)]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [ENNReal.ofReal_prod_of_nonneg fun j _ => hν (U j)]
  by_cases hU : (fun j => y (U j)) ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hU, Pi.one_apply, mul_one]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Set.indicator_of_mem (hU j (Set.mem_univ j)), Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hU, mul_zero]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hU
    obtain ⟨j, hj⟩ := hU
    refine (Finset.prod_eq_zero (Finset.mem_univ j) ?_).symm
    rw [Set.indicator_of_notMem hj, mul_zero]

/-- The integral against the product of a finite law is a finite sum over tuples. -/
theorem integral_pi_discLaw [DecidableEq ι] {ν : ι → ℝ} (hν : ∀ i, 0 ≤ ν i) (y : ι → ℝ) (n : ℕ)
    (f : (Fin n → ℝ) → ℂ) :
    ∫ x, f x ∂(Measure.pi (fun _ : Fin n => discLaw ν y)) =
      ∑ U : Fin n → ι, ((∏ j, ν (U j) : ℝ) : ℂ) * f (fun j => y (U j)) := by
  rw [pi_discLaw hν y n, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun U _ => ?_
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (Finset.prod_nonneg fun j _ => hν (U j)), Complex.real_smul]
  · intro U _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The Fourier-decay input T4, as frozen in the obligation. -/
def OSSDecay : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 → ∃ n : ℕ, 2 ≤ n ∧ ∃ r₀ ε₀ τ : ℝ, 0 < r₀ ∧ 0 < ε₀ ∧ 0 < τ ∧ ∀ r : ℝ,
    0 < r → r < r₀ → ∀ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure μ →
    μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, r ≤ u → u ≤ 1 →
      μ (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ε₀) * u ^ s)) →
    ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2 * r⁻¹ → ‖MeasureTheory.integral (MeasureTheory.Measure.pi
      (fun _ : Fin n => μ)) (fun x : Fin n → ℝ => Complex.exp
        (((-2 * Real.pi * ξ * (∏ j : Fin n, x j) : ℝ) : ℂ) * Complex.I))‖ ≤ |ξ| ^ (-τ)

/-- **T4 for finite laws**: the exponential sum of the product of `n` independent samples
decays at frequencies comparable to `r⁻¹`. -/
theorem ossDecay_discrete (hT4 : OSSDecay) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ r₀ ε₀ τ : ℝ, 0 < r₀ ∧ 0 < ε₀ ∧ 0 < τ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ν y : κ → ℝ), (∀ i, 0 ≤ ν i) → ∑ i, ν i = 1 →
      (∀ i, y i ∈ Set.Icc (-1 : ℝ) 1) →
      (∀ x u : ℝ, r ≤ u → u ≤ 1 →
        (∑ i, if y i ∈ Set.Icc (x - u) (x + u) then ν i else 0) ≤ r ^ (-ε₀) * u ^ s) →
      ∀ ζ : ℝ, r⁻¹ ≤ |ζ| → |ζ| ≤ 2 * r⁻¹ →
        ‖∑ U : Fin n → κ, ((∏ j, ν (U j) : ℝ) : ℂ) *
          Complex.exp (((2 * Real.pi * ζ * ∏ j, y (U j) : ℝ) : ℂ) * Complex.I)‖ ≤ |ζ| ^ (-τ) := by
  obtain ⟨n, hn, r₀, ε₀, τ, hr₀, hε₀, hτ, hdec⟩ := hT4 s hs hs1
  refine ⟨n, hn, r₀, ε₀, τ, hr₀, hε₀, hτ, ?_⟩
  intro r hr hrr₀ κ _ _ ν y hν hν1 hy hfrost ζ hζ1 hζ2
  have := discLaw_isProbability hν hν1 y
  have hμc := discLaw_compl_Icc (ν := ν) hy
  have hμf : ∀ x u : ℝ, r ≤ u → u ≤ 1 →
      discLaw ν y (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ε₀) * u ^ s) := by
    intro x u hu hu1
    rw [discLaw_Icc ν y hν]
    exact ENNReal.ofReal_le_ofReal (hfrost x u hu hu1)
  have key := hdec r hr hrr₀ (discLaw ν y) inferInstance hμc hμf (-ζ) (by rwa [abs_neg])
    (by rwa [abs_neg])
  rw [abs_neg, integral_pi_discLaw hν y n] at key
  have heq : (∑ U : Fin n → κ, ((∏ j, ν (U j) : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * ζ * ∏ j, y (U j) : ℝ) : ℂ) * Complex.I)) =
      ∑ U : Fin n → κ, ((∏ j, ν (U j) : ℝ) : ℂ) *
      Complex.exp (((-2 * Real.pi * (-ζ) * ∏ j, (fun j => y (U j)) j : ℝ) : ℂ) * Complex.I) := by
    refine Finset.sum_congr rfl fun U _ => ?_
    congr 3
    ring_nf
  rw [heq]
  exact key

end

end Submission.Obl.k4_retained_edge_planar_rigidity
