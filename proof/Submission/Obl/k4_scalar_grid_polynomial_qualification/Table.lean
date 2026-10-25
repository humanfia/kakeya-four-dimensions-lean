import Submission.Obl.k4_scalar_grid_polynomial_qualification.Rounding
import Submission.Obl.k4_scalar_grid_polynomial_qualification.WeightedResidual

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory Filter
open Submission.Obl.k4_native_calibrated_homogeneous_remainder

/-- A fixed graph certificate, together with its original depth-one packet
labels. This record adds no analytic hypotheses. -/
structure QualificationTable (α : Type*) [MeasurableSpace α] where
  W : ℕ → ℕ
  n : ℕ → ℕ
  N : ℕ → ℝ
  h : ℕ → ℝ
  ω : (k : ℕ) → Fin (W k) → ℝ
  ρ : (k : ℕ) → Fin (W k) → Measure (α × ℝ)
  E : (k : ℕ) → Fin (W k) → Set (α × ℝ)
  γ : (k : ℕ) → Fin (n k) → Fin (W k)
  A : (k : ℕ) → Fin (n k) → Set α
  I : (k : ℕ) → Fin (n k) → Set ℝ
  row : (k : ℕ) → Fin (W k) → α × ℝ → Fin 2 → ℝ

namespace QualificationTable

variable {α : Type*} [MeasurableSpace α] (D : QualificationTable α)

noncomputable def law (k : ℕ) (g : Fin (D.W k)) : Measure (α × ℝ) :=
  (D.ρ k g).restrict (D.E k g)

def incidence (k : ℕ) (i : Fin (D.n k)) (p : α × ℝ) : Prop :=
  p.1 ∈ D.A k i ∧ p.2 ∈ D.I k i

def realFit (M : ℕ) (ε : ℝ) (k : ℕ) (i : Fin (D.n k)) (p : α × ℝ) : Prop :=
  Fits (D.E k (D.γ k i)) (D.row k (D.γ k i)) (D.I k i)
    M (D.N k ^ ε) (D.h k ^ M) (D.h k * D.N k ^ (-ε)) p

def rationalFit (M : ℕ) (ε : ℝ) (k : ℕ) (i : Fin (D.n k)) (p : α × ℝ) : Prop :=
  RationalFits (D.E k (D.γ k i)) (D.row k (D.γ k i)) (D.I k i)
    M (D.N k ^ ε) (D.h k ^ M) (D.h k * D.N k ^ (-ε)) p

def realFailure (M : ℕ) (ε : ℝ) (k : ℕ) (g : Fin (D.W k)) : Set (α × ℝ) :=
  {p | ∃ i, D.γ k i = g ∧ p.1 ∈ D.A k i ∧ p.2 ∈ D.I k i ∧ ¬ D.realFit M ε k i p}

def rationalFailure (M : ℕ) (ε : ℝ) (k : ℕ) (g : Fin (D.W k)) : Set (α × ℝ) :=
  {p | ∃ i, D.γ k i = g ∧ p.1 ∈ D.A k i ∧ p.2 ∈ D.I k i ∧ ¬ D.rationalFit M ε k i p}

theorem realFailure_subset_rationalFailure (M : ℕ) (ε : ℝ) (k : ℕ) (g : Fin (D.W k)) :
    D.realFailure M ε k g ⊆ D.rationalFailure M ε k g := by
  rintro p ⟨i, hg, ha, ht, hnot⟩
  exact ⟨i, hg, ha, ht, fun h => hnot (RationalFits.fits h)⟩

theorem measurableSet_rationalFailure (M : ℕ) (ε : ℝ) (k : ℕ) (g : Fin (D.W k))
    (hE : ∀ g, MeasurableSet (D.E k g)) (hrow : ∀ g, Measurable (D.row k g))
    (hA : ∀ i, MeasurableSet (D.A k i)) (hI : ∀ i, MeasurableSet (D.I k i)) :
    MeasurableSet (D.rationalFailure M ε k g) := by
  have hi (i : Fin (D.n k)) : MeasurableSet {p : α × ℝ |
      D.γ k i = g ∧ p.1 ∈ D.A k i ∧ p.2 ∈ D.I k i ∧ ¬ D.rationalFit M ε k i p} :=
    (MeasurableSet.const _).inter ((measurable_fst (hA i)).inter
      ((measurable_snd (hI i)).inter
        (measurableSet_rationalFits (hE _) (hrow _) (hI i) _ _ _ _).compl))
  simpa only [rationalFailure, Set.ofPred_exists] using MeasurableSet.iUnion hi

noncomputable def totalMass (k : ℕ) : ENNReal :=
  ∑ g, ENNReal.ofReal (D.ω k g) * D.law k g univ

noncomputable def rationalFailureRatio (M : ℕ) (ε : ℝ) (k : ℕ) : ℝ :=
  (∑ g, ENNReal.ofReal (D.ω k g) * D.law k g (D.rationalFailure M ε k g)).toReal /
    (D.totalMass k).toReal

noncomputable def realFailureRatio (M : ℕ) (ε : ℝ) (k : ℕ) : ℝ :=
  (∑ g, ENNReal.ofReal (D.ω k g) * D.law k g (D.realFailure M ε k g)).toReal /
    (D.totalMass k).toReal

/-- The remaining geometric assertion is a discovery in the same original
failed packet. It has fixed slack, so its witness can be rounded measurably. -/
def SlackDiscovery (M : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ φ : ℕ → ℕ,
    Tendsto φ atTop atTop → (∀ k, δ ≤ D.rationalFailureRatio M ε (φ k)) →
    ∃ (k : ℕ) (i : Fin (D.n (φ k))) (p : α × ℝ) (P : RowPolynomial),
      D.incidence (φ k) i p ∧ ¬ D.rationalFit M ε (φ k) i p ∧
      FitsWith (D.E (φ k) (D.γ (φ k) i)) (D.row (φ k) (D.γ (φ k) i)) (D.I (φ k) i)
        M (D.N (φ k) ^ (ε / 2)) (D.h (φ k) ^ M / 2)
          (D.h (φ k) * D.N (φ k) ^ (-(ε / 2))) p P

/-- Slack discovery contradicts every fixed positive relative failure tail. -/
theorem rationalFailureRatio_tendsto (M : ℕ) (hN : ∀ k, 2 ≤ D.N k)
    (hh : ∀ k, 0 < D.h k) (hI : ∀ k i, D.I k i ⊆ Icc (0 : ℝ) 1)
    (hdiscover : D.SlackDiscovery M) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (D.rationalFailureRatio M ε) atTop (nhds 0) := by
  apply tendsto_zero_of_no_dense_subsequence _ (fun k =>
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  intro δ hδ φ hφ hdense
  obtain ⟨k, i, p, P, hp, hbad, hfit⟩ := hdiscover ε hε δ hδ φ hφ hdense
  have hN1 : 1 < D.N (φ k) := by linarith [hN (φ k)]
  have hC : D.N (φ k) ^ (ε / 2) < D.N (φ k) ^ ε :=
    Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith)
  have hδ' : D.h (φ k) ^ M / 2 < D.h (φ k) ^ M := by
    have := pow_pos (hh (φ k)) M
    linarith
  have hτ : D.h (φ k) * D.N (φ k) ^ (-ε) ≤
      D.h (φ k) * D.N (φ k) ^ (-(ε / 2)) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)) (hh (φ k)).le
  have hfit' := hfit.mono (Subset.rfl) (Subset.rfl) le_rfl le_rfl le_rfl hτ
  apply hbad
  exact hfit'.rational_of_slack
    (fun t ht => ⟨by linarith [(hI _ _ ht).1], (hI _ _ ht).2⟩)
    (abs_le.mpr ⟨by linarith [(hI _ _ hp.2).1], (hI _ _ hp.2).2⟩) hC hδ'

/-- The actual existential failure set is controlled by the measurable rational
failure set, using the original weighted masses in both denominators. -/
theorem realFailureRatio_tendsto (M : ℕ) {ε : ℝ}
    (hfinite : ∀ k g, D.ρ k g univ ≠ ⊤)
    (hlim : Tendsto (D.rationalFailureRatio M ε) atTop (nhds 0)) :
    Tendsto (D.realFailureRatio M ε) atTop (nhds 0) := by
  refine squeeze_zero (fun k => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun k => ?_) hlim
  apply div_le_div_of_nonneg_right _ ENNReal.toReal_nonneg
  apply ENNReal.toReal_mono
  · apply ENNReal.sum_ne_top.mpr
    intro g hg
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ne_top_of_le_ne_top (hfinite k g)
    exact (Measure.restrict_le_self (s := D.E k g) (D.rationalFailure M ε k g)).trans (measure_mono (subset_univ _))
  · exact Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl
      (measure_mono (D.realFailure_subset_rationalFailure M ε k g))

end QualificationTable

end Submission.Obl.k4_scalar_grid_polynomial_qualification
