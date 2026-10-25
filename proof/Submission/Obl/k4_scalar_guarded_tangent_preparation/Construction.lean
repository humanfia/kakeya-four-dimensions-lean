import Submission.Obl.k4_scalar_guarded_tangent_preparation.RawGeometry

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

/-- The geometric construction owns the genuine measured paths, all
potential-parent masks and the low-information window. The original sample
guard is already imposed on each chosen exact parent. -/
def EntropicPathConstruction : Prop :=
  Split.Initial → Split.Calculus → Split.Critical →
  ∃ (p : ℕ → Code) (sample : ℕ → ℕ) (scale H buffer B : ℕ → ℝ)
    (M count : ℕ → ℕ) (node : (k : ℕ) → ℝ → Fin (count k))
    (depth time : (k : ℕ) → Fin (count k) → ℝ)
    (layers : (k : ℕ) → Fin (count k) → Layer ((p k).W (sample k)))
    (σ : (k : ℕ) → Fin ((p k).W (sample k)) → MeasureTheory.Measure Incidence)
    (d κ S : ℝ),
    RawGeometry p sample scale H buffer B M count node depth time layers σ d κ S ∧
    ReferenceLaws (fun k => (p k).N (sample k) ^ scale k) B d S
      (fun k => (p k).W (sample k)) (fun k => (p k).weight (sample k)) σ

/-- A finite reference code gives one common likelihood mask. Its
predeletion velocity marginal is smoothed once to supply immutable palettes
for every real positive bin width on compact exponent ranges. -/
def ReferenceCapPreparation : Prop :=
  ∀ (N B : ℕ → ℝ) (d S : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (σ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Incidence),
  ReferenceLaws N B d S W ω σ →
  ∃ (K : ℕ → ℝ)
    (ρ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Incidence)
    (π : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ℝ),
    (∀ k g, ρ k g ≤ σ k g) ∧
    (∀ k, ENNReal.ofReal (1 / 2 : ℝ) *
      (∑ g, ENNReal.ofReal (ω k g) * σ k g Set.univ) ≤
      ∑ g, ENNReal.ofReal (ω k g) * ρ k g Set.univ) ∧
    RectangularCaps N K d S W ρ π

/-- Simultaneous finite-layer duration pruning and quadratic graph
comparison complete the tangent charts using full original priors. The
current caps are preserved by restriction; the earlier true witnesses and
terminal lists are retained on the surviving rows. -/
def FullPriorLayerCompletion : Prop :=
  ∀ (p : ℕ → Code) (sample : ℕ → ℕ) (scale H buffer B : ℕ → ℝ)
    (M count : ℕ → ℕ) (node : (k : ℕ) → ℝ → Fin (count k))
    (depth time : (k : ℕ) → Fin (count k) → ℝ)
    (layers : (k : ℕ) → Fin (count k) → Layer ((p k).W (sample k)))
    (σ : (k : ℕ) → Fin ((p k).W (sample k)) → MeasureTheory.Measure Incidence)
    (d κ S : ℝ),
  RawGeometry p sample scale H buffer B M count node depth time layers σ d κ S →
  ∀ (K : ℕ → ℝ)
    (ρ : (k : ℕ) → Fin ((p k).W (sample k)) → MeasureTheory.Measure Incidence)
    (π : (k : ℕ) → Fin ((p k).W (sample k)) → MeasureTheory.Measure ℝ),
  (∀ k g, ρ k g ≤ σ k g) →
  (∀ k, ENNReal.ofReal (2 * (H k)⁻¹) ≤
    ∑ g, ENNReal.ofReal ((p k).weight (sample k) g) * ρ k g Set.univ) →
  RectangularCaps (fun k => (p k).N (sample k) ^ scale k) K d S
    (fun k => (p k).W (sample k)) ρ π → GuardedPrepared

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
