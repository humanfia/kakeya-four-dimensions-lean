import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open MeasureTheory Set
open scoped ENNReal

abbrev Coeff := Fin 5 → ℝ
abbrev Traj := ℕ × Coeff
abbrev Obs := (Fin 2 → ℝ) × ℤ
abbrev AugObs := Obs × ℤ

def Subpower (N K : ℕ → ℝ) : Prop :=
  (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε

noncomputable def Noise (σ : ℝ) : Measure Coeff :=
  Measure.pi (fun _ : Fin 5 => ENNReal.ofReal (σ⁻¹) • volume.restrict (Icc 0 σ))

noncomputable def MarkedPrior (σ : ℝ) (H : ℕ) (b₀ : Fin H → Coeff)
    (w : Fin H → ℝ) : Measure Traj :=
  ∑ j, ENNReal.ofReal (w j) •
    Measure.map (fun u : Coeff => ((j : ℕ), b₀ j + u)) (Noise σ)

def timeCell (J : ℕ) (z : Fin J) : Set ℝ :=
  Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))

def MarkedEvent (H J : ℕ) (mark : Fin H → Fin J → Bool) : Set (Traj × ℝ) :=
  {p | ∃ j : Fin H, p.1.1 = (j : ℕ) ∧
    ∃ z : Fin J, mark j z = true ∧ p.2 ∈ timeCell J z}

noncomputable def MarkedLaw (σ : ℝ) (H J : ℕ) (b₀ : Fin H → Coeff)
    (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) : Measure (Traj × ℝ) :=
  ((MarkedPrior σ H b₀ w).prod volume).restrict (MarkedEvent H J mark)

def curveX {α : Type*} (b : α → Coeff) (l : α) (t : ℝ) : ℝ :=
  b l 2 + t * b l 3 + t ^ 2 * b l 4

def curveY {α : Type*} (b : α → Coeff) (l : α) (t : ℝ) : ℝ :=
  b l 0 + t * b l 1

noncomputable def meshCode {α : Type*} (b : α → Coeff) (σ : ℝ)
    (p : α × ℝ) : Fin 2 → ℤ :=
  ![⌊p.2 / σ⌋, ⌊curveY b p.1 p.2 / σ⌋]

noncomputable def observation (N r : ℝ) (p : Traj × ℝ) : Obs :=
  (![p.2, curveY Prod.snd p.1 p.2], ⌊curveX Prod.snd p.1 p.2 / (N ^ (-r))⌋)

noncomputable def velocityObservation (N r u : ℝ) (p : Traj × ℝ) : AugObs :=
  (observation N r p, ⌊p.1.2 1 / (N ^ (-u))⌋)

noncomputable def baseRef : Measure Obs :=
  volume.prod (Measure.count : Measure ℤ)

noncomputable def jointRef : Measure AugObs := baseRef.prod Measure.count

def MeshInput (N K d s m S U : ℝ) (α : Type) [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (b : α → Coeff) (c : ℝ)
    (angular : Bool) : Prop :=
  let a := N ^ (-s)
  let σ := N ^ (-m)
  Measurable b ∧ IsProbabilityMeasure ν ∧
  μ ≤ ENNReal.ofReal K • (ν.prod volume) ∧
  μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 ∧
  ENNReal.ofReal (K⁻¹) ≤ μ univ ∧
  (∀ l i, |b l i| ≤ K) ∧
  (∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s →
    μ {p | meshCode b σ p = q ∧ ⌊curveX b p.1 p.2 / (N ^ (-r))⌋ = j} ≤
      ENNReal.ofReal (K * σ ^ 2 * c * (N ^ (-r)) ^ d)) ∧
  (∃ F : Finset ((Fin 2 → ℤ) × ℤ),
    (F.card : ℝ) * σ ^ 2 ≤ K * c⁻¹ * a ^ (-d) ∧
      ∀ᵐ p ∂μ, (meshCode b σ p, ⌊curveX b p.1 p.2 / a⌋) ∈ F) ∧
  (angular = true → ∀ (r : ℝ) (q : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U →
    μ {p | meshCode b σ p = q ∧ ⌊curveX b p.1 p.2 / a⌋ = j ∧
      ⌊b p.1 1 / (N ^ (-r))⌋ = k} ≤
        ENNReal.ofReal (K * σ ^ 2 * c * a ^ d * N ^ (-S * r)))

def Tables (N K m : ℝ) (M H J : ℕ) (b₀ : Fin H → Coeff)
    (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) : Prop :=
  1 ≤ J ∧ (H : ℝ) ≤ N ^ (M : ℝ) ∧ (J : ℝ) ≤ N ^ (M : ℝ) ∧
  1 ≤ (J : ℝ) * N ^ (-m) ∧ (J : ℝ) * N ^ (-m) ≤ 2 ∧
  (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ (∀ j e, |b₀ j e| ≤ K) ∧
  ENNReal.ofReal (K⁻¹) ≤ MarkedLaw (N ^ (-m)) H J b₀ w mark univ

def Coupling (N K s m : ℝ) (α : Type) [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (b : α → Coeff) (H J : ℕ)
    (tag : α → Fin H) (b₀ : Fin H → Coeff) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) : Prop :=
  Measurable tag ∧
  (∀ j, ENNReal.ofReal (w j) = ν {l | tag l = j}) ∧
  (∀ l e, |b l e - b₀ (tag l) e| ≤ N ^ (-10 * (m + s + 1))) ∧
  (∀ j z, mark j z = true →
    ENNReal.ofReal (w j / ((J : ℝ) * K)) ≤
      μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z})

def RawEstimates (N K d s m S U c : ℝ) (angular : Bool)
    (μ : Measure (Traj × ℝ)) : Prop :=
  (∀ r : ℝ, 0 ≤ r → r ≤ s → ∃ g : Obs → ℝ≥0∞,
    Measurable g ∧ μ.map (observation N r) = baseRef.withDensity g ∧
      ∀ᵐ z ∂baseRef, g z ≤ ENNReal.ofReal (K * c * N ^ (-d * r))) ∧
  (∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) →
    ∃ G : AugObs → ℝ≥0∞,
      Measurable G ∧ μ.map (velocityObservation N r u) = jointRef.withDensity G ∧
      (∀ᵐ z ∂jointRef,
        G z ≤ ENNReal.ofReal (K * c * N ^ (-d * r) * min 1 (N ^ (m - u)))) ∧
      (r = s → angular = true → 0 < u → u ≤ U → ∀ᵐ z ∂jointRef,
        G z ≤ ENNReal.ofReal (K * c * N ^ (-d * s - S * u)))) ∧
  (∃ B : Set Obs, MeasurableSet B ∧
    baseRef B ≤ ENNReal.ofReal (K * c⁻¹ * N ^ (d * s)) ∧
      ∀ᵐ p ∂μ, observation N s p ∈ B)

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
