import Mathlib
import ChallengeDeps
import Submission.Obl.k4_crop_angular_finite_tail.Assembly
set_option linter.unusedVariables false

/-!
# `Submission.k4_crop_angular_finite_tail`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_crop_angular_finite_tail`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_crop_angular_finite_tail/`
belong to this obligation.
-/

theorem Submission.k4_crop_angular_finite_tail : ∀ (n r u₀ u : ℝ) (ν₀ : MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E₀ : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (w : ℕ) (p : Fin w → ℝ) (q : Fin w → (Fin 4 → ℤ)) (ν : Fin w → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : Fin w → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (g : Fin w → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal) (H : ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal), (fun (scale : ℝ → ℝ) => (fun (cell : (Fin 4 → ℤ) → Set (ℕ × (Fin 6 → ℝ))) => (fun (crop : (Fin 4 → ℤ) → (ℕ × (Fin 6 → ℝ)) → (ℕ × (Fin 6 → ℝ))) => (fun (cropInc : (Fin 4 → ℤ) → ((ℕ × (Fin 6 → ℝ)) × ℝ) → ((ℕ × (Fin 6 → ℝ)) × ℝ)) => (fun (selected : MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) => (fun (obs : ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → (EuclideanSpace ℝ (Fin 3) × ℤ)) => (fun (jointObs : ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ))) => (fun (baseRef : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3) × ℤ)) => (fun (jointRef : MeasureTheory.Measure ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ))) => 2 ≤ n → 0 ≤ r → r ≤ 1 → 0 ≤ u₀ → 0 ≤ u → MeasureTheory.IsProbabilityMeasure ν₀ → MeasurableSet E₀ → E₀ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 → Function.Injective q → (∀ γ, 0 < p γ ∧ ν γ = (ENNReal.ofReal (p γ))⁻¹ • MeasureTheory.Measure.map (crop (q γ)) (ν₀.restrict (cell (q γ))) ∧ E γ = cropInc (q γ) '' (E₀ ∩ (cell (q γ) ×ˢ Set.univ))) → Measurable H → MeasureTheory.Measure.map (jointObs r (u₀ + u)) (selected ν₀ E₀) = jointRef.withDensity H → (∀ γ, Measurable (g γ) ∧ MeasureTheory.Measure.map (jointObs r u) (selected (ν γ) (E γ)) = jointRef.withDensity (g γ)) → ∀ lo hi δ : ℝ, 0 < lo → 0 < hi → 0 < δ → δ ≤ 1 → (∑ γ, ENNReal.ofReal (p γ) * (selected (ν γ) (E γ)) {x | g γ ((jointObs r u) x) < ENNReal.ofReal ((scale u₀ ^ 2 / p γ) * δ * lo) ∨ ENNReal.ofReal ((scale u₀ ^ 2 / p γ) * hi / δ) < g γ ((jointObs r u) x)}) ≤ (selected ν₀ E₀) {x | H (jointObs r (u₀ + u) x) < ENNReal.ofReal lo ∨ ENNReal.ofReal hi < H (jointObs r (u₀ + u) x)} + ENNReal.ofReal (32 * δ)) (baseRef.prod MeasureTheory.Measure.count)) (MeasureTheory.volume.prod MeasureTheory.Measure.count)) (fun v s x => (obs v x, fun j : Fin 2 => ⌊(WithLp.toLp 2 ![x.1.2 3, x.1.2 4]) j / scale s⌋))) (fun v x => ((WithLp.toLp 2 ![x.2, x.1.2 0 + x.2 * x.1.2 3, x.1.2 1 + x.2 * x.1.2 4] : EuclideanSpace ℝ (Fin 3)), ⌊(x.1.2 2 + x.2 * x.1.2 5) / scale v⌋))) (fun v A => (v.prod MeasureTheory.volume).restrict A)) (fun z x => (crop z x.1, x.2))) (fun z l => (l.1, ![l.2 0 / scale u₀ - (z 0 : ℝ), l.2 1 / scale u₀ - (z 1 : ℝ), l.2 2, l.2 3 / scale u₀ - (z 2 : ℝ), l.2 4 / scale u₀ - (z 3 : ℝ), l.2 5]))) (fun z => {l | ⌊l.2 0 / scale u₀⌋ = z 0 ∧ ⌊l.2 1 / scale u₀⌋ = z 1 ∧ ⌊l.2 3 / scale u₀⌋ = z 2 ∧ ⌊l.2 4 / scale u₀⌋ = z 3})) (fun v => (2 : ℝ) ^ (-(⌊v * Real.log n / Real.log 2⌋ : ℤ))) := by
  intro n r u₀ u ν₀ E₀ w p q ν E g H
  dsimp only
  intro hn hr hr₁ hu₀ hu hprob hE₀ htime hq hcrop hH hsource hg lo hi δ hlo hhi hδ hδ₁
  letI : MeasureTheory.IsProbabilityMeasure ν₀ := hprob
  exact Submission.Obl.k4_crop_angular_finite_tail.angular_finite_tail
    n r u₀ u ν₀ E₀ w p q ν E g H (by linarith) hu₀ hu hE₀ htime hq hcrop hH hsource hg
    lo hi δ hlo hhi hδ
