import Mathlib
import ChallengeDeps
import Submission.Obl.k4_oss_collision_iteration.Numerics
import Submission.Obl.k4_oss_collision_iteration.Growth
set_option linter.unusedVariables false

/-!
# Collision flattening along a finite mixing tower

Projection flattening contracts collision probabilities above a threshold.
A universal growth bound controls steps that start below that threshold.
-/

open MeasureTheory
open scoped ENNReal

namespace Submission.Obl.k4_oss_collision_iteration

theorem _root_.Submission.k4_oss_collision_iteration : (∀ δ : ℝ, 0 < δ → ∀ α β : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure α → MeasureTheory.IsProbabilityMeasure β → ∀ ω : MeasureTheory.Measure ℝ, ω = MeasureTheory.Measure.map (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q.1.1 * q.1.2 - q.2.1 * q.2.2) / 4) ((α.prod β).prod (α.prod β)) → (ω.prod ω) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} ≤ 3 * MeasureTheory.lintegral (β.prod β) (fun p : ℝ × ℝ => ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) | |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ})) → (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ c ε δ₀ : ℝ, 0 < c ∧ 0 < ε ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ α β : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure α → MeasureTheory.IsProbabilityMeasure β → α (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → β (Set.Icc (1 : ℝ) 2)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → α (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → β (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) → ENNReal.ofReal (δ ^ (1 - γ)) ≤ (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ} → MeasureTheory.lintegral (β.prod β) (fun p : ℝ × ℝ => ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) | |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ}) ≤ ENNReal.ofReal (δ ^ c) * (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}) → ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ m : ℕ, ∃ η r₀ : ℝ, 0 < η ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ μ : Fin (m + 2) → MeasureTheory.Measure ℝ, (∀ j : Fin (m + 2), MeasureTheory.IsProbabilityMeasure (μ j)) → (∀ j : Fin (m + 2), (μ j) (Set.Icc (1 : ℝ) 2)ᶜ = 0) → (∀ j : Fin (m + 2), ∀ x u : ℝ, r ≤ u → u ≤ 1 → (μ j) (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-η) * u ^ s)) → ∀ ν : ℕ → MeasureTheory.Measure ℝ, (∀ k : ℕ, k ≤ m → MeasureTheory.IsProbabilityMeasure (ν k)) → (∀ k : ℕ, k ≤ m → (ν k) (Set.Icc (-1 : ℝ) 1)ᶜ = 0) → (∀ k : ℕ, k ≤ m → ∀ x u : ℝ, r ≤ u → u ≤ 1 → (ν k) (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-η) * u ^ s)) → (∀ k : ℕ, k < m → ν (k + 1) = MeasureTheory.Measure.map (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q.1.1 * q.1.2 - q.2.1 * q.2.2) / 4) (((ν k).prod (μ (Fin.ofNat (m + 2) (k + 1)))).prod ((ν k).prod (μ (Fin.ofNat (m + 2) (k + 1)))))) → ((ν m).prod (ν m)) {p : ℝ × ℝ | |p.1 - p.2| ≤ r} ≤ ENNReal.ofReal (r ^ (1 - γ)) := by
  intro hcs hflat s hs hs1 γ hγ hγ1
  obtain ⟨c, η, R, hc, hη, hR, hflat⟩ :=
    hflat s hs hs1 (γ / 2) (by positivity) (by linarith)
  obtain ⟨m, r₀, hr₀, hr₀R, hiter⟩ :=
    exists_collision_iteration 39 hc hγ hR
  refine ⟨m, η, r₀, hη, hr₀, ?_⟩
  intro r hr hrr μ hμ hμsupp hμfrost ν hν hνsupp hνfrost hrec
  let q : ℕ → ℝ≥0∞ := fun k =>
    ((ν k).prod (ν k)) {p : ℝ × ℝ | |p.1 - p.2| ≤ r}
  apply hiter r hr hrr q
  · have := hν 0 (Nat.zero_le m)
    exact prob_le_one
  · intro k hk
    have := hν k hk.le
    have := hμ (Fin.ofNat (m + 2) (k + 1))
    simpa only [ENNReal.ofReal_ofNat] using
      collision_mix_le hr (ν k) (μ (Fin.ofNat (m + 2) (k + 1)))
        (hμsupp _) (ν (k + 1)) (hrec k hk)
  · intro k hk hq
    have hprojection := hflat r hr (lt_of_lt_of_le hrr hr₀R)
      (ν k) (μ (Fin.ofNat (m + 2) (k + 1)))
      (hν k hk.le) (hμ _) (hνsupp k hk.le) (hμsupp _)
      (hνfrost k hk.le) (hμfrost _) hq
    calc
      q (k + 1) ≤ 3 * MeasureTheory.lintegral
          ((μ (Fin.ofNat (m + 2) (k + 1))).prod (μ (Fin.ofNat (m + 2) (k + 1))))
          (fun p : ℝ × ℝ => ((ν k).prod (ν k)).prod ((ν k).prod (ν k))
            {a : (ℝ × ℝ) × (ℝ × ℝ) |
              |p.1 * (a.1.1 - a.1.2) - p.2 * (a.2.1 - a.2.2)| ≤ 4 * r}) :=
        hcs r hr (ν k) (μ (Fin.ofNat (m + 2) (k + 1)))
          (hν k hk.le) (hμ _) (ν (k + 1)) (hrec k hk)
      _ ≤ 3 * (ENNReal.ofReal (r ^ c) * q k) := by gcongr
      _ = (3 * ENNReal.ofReal (r ^ c)) * q k := (mul_assoc _ _ _).symm

end Submission.Obl.k4_oss_collision_iteration
