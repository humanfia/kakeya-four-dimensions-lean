import Mathlib
import ChallengeDeps

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_oss_unit_decay

noncomputable def mix (α β : Measure ℝ) : Measure ℝ :=
  Measure.map (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
    (q.1.1 * q.1.2 - q.2.1 * q.2.2) / 4) ((α.prod β).prod (α.prod β))

noncomputable def halfLaw (α : Measure ℝ) : Measure ℝ :=
  Measure.map (fun x : ℝ => x / 2) α

noncomputable def collision (δ : ℝ) (α : Measure ℝ) : ℝ≥0∞ :=
  (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ δ}

noncomputable def projectionCollision (δ : ℝ) (α β : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, ((α.prod α).prod (α.prod α))
    {q : (ℝ × ℝ) × (ℝ × ℝ) |
      |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ} ∂(β.prod β)

/-- An interval bound, including radii larger than one. -/
def IntervalCap (α : Measure ℝ) (δ s A : ℝ) : Prop :=
  ∀ x u : ℝ, δ ≤ u → α (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (A * u ^ s)

noncomputable def phase (ξ t : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * ξ * t : ℝ) : ℂ) * Complex.I)

end Submission.Obl.k4_oss_unit_decay
