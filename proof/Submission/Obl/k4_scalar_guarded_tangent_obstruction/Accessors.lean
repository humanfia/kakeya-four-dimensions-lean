import Submission.Obl.k4_scalar_guarded_tangent_obstruction.Defs

namespace Submission.Obl.k4_scalar_guarded_tangent_obstruction

namespace RawData

abbrev N (p : RawData) : ℕ → ℝ := p.2.1

abbrev K (p : RawData) : ℕ → ℝ := p.2.2.1

abbrev M (p : RawData) : ℕ := p.2.2.2.1

abbrev D (p : RawData) : ℕ := p.2.2.2.2.1

abbrev L (p : RawData) : ℝ := p.2.2.2.2.2.1

abbrev d (p : RawData) : ℝ := p.2.2.2.2.2.2.1

abbrev S (p : RawData) : ℝ := p.2.2.2.2.2.2.2.1

abbrev U (p : RawData) : ℝ := p.2.2.2.2.2.2.2.2.1

abbrev weight (p : RawData) : (k : ℕ) → Fin (p.1 k) → ℝ := p.2.2.2.2.2.2.2.2.2.1

abbrev prior (p : RawData) : (k : ℕ) → Fin (p.1 k) → MeasureTheory.Measure Coeff := p.2.2.2.2.2.2.2.2.2.2.1

abbrev support (p : RawData) : (k : ℕ) → Fin (p.1 k) → Set Incidence := p.2.2.2.2.2.2.2.2.2.2.2.1

abbrev density (p : RawData) : (k : ℕ) → Fin (p.1 k) → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal := p.2.2.2.2.2.2.2.2.2.2.2.2.1

abbrev angularDensity (p : RawData) : (k : ℕ) → Fin (p.1 k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal := p.2.2.2.2.2.2.2.2.2.2.2.2.2.1

abbrev profile (p : RawData) : ℝ → ℝ := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end RawData

end Submission.Obl.k4_scalar_guarded_tangent_obstruction
