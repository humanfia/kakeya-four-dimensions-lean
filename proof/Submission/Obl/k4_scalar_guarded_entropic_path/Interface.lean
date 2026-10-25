/-
Adapted from this LOT tree, obligation o168, session x0569, branch x0569,
Submission/Obl/k4_scalar_guarded_tangent_preparation/Interface.lean.
The original source is work of this tree; its provenance comments are retained.
-/
/-
Readable names for the frozen statement of o168.

Adapted from this LOT tree (g-oai-074), obligation o134
`k4_scalar_guarded_tangent_obstruction`, branch x0484 (session x0484, own code of
this tree), files `Submission/Obl/k4_scalar_guarded_tangent_obstruction/Prepared.lean`
and `.../Tangent.lean`, renamed into this namespace. The scalar exact-data vocabulary
(`Code`, `Exact`, `ChartData`, `Chart`, `Critical`, ...) is imported from the accepted
obligation o133.
-/
import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

abbrev Code := Split.Code

/-- Trajectory coefficients `(i, (y₀, y₁, x₀, x₁, x₂))`. -/
abbrev Coeff := ℕ × (Fin 5 → ℝ)

/-- Incidences `(trajectory, time)`. -/
abbrev Incidence := Coeff × ℝ

namespace Code

abbrev W (p : Code) : ℕ → ℕ := p.1
abbrev N (p : Code) : ℕ → ℝ := p.2.1
abbrev K (p : Code) : ℕ → ℝ := p.2.2.1
abbrev M (p : Code) : ℕ := p.2.2.2.1
abbrev D (p : Code) : ℕ := p.2.2.2.2.1
abbrev L (p : Code) : ℝ := p.2.2.2.2.2.1
abbrev d (p : Code) : ℝ := p.2.2.2.2.2.2.1
abbrev S (p : Code) : ℝ := p.2.2.2.2.2.2.2.1
abbrev U (p : Code) : ℝ := p.2.2.2.2.2.2.2.2.1
abbrev weight (p : Code) : (k : ℕ) → Fin (p.1 k) → ℝ := p.2.2.2.2.2.2.2.2.2.1
abbrev prior (p : Code) : (k : ℕ) → Fin (p.1 k) → MeasureTheory.Measure Coeff :=
  p.2.2.2.2.2.2.2.2.2.2.1
abbrev support (p : Code) : (k : ℕ) → Fin (p.1 k) → Set Incidence :=
  p.2.2.2.2.2.2.2.2.2.2.2.1
abbrev density (p : Code) : (k : ℕ) → Fin (p.1 k) → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal :=
  p.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev angularDensity (p : Code) :
    (k : ℕ) → Fin (p.1 k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal :=
  p.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev profile (p : Code) : ℝ → ℝ := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Code

/-- A full original-coordinate true layer: its block exponent, its charts with
worlds, blocks, full trajectory assignments, selected incidence witnesses, affine
centres, widths, quadratic tests, and the list at the original terminal
observation. -/
def Layer (w : ℕ) : Type :=
  Σ T : ℕ, Σ n : ℕ,
    (Fin n → Fin w) × (Fin n → Fin (2 ^ T)) ×
    (Fin n → Set Coeff) × (Fin n → Set Incidence) ×
    (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) ×
    (Fin n → MvPolynomial (Fin 2) ℝ) ×
    (Fin w → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n))

namespace Layer

abbrev T {w : ℕ} (a : Layer w) : ℕ := a.1
abbrev n {w : ℕ} (a : Layer w) : ℕ := a.2.1
abbrev world {w : ℕ} (a : Layer w) : Fin a.n → Fin w := a.2.2.1
abbrev block {w : ℕ} (a : Layer w) : Fin a.n → Fin (2 ^ a.T) := a.2.2.2.1
abbrev assignment {w : ℕ} (a : Layer w) : Fin a.n → Set Coeff := a.2.2.2.2.1
abbrev witness {w : ℕ} (a : Layer w) : Fin a.n → Set Incidence := a.2.2.2.2.2.1
abbrev u {w : ℕ} (a : Layer w) : Fin a.n → ℝ := a.2.2.2.2.2.2.1
abbrev v {w : ℕ} (a : Layer w) : Fin a.n → ℝ := a.2.2.2.2.2.2.2.1
abbrev width {w : ℕ} (a : Layer w) : Fin a.n → ℝ := a.2.2.2.2.2.2.2.2.1
abbrev graph {w : ℕ} (a : Layer w) : Fin a.n → MvPolynomial (Fin 2) ℝ :=
  a.2.2.2.2.2.2.2.2.2.1
abbrev list {w : ℕ} (a : Layer w) :
    Fin w → ((Fin 2 → ℝ) × ℤ) → Finset (Fin a.n) := a.2.2.2.2.2.2.2.2.2.2

/-- Assemble a layer from its fields. -/
abbrev mk {w : ℕ} (T n : ℕ) (γ : Fin n → Fin w) (j : Fin n → Fin (2 ^ T))
    (A : Fin n → Set Coeff) (C : Fin n → Set Incidence) (u v J : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (Λ : Fin w → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)) : Layer w :=
  ⟨T, n, γ, j, A, C, u, v, J, P, Λ⟩

end Layer

/-- Base bins of an incidence, at width `N ^ (-r)`. -/
def baseBin (N r : ℝ) (p : Incidence) (e : Fin 2) : ℤ :=
  ⌊(![p.2, Split.y p.1 p.2] : Fin 2 → ℝ) e / (N ^ (-r))⌋

/-- Hidden bin of an incidence, at width `N ^ (-s)`. -/
def hiddenBin (N s : ℝ) (p : Incidence) : ℤ :=
  ⌊Split.x p.1 p.2 / (N ^ (-s))⌋

/-- Velocity bin, at width `N ^ (-b)`. -/
def velocityBin (N b : ℝ) (v : ℝ) : ℤ :=
  ⌊v / (N ^ (-b))⌋


end

end Submission.Obl.k4_scalar_guarded_entropic_path
