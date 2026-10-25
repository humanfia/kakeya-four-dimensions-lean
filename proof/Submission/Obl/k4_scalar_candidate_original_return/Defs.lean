import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_candidate_original_return

/-! Readable names for the accepted scalar interfaces. -/

abbrev Code := k4_scalar_linear_critical_extremizers.Split.Code
noncomputable abbrev W := k4_scalar_linear_critical_extremizers.Split.W
noncomputable abbrev N := k4_scalar_linear_critical_extremizers.Split.N
noncomputable abbrev K := k4_scalar_linear_critical_extremizers.Split.K
noncomputable abbrev M := k4_scalar_linear_critical_extremizers.Split.M
noncomputable abbrev D := k4_scalar_linear_critical_extremizers.Split.D
noncomputable abbrev L := k4_scalar_linear_critical_extremizers.Split.L
noncomputable abbrev d := k4_scalar_linear_critical_extremizers.Split.d
noncomputable abbrev S := k4_scalar_linear_critical_extremizers.Split.S
noncomputable abbrev U := k4_scalar_linear_critical_extremizers.Split.U
noncomputable abbrev ω := k4_scalar_linear_critical_extremizers.Split.ω
noncomputable abbrev ν := k4_scalar_linear_critical_extremizers.Split.ν
noncomputable abbrev E := k4_scalar_linear_critical_extremizers.Split.E
noncomputable abbrev g := k4_scalar_linear_critical_extremizers.Split.g
noncomputable abbrev G := k4_scalar_linear_critical_extremizers.Split.G
noncomputable abbrev f := k4_scalar_linear_critical_extremizers.Split.f
noncomputable abbrev mu := k4_scalar_linear_critical_extremizers.Split.mu
noncomputable abbrev y := k4_scalar_linear_critical_extremizers.Split.y
noncomputable abbrev x := k4_scalar_linear_critical_extremizers.Split.x
noncomputable abbrev I := k4_scalar_linear_critical_extremizers.Split.I
noncomputable abbrev Format := k4_scalar_linear_critical_extremizers.Split.Format
noncomputable abbrev Exact := k4_scalar_linear_critical_extremizers.Split.Exact
noncomputable abbrev ChartData := k4_scalar_linear_critical_extremizers.Split.ChartData
noncomputable abbrev Chart := k4_scalar_linear_critical_extremizers.Split.Chart
noncomputable abbrev STI := k4_scalar_linear_critical_extremizers.Split.STI

abbrev Line := ℕ × (Fin 5 → ℝ)
abbrev Inc := Line × ℝ
abbrev Base := Fin 2 → ℝ
abbrev Poly := MvPolynomial (Fin 2) ℝ

/-- A true layer stores its original selected incidences and terminal lists. -/
abbrev Layer (w : ℕ) := Σ T : ℕ, Σ n : ℕ,
  (Fin n → Fin w) × (Fin n → Fin (2 ^ T)) × (Fin n → Set Line) ×
  (Fin n → Set Inc) × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) ×
  (Fin n → Poly) × (Fin w → (Base × ℤ) → Finset (Fin n))

namespace Layer

def T {w : ℕ} (a : Layer w) : ℕ := a.1
def n {w : ℕ} (a : Layer w) : ℕ := a.2.1
def world {w : ℕ} (a : Layer w) : Fin a.n → Fin w := a.2.2.1
def time {w : ℕ} (a : Layer w) : Fin a.n → Fin (2 ^ a.T) := a.2.2.2.1
def prior {w : ℕ} (a : Layer w) : Fin a.n → Set Line := a.2.2.2.2.1
def selected {w : ℕ} (a : Layer w) : Fin a.n → Set Inc := a.2.2.2.2.2.1
def u {w : ℕ} (a : Layer w) : Fin a.n → ℝ := a.2.2.2.2.2.2.1
def v {w : ℕ} (a : Layer w) : Fin a.n → ℝ := a.2.2.2.2.2.2.2.1
def width {w : ℕ} (a : Layer w) : Fin a.n → ℝ := a.2.2.2.2.2.2.2.2.1
def poly {w : ℕ} (a : Layer w) : Fin a.n → Poly := a.2.2.2.2.2.2.2.2.2.1
def lists {w : ℕ} (a : Layer w) : Fin w → (Base × ℤ) → Finset (Fin a.n) :=
  a.2.2.2.2.2.2.2.2.2.2

end Layer

end Submission.Obl.k4_scalar_candidate_original_return
