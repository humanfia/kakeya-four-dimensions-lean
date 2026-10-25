import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces

/-! Shared scalar interfaces, imported from the accepted critical-extremizer module. -/

namespace Submission.Obl.k4_scalar_guarded_tangent_obstruction

noncomputable section

abbrev Coeff := ℕ × (Fin 5 → ℝ)

abbrev Incidence := Coeff × ℝ

abbrev RawData := Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Code

def mu : (p:RawData) → (k:ℕ) → Fin ((p).1 k) → MeasureTheory.Measure ((ℕ×(Fin 5 → ℝ))×ℝ) :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.mu

def y : (ℕ×(Fin 5 → ℝ)) → ℝ → ℝ :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y

def x : (ℕ×(Fin 5 → ℝ)) → ℝ → ℝ :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.x

def I : (T:ℕ) → Fin (2 ^ T) → Set ℝ :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.I

def Format : (n:ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Format

def Exact : RawData → Prop :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Exact

def ChartData : (p:RawData) → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → (k:ℕ) → (T n:ℕ) → (Fin n → Fin ((p).1 k)) → (Fin n → Fin (2 ^ T)) → (Fin n → Set (ℕ×(Fin 5 → ℝ))) → (Fin n → Set ((ℕ×(Fin 5 → ℝ))×ℝ)) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → MvPolynomial (Fin 2) ℝ) → (Fin ((p).1 k) → ((Fin 2 → ℝ)×ℤ) → Finset (Fin n)) → Prop :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.ChartData

def Chart : RawData → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → ℕ → Prop :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Chart

def Known : RawData → ℝ → ℝ → ℝ → Prop :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Known

def Cost : RawData → ℝ → Prop :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Cost

def Horizon : RawData → ℝ :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Horizon

def Initial : Prop :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Initial

def Refinement : RawData → RawData → ℝ → ℝ → ℝ → Prop :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Refinement

def Calculus : Prop :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Calculus

def STI : Prop :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.STI

def Critical : Prop :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Critical

end

end Submission.Obl.k4_scalar_guarded_tangent_obstruction
