import Submission.Obl.k4_homogeneous_native_pair_preparation.NativeExtrapolation

namespace Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux

open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split (I)

abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev PairPoint := Trajectory × (ℝ × ℝ)

def coarseIdx {T s : ℕ} (j : Fin (2 ^ (T + s))) : Fin (2 ^ T) := nativeCoarseIndex j

/-- Only the old source data needed by the native pair argument. -/
structure Data where
  W : ℕ
  T : ℕ
  s : ℕ
  C : ℕ
  γ : Fin C → Fin W
  j : Fin C → Fin (2 ^ (T + s))
  R : Fin C → MvPolynomial (Fin 4) ℝ
  A : Fin C → Set Trajectory
  F : Fin C → Set Incidence
  B : Fin W → ℝ
  Good : Fin W → Set Incidence
  κ₀ : ℝ
  dfl : ℝ

namespace Data

def Sb (D : Data) (b : Fin D.C) : Set Incidence :=
  D.F b ∩ {p | p.2 < (((D.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (D.T + D.s)}

def blk (D : Data) (j : Fin (2 ^ D.T)) : Set ℝ :=
  Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ D.T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T)

theorem blk_meas (D : Data) (j : Fin (2 ^ D.T)) : MeasurableSet (D.blk j) := measurableSet_Icc

/-- The source facts consumed by the original-law pair measure proof. -/
structure Hyp (D : Data) (E : Fin D.W → Set Incidence) : Prop where
  κ₀one : 1 ≤ D.κ₀
  Bpos : ∀ γ, 0 < D.B γ
  Rdeg : ∀ b, (D.R b).totalDegree ≤ 2
  sel : ∀ b {p}, p ∈ D.F b →
    p ∈ E (D.γ b) ∧ p.1 ∈ D.A b ∧
      p.2 ∈ I (D.T + D.s) (D.j b) ∧
      D.B (D.γ b) / D.κ₀ ≤
        |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (D.R b))|
  Sb_meas : ∀ b, MeasurableSet (D.Sb b)
  Sb_disjoint : ∀ {b b'}, b ≠ b' → D.γ b = D.γ b' → Disjoint (D.Sb b) (D.Sb b')
  Sb_coarse : ∀ b {p}, p ∈ D.Sb b →
    p.2 ∈ Ico (((coarseIdx (D.j b) : ℕ) : ℝ) / (2 : ℝ) ^ D.T)
      ((((coarseIdx (D.j b) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T)
  Good_meas : ∀ γ, MeasurableSet (D.Good γ)

end Data
end Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux
