import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_dyadic_crop_worlds

open MeasureTheory Set

noncomputable section

abbrev Coeff := Fin 6 → ℝ
abbrev Line := ℕ × Coeff
abbrev Incident := Line × ℝ
abbrev Label := Fin 4 → ℤ

noncomputable def side (N u : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(⌊u * Real.log N / Real.log 2⌋ : ℤ))

def cell (a : ℝ) (q : Label) : Set Line :=
  {l | ⌊l.2 0 / a⌋ = q 0 ∧ ⌊l.2 1 / a⌋ = q 1 ∧
    ⌊l.2 3 / a⌋ = q 2 ∧ ⌊l.2 4 / a⌋ = q 3}

def cropCoeff (a : ℝ) (q : Label) (x : Coeff) : Coeff :=
  ![x 0 / a - (q 0 : ℝ), x 1 / a - (q 1 : ℝ), x 2,
    x 3 / a - (q 2 : ℝ), x 4 / a - (q 3 : ℝ), x 5]

def uncropCoeff (a : ℝ) (q : Label) (x : Coeff) : Coeff :=
  ![a * (x 0 + (q 0 : ℝ)), a * (x 1 + (q 1 : ℝ)), x 2,
    a * (x 3 + (q 2 : ℝ)), a * (x 4 + (q 3 : ℝ)), x 5]

def cropLine (a : ℝ) (q : Label) (l : Line) : Line := (l.1, cropCoeff a q l.2)
def cropPoint (a : ℝ) (q : Label) (z : Incident) : Incident := (cropLine a q z.1, z.2)

noncomputable def cropPrior (ν : Measure Line) (a : ℝ) (q : Label) (p : ℝ) : Measure Line :=
  (ENNReal.ofReal p)⁻¹ • Measure.map (cropLine a q) (ν.restrict (cell a q))

def cropEvent (E : Set Incident) (a : ℝ) (q : Label) : Set Incident :=
  cropPoint a q '' (E ∩ (cell a q ×ˢ univ))

/-- The polynomial Boolean format appearing in the frozen statement. -/
def BoolFormat {n : ℕ} (R : ℝ) (D : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ R ∧ ∃ p : Fin m → MvPolynomial (Fin n) ℝ,
    (∀ i, (p i).totalDegree ≤ D) ∧ ∃ b : (Fin m → Bool) → Bool,
      ∀ x, x ∈ S ↔ b (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) = true

def PriorFormat (R : ℝ) (D : ℕ) (ν : Measure Line) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ R ∧
    ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set Coeff),
      (∀ j, 0 ≤ c j ∧ c j ≤ R ∧ (i j : ℝ) ≤ R ∧ BoolFormat R D (A j) ∧
        ∀ x ∈ A j, ∀ b, |x b| ≤ R) ∧
      ν = ∑ j, (ENNReal.ofReal (c j)) •
        Measure.map (fun x => (i j, x)) (volume.restrict (A j))

def EventFormat (R : ℝ) (D : ℕ) (E : Set Incident) : Prop :=
  MeasurableSet E ∧ E ⊆ univ ×ˢ Icc (0 : ℝ) 1 ∧
    (∀ p ∈ E, (p.1.1 : ℝ) ≤ R ∧ ∀ e, |p.1.2 e| ≤ R) ∧
    ∀ i, BoolFormat R D {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ E}

end
end Submission.Obl.k4_dyadic_crop_worlds
