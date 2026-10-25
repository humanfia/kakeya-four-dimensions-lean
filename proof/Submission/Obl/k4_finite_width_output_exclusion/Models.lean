import Submission.Obl.k4_finite_width_output_exclusion.Definitions

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter

noncomputable section

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev Point := Line × ℝ
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Observation := EuclideanSpace ℝ (Fin 3) × ℤ

structure Data where
  N : ℕ → ℝ
  K : ℕ → ℝ
  L : ℝ
  d : ℝ
  S : ℝ
  η : ℝ
  W : ℕ → ℕ
  ω : (k : ℕ) → Fin (W k) → ℝ
  ν : (k : ℕ) → Fin (W k) → Measure Line
  E : (k : ℕ) → Fin (W k) → Set Point
  P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ
  B : (k : ℕ) → Fin (W k) → ℝ
  f : ℝ → ℝ
  g : (k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal
  G : (k : ℕ) → Fin (W k) → ℝ → (Observation × (Fin 2 → ℤ)) → ENNReal

def Valid (p : Data) : Prop :=
  prob p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G

def Cost (p : Data) (h : ℝ) : Prop :=
  term p.N p.K p.L p.W p.ω p.ν p.E p.B p.f h

def Horizon (p : Data) : ℝ :=
  H p.N p.K p.L p.W p.ω p.ν p.E p.B p.f

def Narrow (p : Data) (h w : ℝ) : Prop :=
  nt p.N p.K p.L p.W p.ω p.ν p.E p.B p.f h w

def priorMass (p : Data) (k : ℕ) (b : Fin (p.W k)) : Measure Point :=
  (p.ν k b).prod volume

def selected (p : Data) (k : ℕ) (b : Fin (p.W k)) : Measure Point :=
  (priorMass p k b).restrict (p.E k b)

structure Atlas (p : Data) (k : ℕ) where
  T : ℕ
  C : ℕ
  γ : Fin C → Fin (p.W k)
  j : Fin C → Fin (2 ^ T)
  c : Fin C → Plane
  u : Fin C → Plane
  Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ
  R : Fin C → MvPolynomial (Fin 4) ℝ
  A : Fin C → Set Line
  F : Fin C → Set Point
  lst : Fin (p.W k) → Observation → Finset (Fin C)

def Atlas.Regular {p : Data} {k : ℕ} (a : Atlas p k)
    (M D : ℕ) (κ r : ℝ) (extra : Fin a.C → Prop) : Prop :=
  (a.C : ℝ) ≤ p.N k ^ M ∧
  (∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b')) ∧
  (∀ b, chart (p.N k) M D κ a.T ((a.j b : ℕ) : ℝ) r
    (p.B k (a.γ b)) (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b)
    (a.A b) (a.F b) (extra b)) ∧
  ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b)

def Atlas.KnownAt {p : Data} {k : ℕ} (a : Atlas p k)
    (M D : ℕ) (κ r : ℝ) : Prop :=
  a.Regular M D κ r (fun b => ∀ z ∈ a.F b,
    b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z)) ∧
  ∀ γ o, ((a.lst γ o).card : ℝ) ≤ κ

def Atlas.TrueAt {p : Data} {k : ℕ} (a : Atlas p k)
    (M D : ℕ) (κ : ℝ) : Prop :=
  a.Regular M D κ p.L (fun b =>
    ENNReal.ofReal (p.N k ^ (-p.f p.L) * |Matrix.det (a.Q b)| /
      ((2 : ℝ) ^ a.T * κ)) ≤ priorMass p k (a.γ b) (a.F b))

def Known (p : Data) (r h w : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
    ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ p.N k ^ ε ∧ ∃ a : Atlas p k,
      (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧
      (∀ b, |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ≤ p.N k ^ (-w + ε)) ∧
      a.KnownAt M D κ r

def Initial : Prop := ∀ p : Data, Valid p → ∀ h : ℝ, p.L < h → Cost p h

def Composition : Prop :=
  ∀ p : Data, Valid p → ∀ r h w : ℝ, 0 ≤ r → r < p.L → Known p r h w →
    ∃ q : Data, Valid q ∧ q.L = p.L - r ∧ q.d = p.d ∧ q.S = p.S ∧ q.η = p.η ∧
      (∀ h' e : ℝ, 0 < e → Cost q h' → Cost p (h + h' + e)) ∧
      (∀ h' w' : ℝ, Narrow q h' w' → Narrow p (h + h') (w + w'))

def Extremal (ds kr S η : ℝ) : Prop :=
  0 ≤ ds ∧ ds < 1 ∧ 0 < kr ∧ kr ≤ 1 ∧
  (∀ t : ℝ, 0 < t → ∃ p : Data, Valid p ∧ p.L = 1 ∧ p.S = S ∧ p.η = η ∧
    p.d < ds + t ∧ kr - t < Horizon p) ∧
  (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧ ∀ p : Data, Valid p →
    p.S = S → p.η = η → p.d < ds + a → Horizon p ≤ (kr + t) * p.L) ∧
  (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧ ∀ p : Data, Valid p →
    p.S = S → p.η = η → p.d < ds + a → (kr - a) * p.L < Horizon p →
    ∀ r : ℝ, 0 ≤ r → r ≤ p.L → |p.f r - p.f 0 - ds * r| ≤ t * p.L)

def UniformWidth (ds kr S η w : ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → ∃ t : ℝ, 0 < t ∧ ∀ p : Data, Valid p →
    p.L = 1 → p.S = S → p.η = η → p.d < ds + t → kr - t < Horizon p →
    Narrow p (kr + a) w

end
end Submission.Obl.k4_finite_width_output_exclusion
