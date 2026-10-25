import Mathlib

noncomputable section

namespace Submission.Obl.k4_scalar_crop_profile_transport

open MeasureTheory Set
open scoped ENNReal

abbrev Line := ℕ × (Fin 5 → ℝ)
abbrev Inc := Line × ℝ
abbrev Base := (Fin 2 → ℝ) × ℤ
abbrev Joint := Base × ℤ

def y (l : Line) (t : ℝ) : ℝ := l.2 0 + t * l.2 1
def x (l : Line) (t : ℝ) : ℝ := l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

def Obs (N r : ℝ) (p : Inc) : Base := (![p.2, y p.1 p.2], ⌊x p.1 p.2 / N ^ (-r)⌋)
def Aug (N r u : ℝ) (p : Inc) : Joint := (Obs N r p, ⌊p.1.2 1 / N ^ (-u)⌋)

def Selected (ν : Measure Line) (E : Set Inc) : Measure Inc := (ν.prod volume).restrict E

def Cell (a : ℝ) (z : Fin 2 → ℤ) : Set Line :=
  {l | ⌊l.2 0 / a⌋ = z 0 ∧ ⌊l.2 1 / a⌋ = z 1}

def Crop (a : ℝ) (z : Fin 2 → ℤ) (l : Line) : Line :=
  (l.1, ![l.2 0 / a - (z 0 : ℝ), l.2 1 / a - (z 1 : ℝ), l.2 2, l.2 3, l.2 4])

def CropInc (a : ℝ) (z : Fin 2 → ℤ) (p : Inc) : Inc := (Crop a z p.1, p.2)

noncomputable def BaseRef : Measure Base := volume.prod Measure.count
noncomputable def JointRef : Measure Joint := BaseRef.prod Measure.count

lemma measurable_Obs (N r : ℝ) : Measurable (Obs N r) := by unfold Obs x y; fun_prop
lemma measurable_Aug (N r u : ℝ) : Measurable (Aug N r u) := by
  unfold Aug
  exact (measurable_Obs N r).prodMk (by fun_prop)
lemma measurable_CropInc (a : ℝ) (z : Fin 2 → ℤ) : Measurable (CropInc a z) := by
  unfold CropInc Crop
  fun_prop
lemma measurableSet_Cell (a : ℝ) (z : Fin 2 → ℤ) : MeasurableSet (Cell a z) := by
  unfold Cell
  exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
    (measurableSet_eq_fun (by fun_prop) measurable_const)

/-- The source law has pure and joint density windows. -/
def Homogeneous (N : ℕ → ℝ) (s V : ℝ) (μ : ℕ → Measure Inc)
    (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ (g : ℕ → ℝ → Base → ENNReal) (G : ℕ → ℝ → ℝ → Joint → ENNReal),
    (∀ k r, 0 ≤ r → r ≤ s → Measurable (g k r) ∧
      (μ k).map (Obs (N k) r) = BaseRef.withDensity (g k r)) ∧
    (∀ k r u, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ V → Measurable (G k r u) ∧
      (μ k).map (Aug (N k) r u) = JointRef.withDensity (G k r u)) ∧
    (∀ r τ : ℝ, 0 ≤ r → r ≤ s → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop,
      μ k {p | g k r (Obs (N k) r p) < ENNReal.ofReal (N k ^ (-F r 0 - τ)) ∨
        ENNReal.ofReal (N k ^ (-F r 0 + τ)) < g k r (Obs (N k) r p)} ≤
        ENNReal.ofReal (N k ^ (-c))) ∧
    (∀ r u τ : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ V → 0 < τ →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop,
      μ k {p | G k r u (Aug (N k) r u p) < ENNReal.ofReal (N k ^ (-F r u - τ)) ∨
        ENNReal.ofReal (N k ^ (-F r u + τ)) < G k r u (Aug (N k) r u p)} ≤
        ENNReal.ofReal (N k ^ (-c)))

/-- Exact incidence lifting facts supplied by the crop construction. -/
def LiftFacts (N : ℕ → ℝ) (u₀ : ℝ) (W : ℕ → ℕ)
    (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set Inc)
    (ν : (k : ℕ) → Fin (W k) → Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc)
    (p : (k : ℕ) → Fin (W k) → ℝ)
    (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ) : Prop :=
  (∀ k γ, MeasurableSet (Cell (N k ^ (-u₀)) (z k γ))) ∧
  (∀ k γ, Measurable (Crop (N k ^ (-u₀)) (z k γ))) ∧
  (∀ k, Pairwise (fun γ γ' => Disjoint (Cell (N k ^ (-u₀)) (z k γ))
    (Cell (N k ^ (-u₀)) (z k γ')))) ∧
  (∀ k γ Z, MeasurableSet Z → ENNReal.ofReal (p k γ) * Selected (ν k γ) (E k γ) Z =
    Selected (ν₀ k) (E₀ k) {a | a.1 ∈ Cell (N k ^ (-u₀)) (z k γ) ∧
      CropInc (N k ^ (-u₀)) (z k γ) a ∈ Z}) ∧
  (∀ k γ l, l ∈ Cell (N k ^ (-u₀)) (z k γ) → ∀ t,
    x (Crop (N k ^ (-u₀)) (z k γ) l) t = x l t) ∧
  (∀ k γ l, l ∈ Cell (N k ^ (-u₀)) (z k γ) → ∀ t,
    y (Crop (N k ^ (-u₀)) (z k γ) l) t =
      (y l t - N k ^ (-u₀) * (z k γ 0 : ℝ) - t * (N k ^ (-u₀) * (z k γ 1 : ℝ))) /
        N k ^ (-u₀)) ∧
  (∀ k γ l, l ∈ Cell (N k ^ (-u₀)) (z k γ) → ∀ t ∈ Icc (0 : ℝ) 1,
    |y (Crop (N k ^ (-u₀)) (z k γ) l) t| ≤ 2)

end Submission.Obl.k4_scalar_crop_profile_transport
