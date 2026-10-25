import Submission.Obl.k4_finite_width_output_exclusion.Models

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- All finite geometric data of a raw forest at a single original sample. -/
structure Forest (p : Data) (k : ℕ) where
  κ : ℝ
  T : ℕ → ℕ
  C : ℕ
  lev : Fin C → ℕ
  par : Fin C → Fin C
  γ : Fin C → Fin (p.W k)
  j : Fin C → ℕ
  c : Fin C → Plane
  u : Fin C → Plane
  Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ
  R : Fin C → MvPolynomial (Fin 4) ℝ
  A : Fin C → Set Line
  F : Fin C → Set Point

/-- The core predicate in o192, with the actual incidence floor at every node. -/
def Forest.Core {p : Data} {k : ℕ} (a : Forest p k) (M D m : ℕ) (r : ℕ → ℝ) : Prop :=
  1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ (a.C : ℝ) ≤ p.N k ^ M ∧
  (∀ i, i < m → ENNReal.ofReal a.κ⁻¹ ≤
    ∑ b, if a.lev b = i then
      ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b) else 0) ∧
  (∀ b b', b ≠ b' → a.lev b = a.lev b' → a.γ b = a.γ b' → a.j b = a.j b' →
    Disjoint (a.A b) (a.A b')) ∧
  (∀ b, a.lev b < m ∧ a.j b < 2 ^ a.T (a.lev b) ∧
    chart (p.N k) M D a.κ (a.T (a.lev b)) (a.j b : ℝ) (r (a.lev b))
      (p.B k (a.γ b)) (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b)
      (a.A b) (a.F b)
      (ENNReal.ofReal (p.N k ^ (-p.f (r (a.lev b))) * |Matrix.det (a.Q b)| /
        ((2 : ℝ) ^ a.T (a.lev b) * a.κ)) ≤ priorMass p k (a.γ b) (a.F b)) ∧
    (0 < a.lev b → a.lev (a.par b) + 1 = a.lev b ∧ a.γ (a.par b) = a.γ b ∧
      a.A b ⊆ a.A (a.par b) ∧ a.F b ⊆ a.F (a.par b) ∧
      (a.j (a.par b) : ℝ) / (2 : ℝ) ^ a.T (a.lev (a.par b)) ≤
        (a.j b : ℝ) / (2 : ℝ) ^ a.T (a.lev b) ∧
      ((a.j b : ℝ) + 1) / (2 : ℝ) ^ a.T (a.lev b) ≤
        ((a.j (a.par b) : ℝ) + 1) / (2 : ℝ) ^ a.T (a.lev (a.par b))))

/-- Regard a terminal atlas as a forest with one layer. -/
def oneLayerForest {p : Data} {k : ℕ} (a : Atlas p k) (κ : ℝ) : Forest p k where
  κ := κ
  T := fun _ => a.T
  C := a.C
  lev := fun _ => 0
  par := id
  γ := a.γ
  j := fun b => (a.j b : ℕ)
  c := a.c
  u := a.u
  Q := a.Q
  R := a.R
  A := a.A
  F := a.F

lemma oneLayerForest_core {p : Data} {k M D : ℕ} {κ : ℝ}
    {a : Atlas p k} (hL : p.L = 1) (hκ : 1 ≤ κ) (hKκ : p.K k ≤ κ)
    (ha : a.TrueAt M D κ) : (oneLayerForest a κ).Core M D 1 (fun _ => 1) := by
  obtain ⟨hC, hsep, hchart, hmass⟩ := ha
  refine ⟨hκ, hKκ, hC, ?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    change ENNReal.ofReal (κ⁻¹) ≤
      ∑ b : Fin a.C, if (0 : ℕ) = 0 then
        ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b) else 0
    simpa only [ite_true] using hmass
  · intro b b' hbb' hlev hγ hj
    exact hsep b b' hbb' hγ (Fin.ext hj)
  · intro b
    refine ⟨Nat.zero_lt_succ 0, (a.j b).isLt, ?_, ?_⟩
    · simpa only [oneLayerForest, hL] using hchart b
    · intro hb
      exact False.elim (Nat.not_lt_zero _ hb)

end
end Submission.Obl.k4_raw_critical_segment_forests
