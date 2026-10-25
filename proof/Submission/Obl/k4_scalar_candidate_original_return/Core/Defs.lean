import Submission.Obl.k4_scalar_candidate_original_return.Core.STIApply
import Submission.Obl.k4_scalar_candidate_original_return.DataFacts
import Submission.Obl.k4_scalar_candidate_original_return.Fits
import Submission.Lib.K4FinitePlankAtlases.Greedy

/-!
# Candidate scenarios and maximal greedy assignments

A *scenario* fixes a tangent depth `s₀`, a gain `c₀` and a coefficient exponent `R`.
Its slack is `θ * c₀` for a global small constant `θ`.  For every stage, every layer
whose tangent depth is within `θ c₀ / 4` of `s₀`, and every plank of that layer, we
choose a maximal threshold-greedy family of candidate fits (finite by the mass budget).
The covered incidences of the first `J` scenarios are `CovJ`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set
open Submission.Lib.K4FinitePlankAtlases

noncomputable section

/-- A candidate scenario: tangent depth, gain, coefficient exponent. -/
structure Scenario where
  s₀ : ℝ
  c₀ : ℝ
  R : ℕ

/-- A surjective enumeration of the rational scenarios `(a/(m+1), b/(m+1), R)`. -/
noncomputable def menu (n : ℕ) : Scenario :=
  ⟨((n.unpair.2.unpair.1 : ℕ) : ℝ) / ((n.unpair.1 : ℝ) + 1),
    ((n.unpair.2.unpair.2.unpair.1 : ℕ) : ℝ) / ((n.unpair.1 : ℝ) + 1),
    n.unpair.2.unpair.2.unpair.2⟩

namespace PreparedData

variable (a : PreparedData)

/-- Number of worlds at stage `k`. -/
abbrev Wk (k : ℕ) : ℕ := W (a.p k) (a.sm k)

/-- Start of the time interval of plank `i` of layer `ℓ`. -/
noncomputable def tStart (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n) : ℝ :=
  (((a.ls k ℓ).time i : ℕ) : ℝ) / (2 : ℝ) ^ (a.ls k ℓ).T

/-- End of the time interval of plank `i` of layer `ℓ`. -/
noncomputable def tEnd (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n) : ℝ :=
  ((((a.ls k ℓ).time i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (a.ls k ℓ).T

/-- The incidence region of plank `i` of layer `ℓ`: its full prior set times its time block. -/
def plank (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n) : Set Inc :=
  (a.ls k ℓ).prior i ×ˢ I (a.ls k ℓ).T ((a.ls k ℓ).time i)

/-- The candidate fit tolerance `N ^ (θ c₀ - s₀ - c₀)` of a scenario. -/
noncomputable def fitTol (θ : ℝ) (σ : Scenario) (k : ℕ) : ℝ :=
  a.tangent k ^ (θ * σ.c₀ - σ.s₀ - σ.c₀)

/-- The incidences of plank `i` whose whole trajectory piece fits `P`. -/
def candSet (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n)
    (P : Poly) : Set Inc :=
  ((a.ls k ℓ).prior i ∩ Fit P (a.tStart k ℓ i) (a.tEnd k ℓ i) (a.fitTol θ σ k)) ×ˢ
    I (a.ls k ℓ).T ((a.ls k ℓ).time i)

/-- Admissible candidate polynomials of a scenario. -/
def Admissible (σ : Scenario) (k : ℕ) (P : Poly) : Prop :=
  P.totalDegree ≤ 2 ∧ ∀ b, |P.coeff b| ≤ a.tangent k ^ (σ.R : ℝ)

/-- The mass floor `N^(-d c₀ - θ c₀) 2^(-T) ν(A_i)` of a scenario candidate. -/
noncomputable def thr (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) : ℝ :=
  a.tangent k ^ (-a.rd * σ.c₀ - θ * σ.c₀) / (2 : ℝ) ^ (a.ls k ℓ).T *
    (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i)).toReal

/-- The original incidence law of the plank's world, restricted to the plank. -/
noncomputable def plankMeasure (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n) :
    Measure Inc :=
  (a.ρ k ((a.ls k ℓ).world i)).restrict (a.plank k ℓ i)

/-- Greedy thresholds: inadmissible polynomials (or a vanishing floor) are never heavy. -/
noncomputable def greedyThr (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) (P : Poly) : ℝ :=
  by
    classical
    exact if a.Admissible σ k P ∧ 0 < a.thr θ σ k ℓ i then a.thr θ σ k ℓ i
      else (a.plankMeasure k ℓ i).real univ + 1

/-- The defining property of a maximal greedy family. -/
def GreedySpec (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) (l : List Poly) : Prop :=
  ThresholdGreedySequence (a.candSet θ σ k ℓ i) (a.greedyThr θ σ k ℓ i)
      (a.plankMeasure k ℓ i) l ∧
    ∀ P, (residualMeasure (a.candSet θ σ k ℓ i) (a.plankMeasure k ℓ i) l).real
      (a.candSet θ σ k ℓ i P) < a.greedyThr θ σ k ℓ i P

/-- A maximal greedy family of candidate polynomials (empty if none exists). -/
noncomputable def greedy (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k))
    (i : Fin (a.ls k ℓ).n) : List Poly :=
  by
    classical
    exact if h : ∃ l, a.GreedySpec θ σ k ℓ i l then Classical.choose h else []

/-- The incidences covered by the greedy family of a plank. -/
def cov (θ : ℝ) (σ : Scenario) (k : ℕ) (ℓ : Fin (a.ct k)) (i : Fin (a.ls k ℓ).n) :
    Set Inc :=
  ⋃ P ∈ a.greedy θ σ k ℓ i, a.candSet θ σ k ℓ i P

/-- Layers used by a scenario at stage `k`: tangent depths within `θ c₀ / 4` and
within `s₀ / 2` of `s₀`. -/
def layersOf (θ : ℝ) (σ : Scenario) (k : ℕ) : Set (Fin (a.ct k)) :=
  {ℓ | 0 < σ.s₀ ∧ 0 < σ.c₀ ∧
    ∃ s : ℝ, |s - σ.s₀| ≤ θ * σ.c₀ / 4 ∧ |s - σ.s₀| ≤ σ.s₀ / 2 ∧ a.nd k s = ℓ}

/-- Covered incidences of world `g` for one scenario. -/
def Cov (θ : ℝ) (σ : Scenario) (k : ℕ) (g : Fin (a.Wk k)) : Set Inc :=
  ⋃ ℓ ∈ a.layersOf θ σ k, ⋃ (i : Fin (a.ls k ℓ).n) (_ : (a.ls k ℓ).world i = g),
    a.cov θ σ k ℓ i

/-- Covered incidences of world `g` for the first `J` menu scenarios. -/
def CovJ (θ : ℝ) (J k : ℕ) (g : Fin (a.Wk k)) : Set Inc :=
  ⋃ n < J, ⋃ (_ : 0 < (menu n).s₀), ⋃ (_ : 0 < (menu n).c₀), a.Cov θ (menu n) k g

/-- Weighted original mass covered by the first `J` menu scenarios. -/
noncomputable def covMass (θ : ℝ) (J k : ℕ) : ENNReal :=
  ∑ g, ENNReal.ofReal (ω (a.p k) (a.sm k) g) * a.ρ k g (a.CovJ θ J k g)

end PreparedData

end

end Submission.Obl.k4_scalar_candidate_original_return
