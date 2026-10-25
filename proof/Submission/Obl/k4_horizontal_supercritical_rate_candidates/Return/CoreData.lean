import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Basics

/-!
# Bundled single-sample data for the supercritical return

`CoreData` collects one sample's objects; `CoreHyp` the hypotheses of `CoreStatement` at
that sample. Scales (`a₀`, `a₁`, `χ`, `D`, block lengths) are derived definitions.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

structure CoreData (α : Type) [MeasurableSpace α] where
  N : ℝ
  K : ℝ
  d : ℝ
  κ : ℝ
  S : ℝ
  e₀ : ℝ
  s₀ : ℝ
  s₁ : ℝ
  vc : ℝ
  M : ℝ
  RL : ℝ
  εL : ℝ
  Rcap : ℝ
  ν : Measure α
  μ : Measure (α × ℝ)
  ρ : Measure (α × ℝ)
  ρs : Measure (α × ℝ)
  π : Measure ℝ
  b : α → Fin 6 → ℝ
  f₀ : Fam α
  fc : Fam α
  fe : Fam α
  Ly : Layer α

namespace CoreData

variable {α : Type} [MeasurableSpace α] (D : CoreData α)

def sc : ℝ := D.s₁ - D.vc
def se : ℝ := 300 * D.s₀
def a₀ : ℝ := D.N ^ (-D.s₀)
def ac : ℝ := D.N ^ (-D.sc)
def a₁ : ℝ := D.N ^ (-D.s₁)
def χ : ℝ := D.N ^ (-D.M)
def Dw : ℝ := D.N ^ (-2 * D.κ * D.s₀)

/-- Direction bin of a slice. -/
def dirBin (i : Fin D.Ly.n) : Set ℝ :=
  Ico ((D.Ly.qp i 0 : ℝ) * D.χ) (((D.Ly.qp i 0 : ℝ) + 1) * D.χ)

end CoreData

/-- The hypotheses of `CoreStatement` at one sample. -/
structure CoreHyp {α : Type} [MeasurableSpace α] (D : CoreData α) : Prop where
  N2 : 2 ≤ D.N
  K1 : 1 ≤ D.K
  bmeas : Measurable D.b
  νprob : IsProbabilityMeasure D.ν
  πprob : IsProbabilityMeasure D.π
  μdom : D.μ ≤ ENNReal.ofReal D.K • D.ν.prod volume
  ρμ : D.ρ ≤ D.μ
  μsupp : D.μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0
  bbd : ∀ᵐ l ∂D.ν, |D.b l 0| + |D.b l 1| + |D.b l 3| + |D.b l 4| ≤ D.K
  x3bd : ∀ᵐ p ∂D.μ, ∀ t ∈ Icc (0 : ℝ) 1, |x3 D.b p.1 t| ≤ D.K
  hor : ∀ᵐ p ∂D.μ, |D.b p.1 4 + D.b p.1 0| ≤ D.N ^ (-D.e₀)
  caps : Caps D.μ D.π D.b D.N D.K D.d D.S D.Rcap⁻¹ D.Rcap D.Rcap D.Rcap⁻¹ D.Rcap
  f₀good : D.f₀.Good D.ν D.μ D.π D.b D.N D.K D.d D.κ D.s₀ D.χ
  fcgood : D.fc.Good D.ν D.μ D.π D.b D.N D.K D.d D.κ D.sc D.χ
  fegood : D.fe.Good D.ν D.μ D.π D.b D.N D.K D.d D.κ D.se D.χ
  nest0 : Nests D.fc D.f₀
  nest1 : Nests D.fe D.fc
  ρsρ : D.ρs ≤ D.ρ
  ρsmass : ENNReal.ofReal (D.N ^ (-D.εL)) ≤ D.ρs univ
  ρscov : ∀ᵐ p ∂D.ρs, ∃ i, p.1 ∈ D.Ly.C i
  lygood : D.Ly.Good D.ρ D.π D.b D.N D.χ D.Dw D.a₁ D.d D.εL D.RL

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
