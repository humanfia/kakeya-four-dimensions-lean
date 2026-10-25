import Submission.Obl.k4_remainder_pure_profile_normalization.TaggedTails
import Submission.Obl.k4_remainder_pure_profile_normalization.AnalyticProfile

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter

/-- A strict subsequence and an incidence-only selection of a fixed family of worlds. -/
structure IncidenceSelection (p : Data) where
  index : ℕ → ℕ
  strictMono : StrictMono index
  K : ℕ → ℝ
  E : (k : ℕ) → Fin (p.W (index k)) → Set Incidence
  f : ℝ → ℝ
  g : (k : ℕ) → Fin (p.W (index k)) → ℝ → Observation → ENNReal
  G : (k : ℕ) → Fin (p.W (index k)) → ℝ → JointObservation → ENNReal

noncomputable def IncidenceSelection.data {p : Data} (s : IncidenceSelection p) : Data where
  N := p.N ∘ s.index
  K := s.K
  L := p.L
  d := p.d
  S := p.S
  η := p.η
  W := p.W ∘ s.index
  ω := fun k => p.ω (s.index k)
  ν := fun k => p.ν (s.index k)
  E := s.E
  P := fun k => p.P (s.index k)
  B := fun k => p.B (s.index k)
  f := s.f
  g := s.g
  G := s.G

/-- The output of pure multiworld homogenization, before any endpoint cap is asserted. -/
structure HomogeneousSelection (p : Data) where
  selection : IncidenceSelection p
  slack_ge : ∀ k, p.K (selection.index k) ≤ selection.K k
  event_subset : ∀ k b, selection.E k b ⊆ p.E (selection.index k) b
  subpower : (∀ k, 1 ≤ selection.K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
    selection.K k ≤ p.N (selection.index k) ^ ε
  samples : ∃ M D : ℕ, ∀ k, Normalization.SampleProblem
    (selection.data.N k) (selection.data.K k) M D (selection.data.W k)
    (selection.data.ω k) (selection.data.ν k) (selection.data.E k)
    (selection.data.P k) (selection.data.B k)
  pure_law : ∀ k b σ, 0 ≤ σ → σ ≤ p.L → Measurable (selection.g k b σ) ∧
    (selection.data.incidenceMeasure k b).map
      (obs (selection.data.B k b) (δ (selection.data.N k) σ)) =
        (volume.prod Measure.count).withDensity (selection.g k b σ)
  joint_law : ∀ k b u, 0 < u → u ≤ p.η * p.L → Measurable (selection.G k b u) ∧
    (selection.data.incidenceMeasure k b).map (fun z =>
      (obs (selection.data.B k b) (δ (selection.data.N k) p.L) z,
        fun j : Fin 2 => ⌊v z.1 j / δ (selection.data.N k) u⌋)) =
          ((volume.prod Measure.count).prod Measure.count).withDensity (selection.G k b u)
  increments : ∀ r s, 0 ≤ r → r ≤ s → s ≤ p.L →
    0 ≤ selection.f s - selection.f r ∧ selection.f s - selection.f r ≤ s - r
  typical : ∀ σ, 0 ≤ σ → σ ≤ p.L → selection.data.TypicalAt σ (selection.f σ)

/-- The independent pure homogenization input needed by the remainder construction. -/
def PureHomogenization : Prop :=
  ∀ p : Data, (∀ k, 2 ≤ p.N k) → Tendsto p.N atTop atTop →
    ((∀ k, 1 ≤ p.K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, p.K k ≤ p.N k ^ ε) →
    0 < p.L →
    (∃ M D : ℕ, ∀ k, Normalization.SampleProblem (p.N k) (p.K k) M D
      (p.W k) (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k)) →
    Nonempty (HomogeneousSelection p)

end Submission.Obl.k4_remainder_pure_profile_normalization
