/- Adapted from this LOT tree, o118, session x0400, KnownSequence.lean,
commit bd322ee595fd. Only its list-carrying finite system is needed here. -/
import Submission.Obl.k4_remainder_pure_profile_normalization.AtlasSequence
import Submission.Obl.k4_remainder_pure_profile_normalization.ProblemFields
namespace Submission.Obl.k4_remainder_pure_profile_normalization
/-- A known system keeps its original-terminal observation lists. -/
structure KnownSystem (p : Data) (k : ℕ) where
  atlas : Atlas p k
  lists : Fin (p.W k) → Observation → Finset (Fin atlas.C)

def KnownSystem.Valid {p : Data} {k : ℕ} (s : KnownSystem p k) (M D : ℕ) (r : ℝ) : Prop :=
  (s.atlas.C : ℝ) ≤ p.N k ^ M ∧ s.atlas.Separated ∧
  (∀ γ o, ((s.lists γ o).card : ℝ) ≤ s.atlas.κ) ∧
  (∀ b, Chart (p.N k) M D s.atlas.κ s.atlas.T (s.atlas.j b : ℝ) r
    (p.B k (s.atlas.γ b)) (p.E k (s.atlas.γ b)) (s.atlas.c b) (s.atlas.u b)
    (s.atlas.Q b) (s.atlas.R b) (s.atlas.A b) (s.atlas.F b)
    (∀ x ∈ s.atlas.F b, b ∈ s.lists (s.atlas.γ b)
      (obs (p.B k (s.atlas.γ b)) (δ (p.N k) p.L) x))) ∧
  ENNReal.ofReal s.atlas.κ⁻¹ ≤ s.atlas.mass


/-- The existential frozen lists can be retained in a finite system record. -/
theorem Atlas.KnownAt.exists_system {p : Data} {k M D : ℕ} {r : ℝ}
    {a : Atlas p k} (ha : a.KnownAt M D r) :
    ∃ s : KnownSystem p k, s.atlas = a ∧ s.Valid M D r := by
  obtain ⟨lst, h⟩ := ha
  exact ⟨⟨a, lst⟩, rfl, h⟩
end Submission.Obl.k4_remainder_pure_profile_normalization
