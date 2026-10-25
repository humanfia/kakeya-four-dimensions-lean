import Submission.Obl.k4_finite_positive_mixed_cover_realization.ActualPairCharge

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_forest_width_selection

/-- Retained analytical incidences: the candidate strip agrees projectively
with some deeper true label at the same actual old parent. -/
def CoverData.alignedWitness {W : ℕ} {p : PathData W} (c : CoverData p)
    (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ) (gap : ℝ)
    (j : ℕ) (a : Fin c.n) : Set Incidence :=
  {z | z ∈ c.interior a ∧ ∃ d : Fin p.C,
    (p.lev d = j ∧ p.world d = p.world (c.old a) ∧
      forestAncestor p.lev p.par d c.level = c.old a ∧ c.Aligned normal bias gap a d) ∧
        z ∈ p.counted d}

section
variable {W m Mp Dp Mg Dg : ℕ} {p : PathData W} {c : CoverData p}
    {ℓ Nk L κ₁ δ₀ σ d₁ ρ gain ε gap : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε)
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ)
    {j : ℕ} (hij : c.level ≤ j) (hjm : j < m)

include hc hp hij hjm

lemma CoverData.Valid.unaligned_subset_pairs (w : Fin W) (a : Fin c.n) :
    {z | p.world (c.old a) = w ∧ z ∈ c.interior a ∧
        z ∉ c.alignedWitness normal bias gap j a} ⊆
      ⋃ d : Fin p.C, c.misalignedPair normal bias gap j w (a, d) := by
  intro z hz
  obtain ⟨d, hd, hdw, hzd, hparent⟩ := hc.interior_deep_coverage hp hij hjm a hz.2.1
  have hmis : ¬ c.Aligned normal bias gap a d := by
    intro halign
    exact hz.2.2 ⟨hz.2.1, d, ⟨hd, hdw, hparent, halign⟩, hzd⟩
  exact Set.mem_iUnion.mpr ⟨d, ⟨hdw.trans hz.1, hz.1, hd, hparent.symm, hmis⟩, hz.2.1, hzd⟩

/-- Good unaligned candidate mass is bounded by the sum charged by the
original-law pair-label estimate. There is no candidate multiplicity on a
world's exceptional set in this comparison. -/
lemma CoverData.Valid.unaligned_mass_le_pairs (μ : Measure Incidence) (Good : Set Incidence)
    (w : Fin W) :
    (∑ a : Fin c.n, μ {z | (p.world (c.old a) = w ∧ z ∈ c.interior a ∧
      z ∉ c.alignedWitness normal bias gap j a) ∧ z ∈ Good}) ≤
      ∑ bd : Fin c.n × Fin p.C,
        μ (c.misalignedPair normal bias gap j w bd ∩ Good) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro a _
  apply (measure_mono (t := ⋃ d : Fin p.C,
    c.misalignedPair normal bias gap j w (a, d) ∩ Good) ?_).trans
    (measure_iUnion_fintype_le _ _)
  intro z hz
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp
    (hc.unaligned_subset_pairs hp normal bias hij hjm w a hz.1)
  exact Set.mem_iUnion.mpr ⟨d, hd, hz.2⟩

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
