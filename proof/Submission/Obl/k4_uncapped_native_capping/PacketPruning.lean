/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/PacketPruning.lean (namespace renamed to
Submission.Obl.k4_uncapped_native_capping). Existing source attributions below are retained.
-/
import Submission.Obl.k4_uncapped_native_capping.PacketData
import Submission.Obl.k4_uncapped_native_capping.HeavyPackets

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Set
noncomputable section

namespace PacketData

variable {W : ℕ}

def restrictTo (p : PacketData W) (s : Finset (Fin p.C)) : PacketData W :=
  p.reindex ⟨s.orderEmbOfFin rfl, (s.orderEmbOfFin rfl).injective⟩

theorem mass_restrictTo (p : PacketData W) (s : Finset (Fin p.C))
    (ω : Fin W → ℝ) (ν : Fin W → Measure Traj) :
    (p.restrictTo s).mass ω ν = ∑ a ∈ s, p.weight ω ν a * p.law a univ := by
  classical
  change (∑ a, p.weight ω ν (s.orderEmbOfFin rfl a) *
    p.law (s.orderEmbOfFin rfl a) univ) = _
  calc
    _ = ∑ a ∈ Finset.univ.image (s.orderEmbOfFin rfl),
        p.weight ω ν a * p.law a univ := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ heq => (s.orderEmbOfFin rfl).injective heq
    _ = _ := by rw [s.image_orderEmbOfFin_univ rfl]

/-- A small extra mass margin removes all light conditional laws.  The
original full priors, format, geometry, lists and certificate are retained. -/
theorem to_sample_of_mass_margin (p : PacketData W) {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {a₀ w loss h χ d s m S U : ℝ}
    (hg : p.Geometry N K ω ν E P B M D loss h)
    (ha : p.Analysis N χ d s m S U ω ν P B)
    (hmass : ENNReal.ofReal (N ^ (-loss)) + ENNReal.ofReal (N ^ (-χ)) ≤ p.mass ω ν) :
    NativeSystemSample true N K W ω ν E P B M D a₀ w loss h χ d s m S U := by
  classical
  let keep := Finset.univ.filter (fun a => ENNReal.ofReal (N ^ (-χ)) ≤ p.law a univ)
  apply (p.restrictTo keep).to_sample
    (hg.reindex ⟨keep.orderEmbOfFin rfl, (keep.orderEmbOfFin rfl).injective⟩)
    (ha.reindex ⟨keep.orderEmbOfFin rfl, (keep.orderEmbOfFin rfl).injective⟩)
  · intro a
    exact (Finset.mem_filter.mp (keep.orderEmbOfFin_mem rfl a)).2
  · rw [mass_restrictTo]
    exact heavy_packet_mass_lower (p.weight ω ν) (fun a => p.law a univ)
      ENNReal.ofReal_ne_top hg.budget_sum hmass

end PacketData
end
end Submission.Obl.k4_uncapped_native_capping
