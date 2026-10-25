-- Adapted from this LOT tree, obligation o254, branch x0898, commit 00585850, file Submission/Obl/k4_general_parent_wide_layer_candidates/PreparedProjectedLayer.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedLayers
import Submission.Obl.k4_general_parent_projected_layers.Layers

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory

noncomputable section

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

/-- The prepared comparison model reads the unchanged original layer. -/
def toPrepared (L : ProjectedLayer α) :
    Submission.Obl.k4_general_parent_projected_layers.ProjLayer α :=
  ⟨L.count, L.β, L.C, L.tag, L.u, L.v, L.G⟩

theorem valid_toPrepared (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {s m H : ℝ} (hL : L.Valid p k s m H) :
    L.toPrepared.Good (p.N k) H p.d p.ℓ 0 s (p.N k ^ (-m))
      (p.b k) (p.P k) (p.π k) (p.ρ k) := by
  obtain ⟨hβ, hlo, hhi, hC, hdisj, hlabels, _⟩ := hL
  refine ⟨hβ, ?_, hhi, hC, hdisj, hlabels⟩
  simpa only [toPrepared, neg_zero, Real.rpow_zero, mul_one] using hlo

theorem covers_toPrepared (L : ProjectedLayer α) (σ : Measure (α × ℝ))
    (hL : L.Covers σ) : ∀ᵐ ω ∂σ, ω ∈ L.toPrepared.covered := hL

end ProjectedLayer

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
