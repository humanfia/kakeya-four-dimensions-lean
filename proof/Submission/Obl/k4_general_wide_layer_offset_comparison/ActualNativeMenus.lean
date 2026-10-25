-- Adapted from this LOT tree, obligation o254, branch x0898, commit 00585850, file Submission/Obl/k4_general_parent_wide_layer_candidates/ActualNativeMenus.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeComparisonMenus
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.TrueLayerDomains
import Submission.Obl.k4_general_wide_layer_offset_comparison.Confine.Bridge

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set
open Native.CommonDomain

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Actual original true incidences lie in the small native domain menu
for their own unchanged parent and major coefficient bins. -/
theorem AtDepth.native_tag_domain_menus {k : ℕ} {s R q χ : ℝ}
    (hat : p.AtDepth k s R) (hK : 1 ≤ p.K k)
    (hQ : 0 < p.toModel.q k s) (hq : 0 < q) (hqQ : q ≤ p.toModel.q k s)
    (hχ : 0 < χ) (hg : 0 < p.N k ^ (-p.ℓ * s))
    (hχg : χ ≤ p.N k ^ (-p.ℓ * s))
    (hχQg : χ ≤ p.toModel.q k s * p.N k ^ (-p.ℓ * s)) :
    ∃ menus : Fin (p.n k s) → (Fin 2 → ℤ) → Finset Code,
      (∀ Q tag, ((menus Q tag).card : ℝ) ≤
        1320 * p.K k ^ 2 * (p.toModel.q k s / q) ^ 2) ∧
      ∀ Q tag (ω : α × ℝ), ω.1 ∈ p.B k s Q →
        ω.2 ∈ block (p.T k s) (p.j k s Q) →
        ⌊p.b k ω.1 3 / χ⌋ = tag 0 → ⌊p.b k ω.1 0 / χ⌋ = tag 1 →
        code q χ (p.N k ^ (-p.ℓ * s)) (q * p.N k ^ (-p.ℓ * s)) (p.b k ω.1) ω.2 ∈ menus Q tag := by
  let g := p.N k ^ (-p.ℓ * s)
  have hwQg : q * g ≤ p.toModel.q k s * g := mul_le_mul_of_nonneg_right hqQ hg.le
  choose menus hcard hcover using fun (Q : Fin (p.n k s)) (tag : Fin 2 → ℤ) =>
    true_tag_domain_menu (t₀ := blockLeft p.toModel k s Q) hK hQ hq hqQ hχ hg hχg hχQg
      (mul_pos hq hg) hwQg (p.c k s Q) ((hat.2.2.2.2.1 Q).2.2.2.1 4) tag
  refine ⟨menus, ?_, ?_⟩
  · intro Q tag
    exact (hcard Q tag).trans_eq (by rw [mul_div_mul_right _ _ hg.ne']; ring)
  · intro Q tag ω hB ht hv hz
    have hA := (hat.2.2.1 Q).2.2 hB
    have hleft := blockLeft_mem p.toModel k s Q
    have hgeo := (hat.2.2.2.2.1 Q).2.2.2.2.2.1 ω.1 hA _ hleft
    apply hcover Q tag (p.b k ω.1) ω.2
      (Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block_subset_unit
        (p.T k s) (p.j k s Q) ht)
      (block_distance_left p.toModel k s Q ht) hv hz
    · simpa [rowError, Submission.Obl.k4_critical_intercept_concentration.Data.x,
        Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q, Parent.toModel] using hgeo.2.1
    · exact hgeo.2.2

end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
