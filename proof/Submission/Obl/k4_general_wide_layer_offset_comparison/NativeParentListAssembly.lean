-- Adapted from this LOT tree, obligation o254, branch x0898, commit 00585850, file Submission/Obl/k4_general_parent_wide_layer_candidates/NativeParentListAssembly.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.PreparedComparisonAt
import Submission.Obl.k4_general_wide_layer_offset_comparison.PreparedProjectedLayer
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeParentLists
import Submission.Obl.k4_general_wide_layer_offset_comparison.ActualNativeMenus
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeRefinementMenus
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeDomainLists
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeCodeBridge

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open Native.SheetComparison Native.CommonDomain

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Aggregate the literal native comparison lists to the original parent
and short-domain format. All source data and the retained law are unchanged. -/
theorem native_parent_lists_of_comparison (hp : p.Valid)
    {k : ℕ} {s R m q H aT Fprune Llist ε C Λ Hout : ℝ}
    (hat : p.AtDepth k s R) (L : ProjectedLayer α) (hL : L.Valid p k s m H)
    {ζ source : Measure (α × ℝ)} (hζsource : ζ ≤ source)
    {assign : α × ℝ → Fin (p.n k s)}
    {graphs : Fin (p.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ}
    (cmp : PreparedComparison p.toParams p.toModel k s H q (p.N k ^ (-m))
      (q * p.N k ^ (-p.ℓ * s)) aT Fprune Llist ε C Λ L.toPrepared ζ assign graphs)
    (hq : 0 < q) (hqQ : q ≤ p.toModel.q k s)
    (hχg : p.N k ^ (-m) ≤ p.N k ^ (-p.ℓ * s))
    (hχQg : p.N k ^ (-m) ≤ p.toModel.q k s * p.N k ^ (-p.ℓ * s))
    (hLlist : 1 ≤ Llist) (hΛ : 1 ≤ Λ)
    (hmass : ENNReal.ofReal Hout⁻¹ ≤ cmp.law univ)
    (hforward : (1320 * p.K k ^ 2 * (p.toModel.q k s / q) ^ 2) *
      (2 * (Llist * Λ ^ p.d)) ≤ Hout)
    (hreverse : (84 * (p.toModel.q k s / q) ^ 2) * (Llist * Λ ^ p.d) ≤ Hout) :
    Nonempty (p.NativeParentLists k s m Hout L source) := by
  classical
  let Q := p.toModel.q k s
  let g := p.N k ^ (-p.ℓ * s)
  let χ := p.N k ^ (-m)
  have hNp : 0 < p.N k := by linarith [hp.scale k]
  have hQ : 0 < Q := by dsimp [Q, Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  have hχ : 0 < χ := by dsimp [χ]; positivity
  have hB : 0 ≤ Llist * Λ ^ p.d :=
    mul_nonneg (zero_le_one.trans hLlist) (Real.rpow_nonneg (by linarith) _)
  obtain ⟨menus, hmenuCard, hmenuCover⟩ := hat.native_tag_domain_menus p
    (hp.subpower.1 k) hQ hq hqQ hχ hg hχg hχQg
  choose refinements hRefCard hRefCover using fun D : Code => refinement_domain_menu hQ hq hqQ hg D
  refine ⟨{
    law := cmp.law
    le_source := cmp.le.trans hζsource
    mass_lower := hmass
    parent := fun ω => (cmp.tru ω).1
    coarse := cmp.lab
    measurable_parent := measurable_fst.comp cmp.measurable_tru
    measurable_coarse := cmp.measurable_lab
    coarseChoices := fun Q tag => (menus Q tag).biUnion (cmp.partners Q)
    coarse_card := ?_
    reverseChoices := fun tag D j => (refinements (fullComparisonCode tag D)).biUnion (cmp.reverse j)
    reverse_card := ?_
    source_data := ?_ }⟩
  · intro Q tag
    exact (finiteMenuUnion_card (menus Q tag) (cmp.partners Q) (hmenuCard Q tag)
      (mul_nonneg (by norm_num) hB) (fun D _ => cmp.card_partners Q D)).trans hforward
  · intro tag D j
    exact (finiteMenuUnion_card (refinements (fullComparisonCode tag D)) (cmp.reverse j)
      (hRefCard _) hB (fun c _ => cmp.card_reverse j c)).trans hreverse
  · filter_upwards [cmp.source] with ω hω
    obtain ⟨_, hparent, htime, hcoarse, hforwardMem, hreverseMem, _⟩ := hω
    have hfit := (hL.2.2.2.2.2.1 (cmp.lab ω)).2.2.2.1 ω.1 hcoarse
    have hv : ⌊p.b k ω.1 3 / χ⌋ = L.tag (cmp.lab ω) 0 := hfit.1
    have hz : ⌊p.b k ω.1 0 / χ⌋ = L.tag (cmp.lab ω) 1 := hfit.2.1
    refine ⟨hparent, htime, hcoarse, ?_, ?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨code q χ g (q * g) (p.b k ω.1) ω.2, ?_, hforwardMem⟩
      exact hmenuCover (cmp.tru ω).1 (L.tag (cmp.lab ω)) ω hparent htime hv hz
    · have htag : (p.comparisonCode k m Q g (Q * g) ω).1 = L.tag (cmp.lab ω) := by
        ext i
        fin_cases i
        · exact hv
        · exact hz
      have hbig : code Q χ g (Q * g) (p.b k ω.1) ω.2 =
          fullComparisonCode (L.tag (cmp.lab ω)) (p.domainCode k Q g (Q * g) ω) := by
        have hh := (p.fullComparisonCode_comparisonCode k m Q g (Q * g) ω).symm
        rw [htag] at hh
        exact hh
      change (cmp.tru ω).1 ∈ (refinements
        (fullComparisonCode (L.tag (cmp.lab ω)) (p.domainCode k Q g (Q * g) ω))).biUnion
          (cmp.reverse (cmp.lab ω))
      exact Finset.mem_biUnion.mpr ⟨code q χ g (q * g) (p.b k ω.1) ω.2,
        hRefCover _ (p.b k ω.1) ω.2 hbig, hreverseMem⟩

end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
