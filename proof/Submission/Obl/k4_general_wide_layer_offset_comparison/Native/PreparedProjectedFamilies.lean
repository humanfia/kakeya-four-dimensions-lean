-- Adapted from this LOT tree, obligation o200, branch x0934, commit 2510f406, file Submission/Obl/k4_finite_projected_horizontal_candidates/PreparedProjectedFamilies.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.Native.
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.PreparedDomainMeshes
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ProjectedSourceFamilies

/-! Canonical projected sheets on every actual prepared comparison domain. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

def projectedSheetConstant : ℝ := Classical.choose exists_projected_source_family_constant

theorem projectedSheetConstant_pos : 0 < projectedSheetConstant :=
  (Classical.choose_spec exists_projected_source_family_constant).1

namespace PreparedDomainData

variable {α : Type} [MeasurableSpace α] {p : Parameters} {a : PreparedModel α}
  {k : ℕ} {s H q χ m : ℝ} {L : ProjLayer α} {ζ : Measure (α × ℝ)} {Extra : α × ℝ → Prop}
  (D : PreparedDomainData p a k s H q χ m L ζ Extra)

theorem exists_projected_families (hp : p.Valid) {La aTable : ℝ}
    (hL : L.Good (p.N k) H p.d p.ell La s χ (a.b k) (a.P k) (a.pi k) (a.rho k))
    (hH : 1 ≤ H) (hq : 0 < q) (hq1 : q ≤ 1) (hχ : 0 < χ) (hm : 0 < m)
    (hqg : q * PreparedModel.narrow p k s ≤ m) (hmβ : m ≤ L.β)
    (Kchart : NNReal) (hK : 4 * (projectedSheetConstant * H ^ 3) ≤ Kchart)
    (herr : 4 * (H * PreparedModel.width p k s) ≤ aTable)
    (M : ∀ u, ComparisonMesh (D.law u)) (hbase : ∀ u, (M u).base = D.base u) :
    ∃ (F : ∀ u, OriginalSheetFamily (D.law u) 4 aTable Kchart (M u).base
        (fun z => eval (a.x k z.1 z.2) (a.P k)))
      (idx : ∀ u, Fin (F u).n → Fin L.n),
      (∀ u, Function.Injective (idx u)) ∧
      (∀ u i z, z ∈ (F u).witness i → z ∈ D.core u ∧ z.1 ∈ L.C (idx u i)) ∧
      ∀ u i, ((F u).witness i).Nonempty →
        (F u).f i = projectedCandidate (L.G (idx u i)) q (PreparedModel.narrow p k s) m (D.decode u) := by
  have hN : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hp.1 k)
  have hconstructor := (Classical.choose_spec exists_projected_source_family_constant).2 (α := α)
  have hone (u : Fin D.n) :
      ∃ (F : OriginalSheetFamily (D.law u) 4 aTable Kchart (M u).base
          (fun z => eval (a.x k z.1 z.2) (a.P k)))
        (idx : Fin F.n → Fin L.n),
        Function.Injective idx ∧ (∀ i z, z ∈ F.witness i → z ∈ D.core u ∧ z.1 ∈ L.C (idx i)) ∧
        ∀ i, (F.witness i).Nonempty →
          F.f i = projectedCandidate (L.G (idx i)) q (PreparedModel.narrow p k s) m (D.decode u) := by
    rw [hbase u]
    obtain ⟨F, -, idx, hinj, hsource, hsame⟩ := hconstructor L
      (p.N k) H p.d p.ell La s χ q m aTable (a.b k) (a.P k) (a.pi k) (a.rho k) (D.law u)
      hL hN hH hχ hq hq1 hm hqg hmβ Kchart hK herr (D.positive_domain u) (D.decode u)
      (D.core u) (D.measurable_core u)
      (fun z hz => ⟨(D.core_point hz).1.time, (D.core_point hz).2⟩)
      ((D.core_ae u).mono fun z hz => ⟨hz, (D.core_point hz).1.projected_label⟩)
    exact ⟨F, idx, hinj, hsource, hsame⟩
  choose F idx hinj hsource hsame using hone
  exact ⟨F, idx, hinj, hsource, hsame⟩

end PreparedDomainData

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
