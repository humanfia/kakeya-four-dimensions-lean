-- Adapted from this LOT tree, obligation o200, branch x0934, commit 2510f406, file Submission/Obl/k4_finite_projected_horizontal_candidates/PreparedTrueFamilies.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.Native.
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.PreparedDomainMeshes
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.TrueSourceFactory

/-! The native true-family constructor on all actual prepared source domains. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

namespace PreparedDomainData

variable {α : Type} [MeasurableSpace α] {p : Parameters} {a : PreparedModel α}
  {k : ℕ} {s H q χ m : ℝ} {L : ProjLayer α} {ζ : Measure (α × ℝ)} {Extra : α × ℝ → Prop}
  (D : PreparedDomainData p a k s H q χ m L ζ Extra)

theorem exists_true_families {aTable : ℝ} (Kchart : NNReal)
    (E : Set (α × ℝ)) (assign : α × ℝ → Fin (a.n k s))
    (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ)
    (hfactory : TrueSourceFactory p a k s q χ m aTable Kchart E assign g)
    (hζ : ζ ≤ a.mu k) (hζE : ζ E = 0)
    (M : ∀ u, ComparisonMesh (D.law u)) (hbase : ∀ u, (M u).base = D.base u) :
    ∃ (F : ∀ u, OriginalSheetFamily (D.law u) 4 aTable Kchart (M u).base
        (fun z => eval (a.x k z.1 z.2) (a.P k)))
      (idx : ∀ u, Fin (F u).n → Fin (a.n k s) × Bool),
      (∀ u, Function.Injective (idx u)) ∧
      (∀ u i z, z ∈ (F u).witness i → z ∈ D.core u ∧
        z.1 ∈ a.B k s (idx u i).1 ∧ z.2 ∈ a.block k s (idx u i).1) ∧
      (∀ u i, ((F u).witness i).Nonempty →
        (F u).f i = trueCandidate p a k s g q χ (PreparedModel.narrow p k s) m (D.decode u) (idx u i)) ∧
      ∀ u, ∀ᵐ z ∂D.law u, idx u ((F u).index z) = (assign z, nativeBranch p a k s (assign z) z) := by
  have hone (u : Fin D.n) :
      ∃ (F : OriginalSheetFamily (D.law u) 4 aTable Kchart (M u).base
          (fun z => eval (a.x k z.1 z.2) (a.P k)))
        (idx : Fin F.n → Fin (a.n k s) × Bool),
        Function.Injective idx ∧
        (∀ i z, z ∈ F.witness i → z ∈ D.core u ∧
          z.1 ∈ a.B k s (idx i).1 ∧ z.2 ∈ a.block k s (idx i).1) ∧
        (∀ i, (F.witness i).Nonempty →
          F.f i = trueCandidate p a k s g q χ (PreparedModel.narrow p k s) m (D.decode u) (idx i)) ∧
        ∀ᵐ z ∂D.law u, idx (F.index z) = (assign z, nativeBranch p a k s (assign z) z) := by
    have hle : D.law u ≤ ζ := Measure.restrict_le_self
    have hE0 : D.law u E = 0 := le_antisymm ((hle E).trans hζE.le) bot_le
    have hcode : ∀ᵐ z ∂D.law u,
        CommonDomain.code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2 = D.decode u :=
      (D.core_ae u).mono fun z hz => (D.core_point hz).2
    rw [hbase u]
    obtain ⟨F, idx, hinj, hsource, hsame, hcurrent⟩ :=
      hfactory (D.law u) (D.decode u) (Measure.absolutelyContinuous_of_le (hle.trans hζ)) hE0 hcode
    let F' := F.trim (D.core u) (D.measurable_core u) (D.core_ae u)
    refine ⟨F', idx, hinj, ?_, ?_, hcurrent⟩
    · intro i z hz
      exact ⟨hz.2, hsource i z hz.1⟩
    · intro i hi
      obtain ⟨z, hz⟩ := hi
      exact hsame i z hz.1
  choose F idx hinj hsource hsame hcurrent using hone
  exact ⟨F, idx, hinj, hsource, hsame, hcurrent⟩

end PreparedDomainData

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
