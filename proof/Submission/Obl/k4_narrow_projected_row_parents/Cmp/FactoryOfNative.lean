import Submission.Obl.k4_narrow_projected_row_parents.Cmp.TrueSourceFactory

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel

noncomputable section

/-- The actual native-sheet data provide the precise family constructor
consumed by `prepared_comparison_at`. The true priority assignment and its
native branch are retained in every domain. -/
theorem exists_true_source_factory_of_native {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    {R : ℝ} {k : ℕ} {s : ℝ} (hs : 0 ≤ s) (hatlas : a.AtlasAt p R k s)
    (Rel : Fin (a.n k s) → MvPolynomial (Fin 4) ℂ)
    (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ)
    (E : Set (α × ℝ)) (hE : MeasurableSet E) {ρ V err : ℝ}
    (hRel : ∀ i, Rel i ≠ 0 ∧ (Rel i).totalDegree ≤ 4)
    (hae : ∀ i, ∀ᵐ z ∂a.mu k, z ∈ a.parentSet k s i → z ∉ E →
      SheetOn (Rel i) (g i (nativeBranch p a k s i z))
          (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z))) (4 * ρ) V ∧
        |eval (a.x k z.1 z.2) (a.P k) -
          (g i (nativeBranch p a k s i z)
            (emb (toEuc (rootBaseCoordinates (parentZoomPoint p a k s i z))))).re| ≤ err)
    (aT : ℝ) (Kc : NNReal) (hV : 0 ≤ V) (hKc : 4 * V ≤ Kc) (herr : err ≤ aT / 4)
    {q χ m : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hχg : χ ≤ narrow p k s) (hm : 0 < m) (hqg : q * narrow p k s ≤ m)
    (hρ : 0 < ρ) (hqsmall : q ≤ ρ * a.q k s / 10000)
    (hχsmall : χ ≤ ρ * (a.q k s * narrow p k s) / 10000)
    (hmsmall : m ≤ ρ * (a.q k s * narrow p k s) / 10000) :
    ∃ assign : α × ℝ → Fin (a.n k s), Measurable assign ∧
      TrueSourceFactory p a k s q χ m aT Kc E assign g := by
  obtain ⟨assign, hassign, -, -, hfamilies⟩ :=
    exists_true_source_families p hp a hcommon hs hatlas Rel g E hE hRel hae
      aT Kc hV hKc herr hq hχ hχ1 hχg hm hqg hρ hqsmall hχsmall hmsmall
  refine ⟨assign, hassign, ?_⟩
  intro μD c hac hE0 hcode
  obtain ⟨F, idx, hinj, hsource, hsame, hcurrent⟩ := hfamilies μD c hac hE0 hcode
  refine ⟨F, idx, hinj, ?_, hsame, hcurrent⟩
  intro i z hz
  obtain ⟨hdecode, hpriority, -⟩ := hsource i z hz
  rw [hdecode]
  exact hpriority.1

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
