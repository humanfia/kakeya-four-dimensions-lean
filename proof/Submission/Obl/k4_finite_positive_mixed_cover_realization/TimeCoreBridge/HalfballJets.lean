-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/HalfballJets.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/HalfballJets.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Directional
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.JetLabels

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Set Metric Finset

/-- Both comparisons use the same half-ball as the separated-pair estimate.
The accepted coefficient-independent sheet norm bound supplies the upper comparison. -/
theorem exists_halfball_directional_jet_system (D : ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ V : Finset Real3, (∀ v ∈ V, ‖v‖ = 1) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∀ f g : RealSheet D,
        (∀ x : Real3, ‖x‖ ≤ (1 : ℝ) / 2 →
          c * ‖f.f (emb x) - g.f (emb x)‖ ≤
            ∑ i : V × Fin (K + 1),
              |directionalJets V K f.f i - directionalJets V K g.f i|) ∧
        (∀ A : ℝ, 0 < A →
          (∀ x : Real3, ‖x‖ ≤ (1 : ℝ) / 2 → ‖f.f (emb x) - g.f (emb x)‖ ≤ A) →
          ∀ i : V × Fin (K + 1),
            |directionalJets V K f.f i - directionalJets V K g.f i| ≤ B i.2.val * A) := by
  obtain ⟨K, hK, V, hV, c, hc, B, hB, hcompare⟩ := exists_directional_jet_system D
  obtain ⟨E, hE⟩ :=
    Submission.Obl.k4_algebraic_real_jet_comparison.exists_sheet_difference_degree 3 D
  obtain ⟨C, hC, hnorm⟩ :=
    Submission.Obl.k4_algebraic_real_jet_comparison.exists_sheet_norm_constant 3 E
  have hCpos : 0 < C := by linarith
  refine ⟨K, hK, V, hV, c, hc, (fun m => B m * C),
    (fun m => mul_pos (hB m) hCpos), ?_⟩
  intro f g
  refine ⟨(hcompare f g).1, ?_⟩
  intro A hA hhalf i
  have hrel := hE f.f g.f ⟨f.P, f.nonzero, f.degree, f.equation⟩
    ⟨g.P, g.nonzero, g.degree, g.equation⟩
  have hcomplex := hnorm (fun z => f.f z - g.f z) hrel
    (f.holomorphic.sub g.holomorphic) A hA hhalf
  have hunit (x : Real3) (hx : ‖x‖ ≤ 1) :
      ‖f.f (emb x) - g.f (emb x)‖ ≤ C * A :=
    hcomplex (emb x) (by simpa only [emb.norm_map] using hx)
  simpa only [mul_assoc] using (hcompare f g).2 (C * A) (mul_pos hCpos hA) hunit i

/-- Merging a finite jet label controls every member by its chosen representative
on the complete comparison half-ball. -/
theorem sheet_bin_representative_bound {D K : ℕ} {V : Finset Real3} {c : ℝ}
    (hc : 0 < c) {α : Type*} [Fintype α] (F : α → RealSheet D)
    (width : (V × Fin (K + 1)) → ℝ) (hw : ∀ i, 0 < width i)
    (hcompare : ∀ a b (x : Real3), ‖x‖ ≤ (1 : ℝ) / 2 →
      c * ‖(F a).f (emb x) - (F b).f (emb x)‖ ≤
        ∑ i, |directionalJets V K (F a).f i - directionalJets V K (F b).f i|)
    (a : α) (x : Real3) (hx : ‖x‖ ≤ (1 : ℝ) / 2) :
    ‖(F a).f (emb x) -
        (F (binRepresentative width (fun a => directionalJets V K (F a).f)
          (mergedLabel width (fun a => directionalJets V K (F a).f) a))).f (emb x)‖ ≤
      (∑ i, width i) / c := by
  apply gap_le_of_binVector_eq (jet := fun a => directionalJets V K (F a).f) hw
    (same_label_as_representative width (fun a => directionalJets V K (F a).f) a) hc
  exact hcompare _ _ x hx

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
