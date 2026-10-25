-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/MatchingRecovery.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.Matching
import Submission.Obl.k4_clean_cover_graph_atlas.JetLabels
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Finset

/-- Every pointwise matched pair either has neighboring jet bins or is one of the
globally separated pairs controlled by local graph matching. -/
theorem jet_neighbor_pair_cover {n : ℕ} {ι : Type*} [Fintype ι]
    (f : Fin n → Complex3 → ℂ) (jet : Fin n → ι → ℝ) (width : ι → ℝ)
    (hw : ∀ i, 0 < width i) (R M ε : ℝ)
    (hjet : ∀ a b, (∀ x : Real3, ‖x‖ ≤ (1 : ℝ) / 2 →
      ‖f a (emb x) - f b (emb x)‖ ≤ M * R ^ (-ε)) →
      ∀ i, |jet a i - jet b i| ≤ width i)
    (μ : Measure ((Fin n × Fin n) × Real3))
    (hsupport : μ {p | ‖p.2‖ ≤ (1 : ℝ) / 2 ∧
      ‖f p.1.1 (emb p.2) - f p.1.2 (emb p.2)‖ ≤ M * R ^ (-1 + ε)}ᶜ = 0) :
    μ univ ≤ μ {p | ∀ i, |binVector width jet p.1.1 i - binVector width jet p.1.2 i| ≤ 1} +
      μ (badPairs f f R M ε) := by
  classical
  let S : Set ((Fin n × Fin n) × Real3) := {p | ‖p.2‖ ≤ (1 : ℝ) / 2 ∧
    ‖f p.1.1 (emb p.2) - f p.1.2 (emb p.2)‖ ≤ M * R ^ (-1 + ε)}
  have hcover : S ⊆ {p | ∀ i,
      |binVector width jet p.1.1 i - binVector width jet p.1.2 i| ≤ 1} ∪ badPairs f f R M ε := by
    intro p hp
    by_cases hn : ∀ i, |binVector width jet p.1.1 i - binVector width jet p.1.2 i| ≤ 1
    · exact Or.inl hn
    · right
      refine ⟨hp.1, hp.2, ?_⟩
      by_contra! hsep
      apply hn
      exact binVector_near hw (hjet p.1.1 p.1.2 (fun x hx => (hsep x hx).le))
  calc
    _ = μ (S ∪ Sᶜ) := by rw [union_compl_self]
    _ ≤ μ S + μ Sᶜ := measure_union_le _ _
    _ = μ S := by rw [hsupport, add_zero]
    _ ≤ μ ({p | ∀ i, |binVector width jet p.1.1 i - binVector width jet p.1.2 i| ≤ 1} ∪
        badPairs f f R M ε) := measure_mono hcover
    _ ≤ _ := measure_union_le _ _

/-- Original packet scales can be summed before recovering a list-success floor. -/
theorem weighted_pair_agreement_floor {Γ X : Type*} [Fintype Γ] [MeasurableSpace X]
    (μ : Γ → Measure X) (w : Γ → ENNReal) (E : Γ → Set X) (err : Γ → ENNReal)
    (hcover : ∀ g, μ g univ ≤ μ g (E g) + err g)
    {m : ℝ} (hm : 0 ≤ m) (hmass : ENNReal.ofReal m ≤ ∑ g, w g * μ g univ)
    (herr : ∑ g, w g * err g ≤ ENNReal.ofReal (m / 2)) :
    ENNReal.ofReal (m / 2) ≤ ∑ g, w g * μ g (E g) := by
  apply Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
    _ _ _ m hm hmass _ herr
  calc
    _ ≤ ∑ g, w g * (μ g (E g) + err g) :=
      sum_le_sum fun g _ => mul_le_mul' le_rfl (hcover g)
    _ = _ := by simp only [mul_add, sum_add_distrib]

end Submission.Obl.k4_clean_cover_graph_atlas
