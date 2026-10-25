import Mathlib
import ChallengeDeps
import Submission.Obl.k4_graph_bsg.RetainedPaths
import Submission.Obl.k4_graph_bsg.TripleCount
set_option linter.unusedVariables false

/-!
# `Submission.k4_graph_bsg`

Graph Balog–Szemerédi–Gowers with retained edges (paper Lemma 7.1, `re:graph-bsg`), with
`c = 1/36` and `C₀ = 6144`. `retained_paths` (graph part, built on the WZ path lemma's
popular vertex) gives `A' ⊆ A`, `B' ⊆ B` with many retained edges and many paths of length three
between every pair of `A' × B'`; `triple_count` turns the paths into the sumset bound.
-/

theorem Submission.k4_graph_bsg : ∃ c C₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ ∀ (G : Type) [AddCommGroup G] [DecidableEq G] (A B : Finset G) (E : Finset (G × G)) (θ : ℝ), A.Nonempty → B.Nonempty → E ⊆ A ×ˢ B → 0 < θ → θ ≤ 1 → θ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ) → ∃ A' : Finset G, ∃ B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧ c * θ * (A.card : ℝ) ≤ (A'.card : ℝ) ∧ c * θ * (B.card : ℝ) ≤ (B'.card : ℝ) ∧ c * θ ^ 2 * (A.card : ℝ) * (B.card : ℝ) ≤ ((E ∩ A' ×ˢ B').card : ℝ) ∧ (((A' ×ˢ B').image (fun p : G × G => p.1 + p.2)).card : ℝ) ≤ C₀ * (θ ^ 5)⁻¹ * ((E.image (fun p : G × G => p.1 + p.2)).card : ℝ) ^ 3 / ((A.card : ℝ) * (B.card : ℝ)) := by
  refine ⟨1 / 36, 6144, by norm_num, by norm_num, ?_⟩
  intro G _ _ A B E θ hA hB hE hθ _ hdense
  obtain ⟨A', hA'A, B', hB'B, hA'card, hB'card, hedges, hpaths⟩ :=
    Submission.Obl.k4_graph_bsg.retained_paths A B E hE hA hB hθ hdense
  have ha : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hK : 0 < θ ^ 5 * (A.card : ℝ) * (B.card : ℝ) / 6144 := by positivity
  have key := Submission.Obl.k4_graph_bsg.triple_count A B A' B' E _ hpaths
  refine ⟨A', B', hA'A, hB'B, ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ θ * (A.card : ℝ) := by positivity
    linarith
  · have : 0 ≤ θ * (B.card : ℝ) := by positivity
    linarith
  · linarith
  · have e : (6144 : ℝ) * (θ ^ 5)⁻¹ * ((E.image (fun p : G × G => p.1 + p.2)).card : ℝ) ^ 3 /
        ((A.card : ℝ) * (B.card : ℝ)) = ((E.image (fun p : G × G => p.1 + p.2)).card : ℝ) ^ 3 /
        (θ ^ 5 * (A.card : ℝ) * (B.card : ℝ) / 6144) := by
      field_simp
    rw [e, le_div_iff₀ hK]
    exact key
