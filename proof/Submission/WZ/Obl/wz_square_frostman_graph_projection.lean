-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GraphSquareExpansion
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_square_frostman_graph_projection`

Specialize the finite graph expansion theorem to graph exponent `1 + b` and
scalar exponent `β`. Lifting the finite sets to finsets identifies square
counts, interval counts, and coordinate-image cardinalities. The selected
scalar is then used for every dense subset of the original graph.
-/

theorem WangZahlLot.wz_square_frostman_graph_projection : ∀ e b β : ℝ, 0 < e → 0 < b → 0 < β → ∃ ζ δ₀ : ℝ, 0 < ζ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ α C : ℝ, 0 < δ → δ ≤ δ₀ → 0 ≤ α → α ≤ 1 - e → 1 ≤ C → C ≤ δ ^ (-ζ) → ∀ (G : Set (ℝ × ℝ)) (S : Set ℝ), G.Finite → G.Nonempty → S.Finite → S.Nonempty → (∀ p ∈ G, |p.1| ≤ 4 ∧ |p.2| ≤ 4) → (∀ x y ρ : ℝ, δ ≤ ρ → ({p ∈ G | dist p.1 x ≤ ρ ∧ dist p.2 y ≤ ρ}.ncard : ℝ) ≤ C * ρ ^ (1 + b) * G.ncard) → (∀ x ρ : ℝ, δ ≤ ρ → ((S ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ C * ρ ^ β * S.ncard) → (∀ t ∈ S, t ∈ Set.Icc (0 : ℝ) 1) → (∀ a ∈ Prod.fst '' G, ∀ a' ∈ Prod.fst '' G, a ≠ a' → δ ≤ dist a a') → (∀ a ∈ Prod.snd '' G, ∀ a' ∈ Prod.snd '' G, a ≠ a' → δ ≤ dist a a') → ((Prod.fst '' G).ncard : ℝ) ≤ δ ^ (-α - ζ) → ((Prod.snd '' G).ncard : ℝ) ≤ δ ^ (-α - ζ) → δ ^ (ζ - 2 * α) ≤ (G.ncard : ℝ) → ∃ t ∈ S, ∀ H : Set (ℝ × ℝ), H ⊆ G → δ ^ ζ * G.ncard ≤ (H.ncard : ℝ) → ∀ (m : ℕ) (cc : Fin m → ℝ), (fun p : ℝ × ℝ => p.1 + t * p.2) '' H ⊆ (⋃ j, Metric.closedBall (cc j) δ) → δ ^ (-α - ζ) ≤ (m : ℝ) := by
  classical
  intro e b β he hb hβ
  obtain ⟨ζ, δ₀, hζ, hδ₀, hδ₀1, hproject⟩ :=
    WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.graph_square_expansion e b β he hb hβ
  refine ⟨ζ, δ₀, hζ, hδ₀, hδ₀1, ?_⟩
  intro δ α C hδ hδsmall hα hαmax hC hCmax G S hGfin hGne hSfin hSne
    hbound hGF hSF hSunit hAsep hBsep hAc hBc hGc
  lift G to Finset (ℝ × ℝ) using hGfin
  lift S to Finset ℝ using hSfin
  have hGF' : WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RectangleFrostman
      δ C (1 + b) G := by
    intro x y ρ hρ
    have hh := hGF x y ρ hρ
    have heq : {p ∈ (↑G : Set (ℝ × ℝ)) | dist p.1 x ≤ ρ ∧ dist p.2 y ≤ ρ} =
        ↑(G.filter (fun p => dist p.1 x ≤ ρ ∧ dist p.2 y ≤ ρ)) := by
      ext p
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter]
    rw [heq, Set.ncard_coe_finset, Set.ncard_coe_finset] at hh
    exact hh
  have hSF' : WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RealFiniteFrostman
      δ C β S := by
    intro x ρ hρ
    have hh := hSF x ρ hρ
    have heq : (↑S : Set ℝ) ∩ Metric.closedBall x ρ =
        ↑(S.filter (fun t => dist t x ≤ ρ)) := by
      ext t
      simp only [Set.mem_inter_iff, Finset.mem_coe, Metric.mem_closedBall, Finset.mem_filter]
    rw [heq, Set.ncard_coe_finset, Set.ncard_coe_finset] at hh
    exact hh
  obtain ⟨t, ht, hexpand⟩ := hproject δ α (1 + b) β C hδ hδsmall hα hαmax
    le_rfl le_rfl hC hCmax G S
    (by simpa only [Finset.coe_nonempty] using hGne)
    (by simpa only [Finset.coe_nonempty] using hSne)
    hbound hGF' hSF' hSunit
    (by simpa only [← Finset.coe_image, Finset.mem_coe] using hAsep)
    (by simpa only [← Finset.coe_image, Finset.mem_coe] using hBsep)
    (by simpa only [← Finset.coe_image, Set.ncard_coe_finset] using hAc)
    (by simpa only [← Finset.coe_image, Set.ncard_coe_finset] using hBc)
    (by simpa only [Set.ncard_coe_finset] using hGc)
  refine ⟨t, ht, ?_⟩
  intro H hHG hH m cc hcover
  lift H to Finset (ℝ × ℝ) using G.finite_toSet.subset hHG
  exact hexpand H hHG (by simpa only [Set.ncard_coe_finset] using hH) m cc hcover
