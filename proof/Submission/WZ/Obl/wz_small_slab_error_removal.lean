-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_slab_error_removal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_small_slab_error_removal.Elementary
import Submission.WZ.Obl.wz_convex_container_tube_packing
import Submission.WZ.Obl.wz_balanced_small_slab_reduction
import Submission.WZ.Obl.wz_small_slab_error_removal.AbstractTransfer

open WangZahlLot.Obl.wz_small_slab_error_removal
open WangZahlLot.Obl.wz_small_slab_error_removal.Model
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_small_slab_error_removal`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_small_slab_error_removal`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_small_slab_error_removal/`
belong to this obligation.
-/

theorem WangZahlLot.wz_small_slab_error_removal : ∀ σ ω : ℝ, (fun (T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop → Prop) => (fun (J : (ℝ → ℝ → ℝ → ℝ → Prop) → Prop) => (fun (Q : ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) => (fun (e : ℝ → ℝ → Prop) => (fun (r : ℝ → ℝ → Prop) => 0 < σ → σ ≤ (1/2 : ℝ) → 0 < ω → r σ ω → e σ ω) (fun s w => J (fun ε a η δ => ∀ m : ℝ, 1 ≤ m → Q η δ m (δ ^ (-η)) (fun N => a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * (N * δ)) ^ (-s))))) (fun s w => J (fun ε a η δ => ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → Q η δ m l (fun N => a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * l * (N * δ)) ^ (-s))))) (fun η δ m l f => ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y ((∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤ ENNReal.ofReal (l * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r})) → ENNReal.ofReal (f n) ≤ MeasureTheory.volume (⋃ i, Y i)))) (fun P => ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → P ε a η δ)) (fun η δ n x v Y P => 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i)) → P)) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v))) := by
  intro σ ω hσ hσle hω hR
  have hp : Packing := WangZahlLot.wz_convex_container_tube_packing
  have hg : Reduction Family := WangZahlLot.wz_balanced_small_slab_reduction hp
  obtain ⟨C, hC, hb⟩ := family_bounds hp
  have hr : Model.Restricted Family σ ω := by
    intro ε hε
    obtain ⟨a, ha, η, hη, h⟩ := hR ε hε
    refine ⟨a, ha, η, hη, ?_⟩
    intro δ hδ hδ100 m hm n U hF
    obtain ⟨x, v, Y, hA, hK, hS, rfl⟩ := hF
    obtain ⟨hn, hv, hball, ho, hY, hsub, hden⟩ := hA
    exact h δ hδ hδ100 m hm n x v Y hn hv hball ho hY hsub hden hK hS
  have he : Model.General Family σ ω :=
    Model.transfer hC family_mono hb hg hσ hσle hω hr
  intro ε hε
  obtain ⟨a, ha, η, hη, h⟩ := he ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 m l hm hl n x v Y hn hv hball ho hY hsub hden hK hS
  exact h δ hδ hδ100 m l hm hl n (MeasureTheory.volume (⋃ i, Y i))
    ⟨x, v, Y, ⟨hn, hv, hball, ho, hY, hsub, hden⟩, hK, hS, rfl⟩
