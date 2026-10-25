-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_balanced_affine_tube_packets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_balanced_affine_tube_packets.Interfaces
import Submission.WZ.Obl.wz_regular_transverse_affine_cells
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover
import Submission.WZ.Obl.wz_weighted_affine_packet_balancing
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_balanced_affine_tube_packets`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_balanced_affine_tube_packets`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_balanced_affine_tube_packets/`
belong to this obligation.
-/

open WangZahlLot.Obl.wz_balanced_affine_tube_packets

set_option maxRecDepth 4096 in
theorem WangZahlLot.wz_balanced_affine_tube_packets : (fun (B : Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun (T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun (A : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop) => (fun (L : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) => (fun (R : ℝ → ℝ → ℝ → ℝ → (n k N q : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin k → Fin N → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin k → Fin N → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) => ∀ e : ℝ, 0 < e → ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (1/100 : ℝ) ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), A (δ ^ η) δ n x v Y → ∃ k N q : ℕ, 0 < k ∧ 0 < N ∧ 0 < q ∧ ∃ ρ t : ℝ, δ ^ (1 + e) ≤ ρ ∧ ρ ≤ (1/100 : ℝ) ∧ 0 < t ∧ ∃ (z w : Fin k → Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (Z : Fin k → Fin N → Set LeanEval.Analysis.WangZahlKakeya.Space), R δ (δ ^ e) ρ t n k N q x v z w ∧ (∀ j, A (δ ^ e) ρ N (z j) (w j) (Z j) ∧ L ρ ((δ ^ e)⁻¹) N (z j) (w j)) ∧ ENNReal.ofReal (δ ^ e * t) * Finset.sum Finset.univ (fun j => MeasureTheory.volume (⋃ a, Z j a)) ≤ MeasureTheory.volume (⋃ i, Y i)) (fun δ h ρ t (n k N q : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (z w : Fin k → Fin N → LeanEval.Analysis.WangZahlKakeya.Space) => ∃ (F : Fin k → Fin N → Finset (Fin n)) (f : Fin k → AffineEquiv ℝ LeanEval.Analysis.WangZahlKakeya.Space LeanEval.Analysis.WangZahlKakeya.Space), (∀ j a, (F j a).card = q) ∧ (∀ j a b, a ≠ b → Disjoint (F j a) (F j b)) ∧ h * (n : ℝ) ≤ (k : ℝ) * (N : ℝ) * (q : ℝ) ∧ (∀ j a i, i ∈ F j a → T δ (x i) (v i) ⊆ f j '' T ρ (z j a) (w j a)) ∧ (∀ j (Q : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ Q → MeasureTheory.volume (f j '' Q ∩ B) ≤ ENNReal.ofReal (t / h) * MeasureTheory.volume Q))) (fun δ l (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (a r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ (B ∩ {p | |inner ℝ u p - a| ≤ r})} : ℝ) ≤ ENNReal.ofReal (l * (n : ℝ)) * MeasureTheory.volume (B ∩ {p | |inner ℝ u p - a| ≤ r}))) (fun d δ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) => 0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, T δ (x i) (v i) ⊆ B) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) ∧ (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ T δ (x i) (v i)) ∧ ENNReal.ofReal (d * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i)))) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v)))) (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) := by
  change ∀ e : ℝ, 0 < e →
    ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (1/100 : ℝ) ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (n : ℕ) (x v : Fin n → E) (Y : Fin n → Set E),
      admissible (δ ^ η) δ n x v Y → conclusion e δ n x v Y
  intro e he
  have balance : ∀ e : ℝ, 0 < e →
      ∃ s : ℝ, 0 < s ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (1/100 : ℝ) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (n : ℕ) (x v : Fin n → E) (Y : Fin n → Set E),
        weighted δ (δ ^ s) n x v Y → conclusion e δ n x v Y :=
    WangZahlLot.wz_weighted_affine_packet_balancing
  obtain ⟨s, hs, d₃, hd₃, _, hbalance⟩ := balance e he
  have cover : ∀ s : ℝ, 0 < s →
      ∃ r : ℝ, 0 < r ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (1/100 : ℝ) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (n : ℕ) (x v : Fin n → E) (Y : Fin n → Set E),
        cells δ (δ ^ r) n x v Y → weighted δ (δ ^ s) n x v Y :=
    WangZahlLot.wz_transverse_cell_weighted_cover
  obtain ⟨r, hr, d₂, hd₂, _, hcover⟩ := cover s hs
  have extract : ∀ r : ℝ, 0 < r →
      ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (1/100 : ℝ) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (n : ℕ) (x v : Fin n → E) (Y : Fin n → Set E),
        admissible (δ ^ η) δ n x v Y → cells δ (δ ^ r) n x v Y :=
    WangZahlLot.wz_regular_transverse_affine_cells
  obtain ⟨η, hη, d₁, hd₁, hd₁small, hextract⟩ := extract r hr
  refine ⟨η, hη, min d₁ (min d₂ d₃),
    lt_min hd₁ (lt_min hd₂ hd₃),
    (min_le_left _ _).trans hd₁small, ?_⟩
  intro δ hδ hδsmall n x v Y hA
  have hδ₁ : δ ≤ d₁ := hδsmall.trans (min_le_left _ _)
  have hδ₂ : δ ≤ d₂ :=
    hδsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₃ : δ ≤ d₃ :=
    hδsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  exact hbalance δ hδ hδ₃ n x v Y
    (hcover δ hδ hδ₂ n x v Y (hextract δ hδ hδ₁ n x v Y hA))
