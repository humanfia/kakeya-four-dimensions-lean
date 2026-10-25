-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_packet_counting_transfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.Counting
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.Arithmetic
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.GeometricEstimates
set_option linter.unusedVariables false

/-!
# Affine packet counting transfer

Disjoint packet fibers transfer convex counts. Applying the supplied slab cover to one
whole cell gives the slab estimate; applying packing to one injectively reindexed fiber
gives the final density bound. A common constant absorbs all three estimates.
-/

open WangZahlLot.Obl.wz_affine_packet_counting_transfer in
theorem WangZahlLot.wz_affine_packet_counting_transfer : (fun (B : Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun (T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun (K : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) => (fun (L : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) => (fun (R : ℝ → ℝ → ℝ → ℝ → (n k N q : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin k → Fin N → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin k → Fin N → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) => (fun (SlabCover : Prop) => (fun (Packing : Prop) => SlabCover → Packing → ∃ C : ℝ, 1 ≤ C ∧ ∀ δ ρ h t : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → 0 < ρ → ρ ≤ (1/100 : ℝ) → 0 < h → h ≤ 1 → 0 < t → ∀ n k N q : ℕ, 0 < n → 0 < k → 0 < N → 0 < q → ∀ (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (z w : Fin k → Fin N → LeanEval.Analysis.WangZahlKakeya.Space), (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) → (∀ j a, ‖w j a‖ = 1) → (∀ j a, T ρ (z j a) (w j a) ⊆ B) → R δ h ρ t n k N q x v z w → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → K δ m n x v → L δ l n x v → ∃ M : ℝ, 1 ≤ M ∧ (∀ j, K ρ M N (z j) (w j)) ∧ M ≤ (C / h ^ 2) * m * ((k : ℝ) * t * (N : ℝ) * ρ ^ 2) / ((n : ℝ) * δ ^ 2) ∧ h ^ 2 ≤ C * l * (k : ℝ) * t ^ (1/2 : ℝ) ∧ δ ^ 2 * ((n : ℝ) / ((k : ℝ) * (N : ℝ))) ^ (1/2 : ℝ) ≤ (C / h ^ 2) * t * ρ ^ 2) (∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → W ⊆ B → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ W) → (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) → ENNReal.ofReal ((n : ℝ) * δ ^ 4) ≤ ENNReal.ofReal C * (MeasureTheory.volume W) ^ 2)) (∃ C : ℝ, 1 ≤ C ∧ ∀ (s : ℝ) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < s → Convex ℝ W → W ⊆ B → MeasureTheory.volume W ≤ ENNReal.ofReal s → (∃ x v : LeanEval.Analysis.WangZahlKakeya.Space, ‖v‖ = 1 ∧ segment ℝ x (x + v) ⊆ W) → ∃ (u : LeanEval.Analysis.WangZahlKakeya.Space) (a r : ℝ), ‖u‖ = 1 ∧ 0 < r ∧ W ⊆ (B ∩ {p | |inner ℝ u p - a| ≤ r}) ∧ MeasureTheory.volume (B ∩ {p | |inner ℝ u p - a| ≤ r}) ≤ ENNReal.ofReal (C * s ^ (1/2 : ℝ)))) (fun δ h ρ t (n k N q : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (z w : Fin k → Fin N → LeanEval.Analysis.WangZahlKakeya.Space) => ∃ (F : Fin k → Fin N → Finset (Fin n)) (f : Fin k → AffineEquiv ℝ LeanEval.Analysis.WangZahlKakeya.Space LeanEval.Analysis.WangZahlKakeya.Space), (∀ j a, (F j a).card = q) ∧ (∀ j a b, a ≠ b → Disjoint (F j a) (F j b)) ∧ h * (n : ℝ) ≤ (k : ℝ) * (N : ℝ) * (q : ℝ) ∧ (∀ j a i, i ∈ F j a → T δ (x i) (v i) ⊆ f j '' T ρ (z j a) (w j a)) ∧ (∀ j (Q : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ Q → MeasureTheory.volume (f j '' Q ∩ B) ≤ ENNReal.ofReal (t / h) * MeasureTheory.volume Q))) (fun δ l (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (a r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ (B ∩ {p | |inner ℝ u p - a| ≤ r})} : ℝ) ≤ ENNReal.ofReal (l * (n : ℝ)) * MeasureTheory.volume (B ∩ {p | |inner ℝ u p - a| ≤ r}))) (fun δ m (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ Q : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ Q → ENNReal.ofReal ((Set.ncard {i | T δ (x i) (v i) ⊆ Q} : ℝ) * δ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume Q)) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v)))) (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) := by
  classical
  dsimp only
  rintro ⟨Cs, hCs, hcover⟩ ⟨Cp, hCp, hpacking⟩
  have hCs0 : 0 ≤ Cs := by linarith
  have hCp0 : 0 ≤ Cp := by linarith
  let C : ℝ := 384 + 4 * Cs + 384 * Cp
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  have hC384 : 384 ≤ C := by dsimp [C]; linarith
  have hCsC : 4 * Cs ≤ C := by dsimp [C]; linarith
  have hCpC : 384 * Cp ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC1, ?_⟩
  intro δ ρ h t hδ hδ1 hρ hρ1 hh hh1 ht n k N q hn hk hN hq
    x v z w hv hB hdist hw houtB hR m l hm hl hK hL
  obtain ⟨F, f, hcard, hdisj, hbalance, hsub, hvol⟩ := hR
  have hm0 : 0 ≤ m := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hρone : ρ ≤ 1 := by linarith
  let A : ℝ := m * (t / h) * ρ ^ 2 / ((q : ℝ) * δ ^ 2)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hKA : ∀ j, ConvexCount ρ A N (z j) (w j) := by
    intro j
    exact convex_transfer hδ hρ hh ht hm0 hq x v (z j) (w j) (F j) (f j)
      (hcard j) (hdisj j) hB (hsub j) (hvol j) hK
  let j : Fin k := ⟨0, hk⟩
  have hM1 : 1 ≤ 384 * A :=
    constant_lower hρ hρone hA0 hN (z j) (w j) (hw j) (hKA j)
  refine ⟨384 * A, hM1, ?_, ?_, ?_, ?_⟩
  · intro j
    exact convex_count_mono (by nlinarith) (hKA j)
  · exact convex_arithmetic hC384 hδ hρ hh ht hm0 hn' hk' hN' hq' hbalance
  · have hs := slab_cell hCs0 hcover hδ hh ht hl0 hN hq x v (z j) (w j) (F j) (f j)
      (hcard j) (hdisj j) hv hB (houtB j) (hsub j) (hvol j) hL
    exact slab_arithmetic hCsC hCs0 hh hh1 ht hl0 hn' hk' hbalance hs
  · let a : Fin N := ⟨0, hN⟩
    have hp := packing_fiber hCp0 hpacking hδ hδ1 hρ hρone hh ht x v (z j a) (w j a)
      (F j a) (f j) (hcard j a) hv (hw j a) hB (hsub j a) hdist (hvol j)
    exact packing_arithmetic hCpC hCp hδ hρ hh hh1 ht hn' hk' hN' hq' hbalance hp
