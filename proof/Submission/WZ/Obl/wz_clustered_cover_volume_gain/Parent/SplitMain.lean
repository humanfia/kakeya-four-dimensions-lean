-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SplitMain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.SplitProposal

/-!
# The o019 statement from the three frozen children of the proposed split

`main_of_frozen_children` is the whole glue of the proposed split: once the children are frozen
with the types `SplitTypes.flatFrozen`, `SplitTypes.grainsFrozen`, `SplitTypes.gainFrozen`, the main
file is `main_of_frozen_children child₁ child₂ child₃`.
-/

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open Interfaces

theorem main_of_frozen_children (hflat : SplitTypes.flatFrozen)
    (hgrains : SplitTypes.grainsFrozen) (hgain : SplitTypes.gainFrozen) :
    ∀ σ ω : ℝ, 0 < σ → σ ≤ (1 / 2 : ℝ) → 0 < ω → ω ≤ 1 → ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ K, K = (fun (d m : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ W, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T d (x i) (v i) ⊆ W} * d ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → ∀ F, F = (fun (d l : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | T d (x i) (v i) ⊆ Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}}) ≤ ENNReal.ofReal (l * n) * MeasureTheory.volume (Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r})) → ∀ A, A = (fun (d η m l : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) => 0 < n ∧ (∀ i, ‖v i‖ = 1 ∧ T d (x i) (v i) ⊆ Metric.ball 0 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T d (x i) (v i)) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T d (x i) (v i) ∩ T d (x j) (v j)) ≤ 1 / 2 * MeasureTheory.volume (T d (x i) (v i))) ∧ ENNReal.ofReal (d ^ η * n * d ^ 2) ≤ ∑ i, MeasureTheory.volume (Y i) ∧ K d m n x v ∧ F d l n x v) → (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ n x v Y, A δ η m l n x v Y → ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ)) ≤ MeasureTheory.volume (⋃ i, Y i)) → (∀ ζ : ℝ, 0 < ζ → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ MeasureTheory.volume (⋃ i, Y i) ∨ ∃ (S : Finset (Fin n)) (Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℝ) (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (f : Fin n → Fin N), (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧ ENNReal.ofReal (δ ^ ζ) * ∑ i, MeasureTheory.volume (Y i) ≤ ∑ i ∈ S, MeasureTheory.volume (Z i) ∧ δ ^ (1 - ω / 100) ≤ ρ ∧ ρ ≤ δ ^ (ω / 100) ∧ (∀ k, ‖w k‖ = 1) ∧ (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧ K ρ (δ ^ (-ζ)) N y w ∧ F ρ (δ ^ (-ζ)) N y w ∧ ∀ k (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | i ∈ S ∧ f i = k ∧ T δ (x i) (v i) ⊆ T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p - t| ≤ r}}) * MeasureTheory.volume (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)) ≤ ENNReal.ofReal (δ ^ (-ζ) * Set.ncard {i | i ∈ S ∧ f i = k}) * MeasureTheory.volume (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p - t| ≤ r})) := by
  intro σ ω hσ hσu hω hωu T₀ hT K₀ hK F₀ hF A₀ hA
  subst T₀
  subst K₀
  subst F₀
  subst A₀
  intro hE
  exact glue_of_children hE (flatChild_of_frozen hflat hσ hσu hω hωu)
    (grainsChild_of_frozen hgrains hσ hσu hω hωu) (gainChild_of_frozen hgain hσ hσu hω hωu)

/-- The variant split: children rescale, grains and gain (premise `R`). -/
theorem main_of_frozen_children_v2 (hresc : SplitTypes.rescaleFrozen)
    (hgrains : SplitTypes.grainsFrozen) (hgain : SplitTypes.gain2Frozen) :
    ∀ σ ω : ℝ, 0 < σ → σ ≤ (1 / 2 : ℝ) → 0 < ω → ω ≤ 1 → ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ K, K = (fun (d m : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ W, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T d (x i) (v i) ⊆ W} * d ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) → ∀ F, F = (fun (d l : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | T d (x i) (v i) ⊆ Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}}) ≤ ENNReal.ofReal (l * n) * MeasureTheory.volume (Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r})) → ∀ A, A = (fun (d η m l : ℝ) (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) => 0 < n ∧ (∀ i, ‖v i‖ = 1 ∧ T d (x i) (v i) ⊆ Metric.ball 0 1 ∧ MeasurableSet (Y i) ∧ Y i ⊆ T d (x i) (v i)) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T d (x i) (v i) ∩ T d (x j) (v j)) ≤ 1 / 2 * MeasureTheory.volume (T d (x i) (v i))) ∧ ENNReal.ofReal (d ^ η * n * d ^ 2) ≤ ∑ i, MeasureTheory.volume (Y i) ∧ K d m n x v ∧ F d l n x v) → (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ n x v Y, A δ η m l n x v Y → ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ)) ≤ MeasureTheory.volume (⋃ i, Y i)) → (∀ ζ : ℝ, 0 < ζ → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y, A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ MeasureTheory.volume (⋃ i, Y i) ∨ ∃ (S : Finset (Fin n)) (Z : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) (ρ : ℝ) (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (f : Fin n → Fin N), (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧ ENNReal.ofReal (δ ^ ζ) * ∑ i, MeasureTheory.volume (Y i) ≤ ∑ i ∈ S, MeasureTheory.volume (Z i) ∧ δ ^ (1 - ω / 100) ≤ ρ ∧ ρ ≤ δ ^ (ω / 100) ∧ (∀ k, ‖w k‖ = 1) ∧ (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧ K ρ (δ ^ (-ζ)) N y w ∧ F ρ (δ ^ (-ζ)) N y w ∧ ∀ k (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | i ∈ S ∧ f i = k ∧ T δ (x i) (v i) ⊆ T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p - t| ≤ r}}) * MeasureTheory.volume (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)) ≤ ENNReal.ofReal (δ ^ (-ζ) * Set.ncard {i | i ∈ S ∧ f i = k}) * MeasureTheory.volume (T (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k) ∩ {p | |inner ℝ u p - t| ≤ r})) := by
  intro σ ω hσ hσu hω hωu T₀ hT K₀ hK F₀ hF A₀ hA
  subst T₀
  subst K₀
  subst F₀
  subst A₀
  intro hE
  exact glue_of_children_v2 hE (rescale_of_frozen hresc hσ hσu hω hωu)
    (grainsChild_of_frozen hgrains hσ hσu hω hωu) (gainChild2_of_frozen hgain hσ hσu hω hωu)

/-- The frozen local rescaling statement holds: it is `Interfaces.local_rescaling_of_estimate`. -/
theorem rescale_frozen : SplitTypes.rescaleFrozen := by
  intro σ ω hσ hσu hω hωu O hO q hq I hI T hT Q hQ X hX K hK F hF A hA B hB E hE R hR
  subst hO hq hI hT hQ hX hK hF hA hB hE hR
  exact local_rescaling_of_estimate hσ.le hσu hω.le

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
