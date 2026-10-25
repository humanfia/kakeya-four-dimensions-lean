-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Analytic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.FineEstimate
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.CoarseEstimate

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyEstimate BodyConvexCount BodySlabCount flatMap)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (closedTube)

def FineBoxBound (σ ω ε A η d : ℝ) : Prop :=
    ∀ (δ a b m l : ℝ) (hδ : 0 < δ), δ ≤ d →
    ∀ (hδa : δ ≤ a) (hab : a ≤ b), b ≤ 2 → a ≤ 1 / 100 → 1 ≤ m → 1 ≤ l →
    ∀ (e : AffineIsometryEquiv ℝ Space Space) (n : ℕ) (x v : Fin n → Space)
      (Y : Fin n → Set Space),
    0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → (∀ i, ‖v i‖ = 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ e '' WangZahlLot.Obl.wz_flat_factored_improvement.StandardPrism a b) →
    Distinct δ n x v → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
    (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
    WangZahlLot.Obl.wz_tower_balanced_refinement.ConvexCount δ m n x v →
    BodySlabCount (fun i => flatMap e a b (hδ.trans_le hδa) ((hδ.trans_le hδa).trans_le hab) ''
      closedTube δ (x i) (v i)) l →
    ENNReal.ofReal (A * δ ^ ε * (δ / a) ^ ω * m ^ (-1 + 3 / 2 * σ) * l ^ (-σ) *
      (n : ℝ) ^ (1 - σ) * δ ^ (2 - σ) * (a * b) ^ (σ / 2)) ≤ volume (⋃ i, Y i)

def CoarseBoxBound (σ ω ε A η d : ℝ) : Prop :=
    ∀ δ a b c D l : ℝ, 0 < δ → δ ≤ d → δ ≤ a → a ≤ b → b ≤ c → 1 ≤ c → c ≤ 8 →
    1 ≤ D → 1 ≤ l →
    ∀ (q : ℕ) (z : Fin q → Space) (e : Fin q → Space ≃ₗᵢ[ℝ] Space) (Z : Fin q → Set Space),
    0 < q → (q : ℝ) ≤ δ ^ (-100 : ℝ) →
    (∀ j, (Box a b c (z j) (e j) ∩ ball (0 : Space) 1).Nonempty) →
    (∀ j, MeasurableSet (Z j)) → (∀ j, Z j ⊆ Box (6 * a) (6 * b) (6 * c) (z j) (e j)) →
    (∀ j, ENNReal.ofReal (δ ^ η * (a * b)) ≤ volume (Z j)) →
    BodyConvexCount (fun j => Box a b c (z j) (e j)) (a * b * c) D →
    BodySlabCount (fun j => coarseBox a b c (z j) (e j)) l →
    ENNReal.ofReal (A * δ ^ ε * b ^ ω * D ^ (-1 + σ / 2) * l ^ (-σ) *
      (q : ℝ) ^ (1 - σ) * (a * b * c) ^ (1 - σ / 2)) ≤ volume (⋃ j, Z j)

lemma fineBoxBound_of_body_estimate {σ ω ε : ℝ} (h : BodyEstimate σ ω) (hε : 0 < ε) :
    ∃ A η d : ℝ, 0 < A ∧ 0 < η ∧ 0 < d ∧ d ≤ 1 / 100 ∧ FineBoxBound σ ω ε A η d :=
  fine_estimate_from_flattened_slabs h hε

lemma coarseBoxBound_of_body_estimate {σ ω ε : ℝ} (h : BodyEstimate σ ω) (hε : 0 < ε) :
    ∃ A η d : ℝ, 0 < A ∧ 0 < η ∧ 0 < d ∧ d ≤ 1 / 100 ∧ CoarseBoxBound σ ω ε A η d :=
  coarse_box_estimate h hε

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
