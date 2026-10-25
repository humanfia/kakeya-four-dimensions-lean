-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.AlternativeTypes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Basic

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

abbrev GlobalCover (d ζ ω : ℝ) {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  ∃ (S : Finset (Fin n)) (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ)
    (y w : Fin N → Space) (f : Fin n → Fin N),
    (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
    ENNReal.ofReal (d ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Z i) ∧
    d ^ (1 - ω / 100) ≤ ρ ∧ ρ ≤ d ^ (ω / 100) ∧
    (∀ k, ‖w k‖ = 1) ∧ (∀ i ∈ S, tube d (x i) (v i) ⊆ tube ρ (y (f i)) (w (f i))) ∧
    ConvexCount ρ (d ^ (-ζ)) (fun _ => True) (fun k => tube ρ (y k) (w k)) ∧
    (∀ u t r, ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal ({k | tube ρ (y k) (w k) ⊆ ball (0 : Space) 1 ∩ slab u t r}.ncard : ℝ) ≤
        ENNReal.ofReal (d ^ (-ζ) * N) * volume (ball (0 : Space) 1 ∩ slab u t r)) ∧
    ∀ k, SlabBound (doubled ρ (y k) (w k)) (d ^ (-ζ))
      (fun i => i ∈ S ∧ f i = k) (fun i => tube d (x i) (v i))

abbrev OneScaleAlternative (σ ω : ℝ) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible d η (d ^ (-η)) (d ^ (-η)) x v Y →
      ENNReal.ofReal (κ * d ^ (ω - α) * (n * d ^ 2) * (n * d) ^ (-σ)) ≤ volume (⋃ i, Y i) ∨
        GlobalCover d ζ ω x v Y

abbrev FibreCover (r s ζ C ω : ℝ) (y w : Space) {n : ℕ}
    (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  ∃ (S : Finset (Fin n)) (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ)
    (y' w' : Fin N → Space) (f : Fin n → Fin N),
    (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
    ENNReal.ofReal ((s / r) ^ ζ) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Z i) ∧
    r * (s / r) ^ (1 - ω / 100) ≤ C * ρ ∧ ρ ≤ C * (r * (s / r) ^ (ω / 100)) ∧
    (∀ k, ‖w' k‖ = 1 ∧ tube ρ (y' k) (w' k) ⊆ tube (2 * r) y w) ∧
    (∀ i ∈ S, tube s (x i) (v i) ⊆ doubled ρ (y' (f i)) (w' (f i))) ∧
    ConvexCount ρ ((s / r) ^ (-ζ)) (fun _ => True) (fun k => tube ρ (y' k) (w' k)) ∧
    SlabBound (doubled r y w) ((s / r) ^ (-ζ)) (fun _ => True) (fun k => tube ρ (y' k) (w' k)) ∧
    ∀ k, SlabBound (doubled ρ (y' k) (w' k)) ((s / r) ^ (-ζ))
      (fun i => i ∈ S ∧ f i = k) (fun i => tube s (x i) (v i))

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
