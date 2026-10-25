-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Interfaces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.Types

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric

abbrev Space := LeanEval.Analysis.WangZahlKakeya.Space
abbrev Tube := WangZahlLot.Obl.wz_tower_balanced_refinement.Tube
abbrev Admissible := WangZahlLot.Obl.wz_tower_balanced_refinement.Admissible
abbrev SlabCount := WangZahlLot.Obl.wz_tower_balanced_refinement.SlabCount
abbrev Estimate := WangZahlLot.Obl.wz_flat_factored_improvement.TubeEstimate

abbrev Distinct (δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
    1 / 2 * volume (Tube δ (x i) (v i))

def Box (a b c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : Set Space :=
  {p | |e (p - z) 0| ≤ a / 2 ∧ |e (p - z) 1| ≤ b / 2 ∧ |e (p - z) 2| ≤ c / 2}

def BelowSlab (δ ρ l : ℝ) (n N : ℕ) (x v : Fin n → Space)
    (S : Finset (Fin n)) (y w : Fin N → Space) (f : Fin n → Fin N) : Prop :=
  ∀ k, let D := Tube (2 * ρ) (y k - (1 / 2 : ℝ) • w k) (2 • w k)
    ∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i | i ∈ S ∧ f i = k ∧
        Tube δ (x i) (v i) ⊆ D ∩ {p | |inner ℝ u p - t| ≤ r}} : ℝ) * volume D ≤
      ENNReal.ofReal (l * (Set.ncard {i | i ∈ S ∧ f i = k} : ℝ)) *
        volume (D ∩ {p | |inner ℝ u p - t| ≤ r})

def Cover (δ h : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (S : Finset (Fin n)) (Z : Fin n → Set Space) (ρ : ℝ) (N : ℕ)
    (y w : Fin N → Space) (f : Fin n → Fin N) : Prop :=
  (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅)) ∧
  ENNReal.ofReal (δ ^ h) * ∑ i, volume (Y i) ≤ ∑ i ∈ S, volume (Z i) ∧
  (∀ k, ‖w k‖ = 1) ∧
  (∀ i ∈ S, Tube δ (x i) (v i) ⊆ Tube ρ (y (f i)) (w (f i))) ∧
  SlabCount ρ (δ ^ (-h)) N y w ∧ BelowSlab δ ρ (δ ^ (-h)) n N x v S y w f ∧
  (∀ k k', (Set.ncard {i | i ∈ S ∧ f i = k} : ℝ) ≤
    δ ^ (-h) * (Set.ncard {i | i ∈ S ∧ f i = k'} : ℝ)) ∧
  Distinct ρ N y w ∧
  ∀ i ∈ S, (Set.ncard {k | Tube δ (x i) (v i) ⊆ Tube ρ (y k) (w k)} : ℝ) ≤ δ ^ (-h)

noncomputable def bound (σ ω ε κ δ a b n : ℝ) : ℝ :=
  κ * δ ^ (ω + ε) * (b / a) ^ ω * (n * δ ^ 2) * (n * δ) ^ (-σ)

def BoxCover (δ η ρ a b c : ℝ) (N L : ℕ) (y w : Fin N → Space)
    (z : Fin L → Space) (e : Fin L → Space ≃ₗᵢ[ℝ] Space) (g : Fin N → Fin L) : Prop :=
  let U := fun j => Box a b c (z j) (e j)
  (∀ k, Tube ρ (y k) (w k) ⊆ U (g k)) ∧
  (∀ j j', (Set.ncard {k | g k = j} : ℝ) ≤ δ ^ (-η) * (Set.ncard {k | g k = j'} : ℝ)) ∧
  (∀ k, (Set.ncard {j | Tube ρ (y k) (w k) ⊆ U j} : ℝ) ≤ δ ^ (-η)) ∧
  (∀ W, Convex ℝ W → ENNReal.ofReal ((Set.ncard {j | U j ⊆ W} : ℝ) * (a * b * c)) ≤
    ENNReal.ofReal (δ ^ (-η)) * volume W) ∧
  ∀ j W, Convex ℝ W →
    ENNReal.ofReal (Set.ncard {k | g k = j ∧ Tube ρ (y k) (w k) ⊆ U j ∩ W} : ℝ) *
      volume (U j) ≤ ENNReal.ofReal (δ ^ (-η) * (Set.ncard {k | g k = j} : ℝ)) *
        volume (U j ∩ W)

def Conclusion (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
    ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ N y w f, Cover δ η n x v Y .univ Y ρ N y w f →
    ∀ a b c : ℝ, ρ ≤ a → a ≤ b → b ≤ c → 1 ≤ c → c ≤ 8 →
    ∀ (L : ℕ) (z : Fin L → Space) (e : Fin L → Space ≃ₗᵢ[ℝ] Space) (g : Fin N → Fin L),
    BoxCover δ η ρ a b c N L y w z e g →
    ENNReal.ofReal (bound σ ω ε κ δ a b n) ≤ volume (⋃ i, Y i)

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
