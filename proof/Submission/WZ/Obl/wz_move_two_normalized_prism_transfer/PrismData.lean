-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.PrismData.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Defs

noncomputable section
namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
open Set MeasureTheory

/-- Explicit data of frozen stage two, after substituting its exact coarse radius. -/
structure PrismData (ω ζ δ h ρ c : ℝ) (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) where
  a : ℝ
  L : ℕ
  N : ℕ
  z : Fin L → V
  e : Fin L → V ≃ₗᵢ[ℝ] V
  W : Fin n → Fin L → Set V
  y : Fin N → V
  w : Fin N → V
  γ : Fin L → Fin N
  lower : δ ≤ a
  middle : a ≤ ρ * c
  upper : ρ * c ≤ c
  length : c ≤ 1
  pieces : ∀ i j, MeasurableSet (W i j) ∧ W i j ⊆ Y i ∩ P a (ρ * c) c (z j) (e j) ∧
    ∀ j', j ≠ j' → Disjoint (W i j) (W i j')
  mass : O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i, ∑ j, μ (W i j)
  dense : ∀ j, O (δ ^ h) * μ (P a (ρ * c) c (z j) (e j)) ≤ μ (⋃ i, W i j)
  crossing : ∀ i j, (W i j).Nonempty →
    T δ (x i) (v i) ⊆ T ρ (y (γ j)) (w (γ j)) ∧
    (∀ p ∈ T δ (x i) (v i) ∩ frontier (P a (ρ * c) c (z j) (e j)),
      |ι (e j (p - z j)) 2| = c / 2) ∧
    ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ (x i) (v i) ∩ P a (ρ * c) c (z j) (e j), ι (e j (p - z j)) 2 = t
  broad : ∀ j (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
    q n {i | p ∈ W i j ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ W i j}
  distinct : X ρ N y w
  unit : ∀ k, ‖w k‖ = 1
  geometry : ∀ j, P a (ρ * c) c (z j) (e j) ⊆ T ρ (y (γ j)) (w (γ j)) ∧
    ι (e j (w (γ j))) 0 ^ 2 + ι (e j (w (γ j))) 1 ^ 2 ≤ (10 * ρ) ^ 2
  disjoint : ∀ j j', j ≠ j' → γ j = γ j' → Disjoint (⋃ i, W i j) (⋃ i, W i j')

theorem prismData_iff {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} :
    Nonempty (PrismData ω ζ δ h ρ c n x v Y) ↔ G ω ζ δ h ρ c n x v Y 2 := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.a, ρ, D.L, D.N, D.z, D.e, D.W, D.y, D.w, D.γ,
      D.lower, D.middle, D.upper, D.length, D.pieces, D.mass, D.dense, D.crossing,
      D.broad, D.distinct, D.unit, fun _ => ⟨rfl, D.geometry⟩, fun _ => D.disjoint⟩
  · rintro ⟨a, s, L, N, z, e, W, y, w, γ, hlo, hmid, hup, hlen, hW, hmass, hdense,
      hcross, hbr, hX, hw, hgeom, hdisj⟩
    obtain ⟨rfl, hgeom⟩ := hgeom (by norm_num)
    exact ⟨⟨a, L, N, z, e, W, y, w, γ, hlo, hmid, hup, hlen, hW, hmass, hdense,
      hcross, hbr, hX, hw, hgeom, hdisj (by norm_num)⟩⟩

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
