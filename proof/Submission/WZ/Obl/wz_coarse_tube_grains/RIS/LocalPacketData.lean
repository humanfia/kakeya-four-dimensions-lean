-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LocalPacketData.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalPlanarPacket
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.KatzSeparation

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

/-- The geometric and quantitative output of one local prism construction. -/
structure LocalPrismPacket (δ r ρ c ε : ℝ) {n : ℕ}
    (x v : Fin n → V) (Y : Fin n → Set V) (p₀ y w : V) where
  level : ℕ
  frame : V ≃ₗᵢ[ℝ] V
  centers : Finset V
  shading : Fin n → Set V
  pieces : V → Set V
  aligned : (frame w 0) ^ 2 + (frame w 1) ^ 2 ≤ (10 * ρ) ^ 2
  refines : ∀ i, MeasurableSet (shading i) ∧ shading i ⊆ Y i
  disjoint : (↑centers : Set V).PairwiseDisjoint (fun z => P (16 * δ) (128 * ρ * c) c z frame)
  piece_data : ∀ z ∈ centers, MeasurableSet (pieces z) ∧
    pieces z ⊆ P (16 * δ) (128 * ρ * c) c z frame ∧ (pieces z).Nonempty ∧
    P (16 * δ) (128 * ρ * c) c z frame ⊆ T (2 * ρ) y w ∧
    P (16 * δ) (128 * ρ * c) c z frame ⊆ ball p₀ (3 * r)
  union_eq : (⋃ z ∈ centers, pieces z) = ⋃ i, shading i
  retains : o (δ ^ ε) * (∑ i, μ (Y i)) ≤ ∑ i, μ (shading i)
  density : o (δ ^ ε * centers.card * ((16 * δ) * (128 * ρ * c) * c)) ≤ ∑ z ∈ centers, μ (pieces z)
  crossing : ∀ i z, z ∈ centers → (shading i ∩ pieces z).Nonempty →
    shading i ∩ P (16 * δ) (128 * ρ * c) c z frame ⊆ pieces z ∧
    (∀ p ∈ T δ (x i) (v i) ∩ frontier (P (16 * δ) (128 * ρ * c) c z frame),
      |frame (p - z) 2| = c / 2) ∧
    ∀ s ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ (x i) (v i) ∩ P (16 * δ) (128 * ρ * c) c z frame,
        frame (p - z) 2 = s
  uniform : ∀ p ∈ ⋃ i, shading i,
    2 ^ level ≤ (Finset.univ.filter fun i => p ∈ shading i).card ∧
    (Finset.univ.filter fun i => p ∈ shading i).card < 2 ^ (level + 1)

/-- Empty local cells have a packet with no prisms and an aligned frame. -/
theorem empty_local_prism_packet {δ r ρ c ε : ℝ} {n : ℕ}
    (x v : Fin n → V) (Y : Fin n → Set V) (p₀ y w : V) (hw : ‖w‖ = 1)
    (hzero : ∀ i, Y i = ∅) : Nonempty (LocalPrismPacket δ r ρ c ε x v Y p₀ y w) := by
  obtain ⟨e, he⟩ := exists_rotation_last hw
  refine ⟨{
    level := 0
    frame := e
    centers := ∅
    shading := fun _ => ∅
    pieces := fun _ => ∅
    aligned := ?_
    refines := fun _ => ⟨MeasurableSet.empty, empty_subset _⟩
    disjoint := by simp
    piece_data := by simp
    union_eq := by simp
    retains := by simp only [hzero, measure_empty, Finset.sum_const_zero, mul_zero, le_refl]
    density := by simp [o, μ]
    crossing := by simp
    uniform := by simp
  }⟩
  rw [he]
  simpa using sq_nonneg (10 * ρ)

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
