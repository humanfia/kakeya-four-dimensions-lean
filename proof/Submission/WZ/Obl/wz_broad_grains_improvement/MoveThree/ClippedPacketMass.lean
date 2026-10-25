-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClippedPacketMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClippedPacketMass.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedCarrierPackets

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory

noncomputable section
namespace ClippedCarrierAngularData

variable {σ ω ζ δ ε b ρ c β τ den k Cnet e u t loss density β₂ q₀ jump τ₂ : ℝ}
  {p n d : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
  {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}
  {A : BlockAngularData D R G β τ} {hk : 0 < k}
  {F : BlockFirstFilling A (δ ^ t / firstFillingMassConstant) den k hk}
  {N : BlockNetData (σ := σ) F Cnet e (δ ^ (-u)) (δ ^ (-ζ / 2)) d}
  {l : Fin A.labels.card} {j : Fin (N.N l)}
  {B : PhysicalCarrierBox N loss density l j} {hδ : 0 < δ}

theorem shade_outside (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂)
    (i : Fin R.card) (hi : i ∉ N.fibre l j) : Q.shade i = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hh := Q.input_subset i (((Q.refinement.1 i).2 hz).1)
  rw [N.physicalPiece_outside l j i hi] at hh
  exact hh

/-- The actual first-fibre row mass, second angular retention, and clipped
Jacobian give the round-row budget required by the second filling. -/
theorem normalized_mass (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂)
    (hl : l ∈ F.good) :
    O ((24 / firstFillingMassConstant) * δ ^ (t + τ₂ + loss) *
      (N.size l : ℝ) * (2 * ρ) ^ 2) ≤ ∑ i, μ (B.map hδ '' Q.shade i) := by
  obtain ⟨ha, hρ, _, hc, _⟩ := D.dimensions hδ
  have hH : 0 < firstFillingMassConstant := by norm_num [firstFillingMassConstant]
  have hlam : 0 ≤ δ ^ t / firstFillingMassConstant := by positivity
  have hJ : 0 < ρ / (64 * min B.short (ρ * c) * c ^ 2) := by
    have hB := B.short_pos hδ
    positivity
  have hscalar : (24 / firstFillingMassConstant) * δ ^ (t + τ₂ + loss) *
      (N.size l : ℝ) * (2 * ρ) ^ 2 ≤
      (ρ / (64 * min B.short (ρ * c) * c ^ 2)) *
        (δ ^ τ₂ / 2 * (12288 * (δ ^ t / firstFillingMassConstant) *
          (D.a * (ρ * c) * c) * (N.size l : ℝ))) := by
    have hh := renormS_row_mass hδ D.grains.1 D.grains.2.1 B.lower B.thin hρ hc
      (lam := (6144 / firstFillingMassConstant) * δ ^ (t + τ₂) * (N.size l : ℝ))
      (by positivity)
    convert hh using 1 <;> simp only [Real.rpow_add hδ] <;> ring
  calc
    _ ≤ O ((ρ / (64 * min B.short (ρ * c) * c ^ 2)) *
        (δ ^ τ₂ / 2 * (12288 * (δ ^ t / firstFillingMassConstant) *
          (D.a * (ρ * c) * c) * (N.size l : ℝ)))) := ENNReal.ofReal_le_ofReal hscalar
    _ = O (ρ / (64 * min B.short (ρ * c) * c ^ 2)) *
        (O (δ ^ τ₂ / 2) * O (12288 * (δ ^ t / firstFillingMassConstant) *
          (D.a * (ρ * c) * c) * (N.size l : ℝ))) := by
      dsimp only [O]
      rw [ENNReal.ofReal_mul hJ.le, ENNReal.ofReal_mul (by positivity : 0 ≤ δ ^ τ₂ / 2)]
    _ ≤ O (ρ / (64 * min B.short (ρ * c) * c ^ 2)) * ∑ i, μ (Q.shade i) :=
      mul_le_mul' le_rfl ((mul_le_mul' le_rfl
        (N.physical_piece_mass hδ hlam hl j)).trans Q.mass)
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => (B.map_volume hδ (Q.shade i)).symm)

theorem normalized_mass_power (Q : ClippedCarrierAngularData B hδ β₂ q₀ jump τ₂)
    (hl : l ∈ F.good) {h : ℝ}
    (hbudget : δ ^ h ≤ (24 / firstFillingMassConstant) * δ ^ (t + τ₂ + loss)) :
    O (δ ^ h * (N.fibre l j).card * (2 * ρ) ^ 2) ≤
      ∑ i, μ (B.map hδ '' Q.shade i) := by
  rw [(N.net l hl).2.2.2.2.1 j]
  apply le_trans ?_ (Q.normalized_mass hl)
  apply ENNReal.ofReal_le_ofReal
  gcongr

end ClippedCarrierAngularData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
