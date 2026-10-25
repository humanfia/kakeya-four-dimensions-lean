-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockPacketGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockPacketGeometry.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NormalizedPacketPieces
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketRounding

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped Classical
open WangZahlLot.Obl.wz_broad_grains_initialization (packetPiece)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit pd)
open WangZahlLot.Obl.wz_separated_cover_refinement (enumerate enumerate_mem enumerate_sum)

noncomputable section
namespace BlockAngularData

variable {ω ζ δ ε b ρ c β τ : ℝ} {p n : ℕ} {x v : Fin n → V}
  {Y : Fin n → Set V} {D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y}
  {R : Finset (Fin D.L)} {G : D.NormalizedBlock R}

abbrev normalizedPiece (A : BlockAngularData D R G β τ) (l : Fin A.labels.card) :
    Fin R.card → Set V :=
  packetPiece A.scale (fun i => unit (A.axis i)) A.shade A.packets A.center
    (enumerate A.labels l)

def active (A : BlockAngularData D R G β τ) (l : Fin A.labels.card) : Finset (Fin R.card) :=
  Finset.univ.filter fun i => (A.normalizedPiece l i).Nonempty

def packetMiddle (A : BlockAngularData D R G β τ) : ℝ := min (80 * A.scale) 4

def packetShort (A : BlockAngularData D R G β τ) : ℝ :=
  max (2 * ρ) (min (36 * G.short) A.packetMiddle)

theorem packet_dimensions (A : BlockAngularData D R G β τ) (hδ : 0 < δ)
    (hR : R.Nonempty) :
    0 < A.packetShort ∧ 2 * ρ ≤ A.packetShort ∧ A.packetShort ≤ A.packetMiddle ∧
      A.packetMiddle ≤ 4 ∧ 4 * A.scale ≤ A.packetMiddle ∧ A.packetMiddle ≤ 80 * A.scale ∧
      A.packetShort ≤ 25 * δ ^ (ζ / 8) * A.packetMiddle := by
  obtain ⟨ha, hρ, _, hc, _⟩ := D.dimensions hδ
  let i₀ : Fin R.card := ⟨0, Finset.card_pos.mpr hR⟩
  have hr := ball_in_prism_short_width (by positivity : 0 < ρ / 100)
    (G.affine (D.z (enumerate R i₀))) G.center G.frame ((G.round i₀).trans (G.enclosure i₀))
  have hθ : 0 < A.scale := (by positivity : 0 < 2 * ρ).trans_le A.lower
  obtain ⟨hra, hab, has, hθb, hbθ, hb⟩ := rounded_packet_widths G.short_pos.le hθ.le
    A.lower A.upper (by linarith : 2 * ρ ≤ 100 * G.short)
  have hwide : G.short ≤ δ ^ (ζ / 8) * A.scale := by
    have hh := A.wider
    rw [Real.rpow_neg hδ.le, inv_mul_eq_div] at hh
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hδ _)).mp hh |>.trans_eq (mul_comm _ _)
  refine ⟨(by positivity : 0 < 2 * ρ).trans_le hra, hra, hab, hb, hθb, hbθ, ?_⟩
  have hh := mul_le_mul_of_nonneg_left hwide (by norm_num : (0 : ℝ) ≤ 100)
  have hh' := mul_le_mul_of_nonneg_left hθb (Real.rpow_nonneg hδ.le (ζ / 8))
  dsimp only [packetShort, packetMiddle]
  nlinarith only [has, hh, hh']

theorem normalizedPiece_measurable (A : BlockAngularData D R G β τ)
    (l : Fin A.labels.card) (i : Fin R.card) : MeasurableSet (A.normalizedPiece l i) :=
  A.refinement.measurable_piece _ _

theorem normalizedPiece_subset (A : BlockAngularData D R G β τ)
    (l : Fin A.labels.card) (i : Fin R.card) :
    A.normalizedPiece l i ⊆ D.normalizedShade R G.affine i :=
  fun _ hp => (A.refinement.1 i).2 hp.1

theorem normalizedPiece_outside (A : BlockAngularData D R G β τ)
    (l : Fin A.labels.card) (i : Fin R.card) (hi : i ∉ A.active l) :
    A.normalizedPiece l i = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hi

/-- The rounded packet boxes have explicit diagonal normalizations and contain
both endpoints of every occupied old grain axis. -/
theorem packet_normalizations (A : BlockAngularData D R G β τ) (hδ : 0 < δ)
    (hR : R.Nonempty) (hshort : G.short ≤ 1 / 8) :
    ∃ (z : Fin A.labels.card → V) (e : Fin A.labels.card → V ≃ₗᵢ[ℝ] V)
      (f : Fin A.labels.card → V ≃ᵃ[ℝ] V),
      (∀ l i, i ∈ A.active l → D.normalizedBody R G.affine i ⊆
        P A.packetShort A.packetMiddle 4 (z l) (e l)) ∧
      (∀ l q j, (f l).linear q j =
        (![A.packetShort⁻¹, A.packetMiddle⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) j * e l q j) ∧
      (∀ l Q, μ (f l '' Q) = O (1 / (4 * A.packetShort * A.packetMiddle)) * μ Q) ∧
      ∀ l, f l '' P A.packetShort A.packetMiddle 4 (z l) (e l) ⊆ ball (0 : V) 1 := by
  classical
  obtain ⟨ha, _, hab, hb, _⟩ := A.packet_dimensions hδ hR
  have hex (l : Fin A.labels.card) : ∃ (z : V) (e : V ≃ₗᵢ[ℝ] V),
      ∀ i ∈ A.active l, D.normalizedBody R G.affine i ⊆
        P A.packetShort A.packetMiddle 4 z e := by
    by_cases hl : (A.active l).Nonempty
    · obtain ⟨i, hi⟩ := hl
      have hi' : (A.normalizedPiece l i).Nonempty := (Finset.mem_filter.mp hi).2
      have hne : ∃ j, (A.grainPiece j l).Nonempty := by
        refine ⟨enumerate R i, ?_⟩
        rw [normalizedPiece, ← A.image_grainPiece i l] at hi'
        exact hi'.of_image
      obtain ⟨z, e, hbox⟩ := A.grainPiece_prism hδ hshort l hne
      refine ⟨z, e, ?_⟩
      intro i hi
      apply (hbox (enumerate R i) ?_).trans (packet_prism_subset_rounded z e)
      have hh := (Finset.mem_filter.mp hi).2
      rw [normalizedPiece, ← A.image_grainPiece i l] at hh
      exact hh.of_image
    · exact ⟨0, LinearIsometryEquiv.refl ℝ V, fun i hi => (hl ⟨i, hi⟩).elim⟩
  choose z e hbox using hex
  choose f hvol hball hdist hcoord using
    fun l => fixed_prism_normalization_coordinates ha hab hb (z l) (e l)
  refine ⟨z, e, f, hbox, ?_, hvol, hball⟩
  intro l q j
  have hh := congrArg (fun u : V => u j) ((f l).map_vadd (0 : V) q)
  simp only [vadd_eq_add, add_zero, PiLp.add_apply, hcoord, map_sub, map_zero,
    PiLp.sub_apply, PiLp.zero_apply] at hh
  linarith only [hh]

/-- The labelled normalized pieces remain broad up to the middle-side scale. -/
theorem normalizedPiece_broad (A : BlockAngularData D R G β τ) (hδ : 0 < δ)
    (hR : R.Nonempty) (hβ : 0 ≤ β) (l : Fin A.labels.card) :
    ∀ (q u : V) (r : ℝ), 2 * ρ ≤ r →
      WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.q R.card
        {i | q ∈ A.normalizedPiece l i ∧ pd (unit (A.axis i)) u ≤ r} ≤
        (2 * (240 : ℝ) ^ β) * (r / (3 * A.packetMiddle)) ^ β *
          WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.q R.card {i | q ∈ A.normalizedPiece l i} := by
  intro q u r hr
  obtain ⟨_, hρ, _⟩ := D.dimensions hδ
  have hθ : 0 < A.scale := (by positivity : 0 < 2 * ρ).trans_le A.lower
  obtain ⟨ha, _, hab, _, _, hbθ, _⟩ := A.packet_dimensions hδ hR
  have hb : 0 < A.packetMiddle := ha.trans_le hab
  have hrpos : 0 < r := (by positivity : 0 < 2 * ρ).trans_le hr
  have hratio : 3 * A.packetMiddle / A.scale ≤ 240 := by
    apply (div_le_iff₀ hθ).mpr
    linarith
  have he : (r / A.scale) ^ β =
      (3 * A.packetMiddle / A.scale) ^ β * (r / (3 * A.packetMiddle)) ^ β := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  apply (packet_piece_broad A.refinement (enumerate A.labels l) q u r hr).trans
  rw [he]
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 3 * A.packetMiddle / A.scale) hratio hβ
  rw [← mul_assoc (2 : ℝ) ((3 * A.packetMiddle / A.scale) ^ β)]
  gcongr

end BlockAngularData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
