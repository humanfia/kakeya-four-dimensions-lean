-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClippedWindowGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClippedWindowGeometry.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, ClippedWindowGeometry.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedPacketGeometry
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedWidthEnclosure
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketWindowGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_broad_grains_initialization (PacketRefinement packetLabelUniverse)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)

/-- Fixed normalized volume cost of the width-controlled physical windows. -/
def clippedWindowConstant : ℝ := 16384 * 3145728 * 11520

/-- A sufficiently small second angle gives physical windows whose middle
width is at most the old length. The clipped chart controls both the
normalized volume and the physical middle side. -/
theorem clipped_packet_window_geometry {n : ℕ} {a ρ c Ac Bc Cc δ β θ : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c)
    (hac : a ≤ ρ*c) (hAc : 0 < Ac) (hδρ : δ ≤ 2*ρ) (hρθ : 2*ρ ≤ θ)
    (hα : ρ*Ac/(4*min Ac (ρ*c)) ≤ 1/8) (hθmax : θ ≤ 1/2^35)
    (zOld : Fin n → V) (eOld : Fin n → V ≃ₗᵢ[ℝ] V)
    (z₀ zc : V) (g : V ≃ₗᵢ[ℝ] V) :
    let f := carrierAffine (lt_min hAc (mul_pos hρ hc)) hc hρ z₀ zc g
    let ν := fun j => unit (f.linear (boxAxis (eOld j) 2))
    let x := fun j => f (zOld j)-(1/2:ℝ) • ν j
    let α := ρ*Ac/(4*min Ac (ρ*c))
    ∀ (Y Z : Fin n → Set V) (packets : V → Finset (Finset (Fin n)))
      (center : V → Finset (Fin n) → Fin n),
      PacketRefinement β δ θ ν Y Z packets center →
      (∀ j, Y j ⊆ P a (ρ*c) c (zOld j) (eOld j)) →
      (∀ j, (Y j).Nonempty →
        P a (ρ*c) c (zOld j) (eOld j) ⊆ P Ac Bc Cc zc g ∩ ball z₀ (2*c)) →
      ∃ (A B : packetLabelUniverse θ x ν → ℝ)
        (z : packetLabelUniverse θ x ν → V)
        (e : packetLabelUniverse θ x ν → V ≃ₗᵢ[ℝ] V),
        (∀ k, 0 ≤ A k ∧ A k ≤ B k ∧ 128*B k ≤ c ∧ B k ≤ 83886080*θ*c) ∧
        (∀ (k : packetLabelUniverse θ x ν),
          (⋃ i, affinePacketPiece f θ ν Z packets center k i).Nonempty → a ≤ A k) ∧
        (∀ (k : packetLabelUniverse θ x ν) i,
          (affinePacketPiece f θ ν Z packets center k i).Nonempty →
          P a (ρ*c) c (zOld i) (eOld i) ⊆ P (A k) (B k) (384*c) (z k) (e k)) ∧
        (∀ (k : packetLabelUniverse θ x ν) i,
          affinePacketPiece f θ ν Z packets center k i ⊆ ⋃ j : Fin 6145,
            P (A k) (B k) (c/8) (axialWindowCenter c (384*c) (z k) (e k) j) (e k)) ∧
        ∀ k (j : Fin 6145), μ (f '' P (128*A k) (128*B k) c
          (axialWindowCenter c (384*c) (z k) (e k) j) (e k)) ≤
            O (clippedWindowConstant*α*θ) := by
  classical
  dsimp only
  let f := carrierAffine (lt_min hAc (mul_pos hρ hc)) hc hρ z₀ zc g
  let ν := fun j => unit (f.linear (boxAxis (eOld j) 2))
  let x := fun j => f (zOld j)-(1/2:ℝ) • ν j
  let α := ρ*Ac/(4*min Ac (ρ*c))
  let Λ := packetLabelUniverse θ x ν
  let A₀ := min (36*α) (min (80*θ) 4)
  let B₀ := min (80*θ) 4
  have hθ : 0 < θ := (by positivity : 0 < 2*ρ).trans_le hρθ
  have hαpos : 0 < α := by dsimp [α]; positivity
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  have hAB₀ : A₀ ≤ B₀ := min_le_right _ _
  have hB₀ : B₀ ≤ 4 := min_le_right _ _
  have hBθ : B₀ ≤ 80*θ := min_le_left _ _
  intro Y Z packets center hpack hY hbody
  have hgeo (k : Λ) : ∃ (A B : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V),
      (0 ≤ A ∧ A ≤ B ∧ 128*B ≤ c ∧ B ≤ 83886080*θ*c) ∧
      ((⋃ i, affinePacketPiece f θ ν Z packets center k i).Nonempty → a ≤ A) ∧
      (∀ i, (affinePacketPiece f θ ν Z packets center k i).Nonempty →
        P a (ρ*c) c (zOld i) (eOld i) ⊆ P A B (384*c) z e) ∧
      μ (f '' P A B (384*c) z e) ≤ O (3145728*11520*α*θ) := by
    by_cases hk : (⋃ i, affinePacketPiece f θ ν Z packets center k i).Nonempty
    · obtain ⟨i₀, hi₀⟩ := nonempty_iUnion.mp hk
      obtain ⟨p, E, hwhole, hvol₀⟩ := clipped_packet_prism ha.le hρ hρ1 hc hac hAc hδρ hρθ hα
        zOld eOld z₀ zc g Y Z packets center hpack hY hbody k ⟨i₀, hi₀⟩
      obtain ⟨A, B, e, haA, hAB, _, hBW, hbox, hvol⟩ :=
        carrierAffine_middle_enclosure ha hρ hρ1 hc hac (lt_min hAc (mul_pos hρ hc))
          (min_le_right Ac (ρ*c)) hA₀ hAB₀ hB₀
          (zOld i₀) z₀ zc p (eOld i₀) g E (hwhole i₀ hi₀)
      norm_num only [show (96:ℝ)*4=384 by norm_num,
        show (786432:ℝ)*4=3145728 by norm_num] at hbox hvol
      have hBW' : B ≤ 83886080*θ*c := by
        have hh := mul_le_mul_of_nonneg_right hBθ (show 0 ≤ 1048576*c by positivity)
        nlinarith
      have hsmall : 128*B ≤ c := by
        have hh := mul_le_mul_of_nonneg_right hθmax hc.le
        norm_num at hh
        nlinarith
      refine ⟨A, B, f.symm p, e, ⟨ha.le.trans haA, hAB, hsmall, hBW'⟩,
        fun _ => haA, ?_, ?_⟩
      · intro i hi q hq
        exact hbox ⟨f q, hwhole i hi (mem_image_of_mem f hq), f.symm_apply_apply q⟩
      · change μ (P A B (384*c) (f.symm p) e) ≤
          O 3145728*μ (f.symm '' P A₀ B₀ 4 p E) at hvol
        have hh := affine_volume_comparison f hvol
        simp only [image_image, f.apply_symm_apply, image_id'] at hh
        calc
          _ ≤ O 3145728*μ (P A₀ B₀ 4 p E) := hh
          _ ≤ O 3145728*O (11520*α*θ) := mul_le_mul' le_rfl hvol₀
          _ = _ := by
            rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3145728)]
            congr 1
            ring
    · refine ⟨0, 0, 0, LinearIsometryEquiv.refl ℝ V,
        ⟨le_rfl, le_rfl, by simpa using hc.le, by positivity⟩,
        fun hh => (hk hh).elim, fun i hi => (hk (nonempty_iUnion.mpr ⟨i, hi⟩)).elim, ?_⟩
      have hvol : μ (P 0 0 (384*c) (0:V) (LinearIsometryEquiv.refl ℝ V)) = 0 := by
        change volume (WangZahlLot.Obl.wz_move_three_thick_grains_gain.P 0 0 (384*c) (0:V)
          (LinearIsometryEquiv.refl ℝ V)) = 0
        rw [WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P
          (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) ≤ 0) (by positivity)]
        norm_num [O]
      change volume (f '' P 0 0 (384*c) (0:V) (LinearIsometryEquiv.refl ℝ V)) ≤ _
      rw [WangZahlLot.Obl.wz_regular_transverse_affine_cells.affineEquiv_volume f]
      change O _*μ (P 0 0 (384*c) (0:V) (LinearIsometryEquiv.refl ℝ V)) ≤ _
      rw [hvol, mul_zero]
      exact bot_le
  choose A B z e hdim haA hwhole hvol using hgeo
  refine ⟨A, B, z, e, hdim, haA, hwhole, ?_, ?_⟩
  · intro k i p hp
    have hcont := hwhole k i ⟨p, hp⟩
      (hY i ((hpack.1 i).2 (affinePacketPiece_subset f θ ν Z packets center k i hp)))
    exact prescribed_length_core_cover_fixed (N := 6144) hc
      (by rw [← mul_assoc, mul_div_cancel_right₀ _ hc.ne']; norm_num) (z k) (e k) hcont
  · intro k j
    have hh := affine_volume_comparison f (prescribed_length_single_window_volume
      (hdim k).1 ((hdim k).1.trans (hdim k).2.1) hc.le (by linarith : c ≤ 384*c)
      (axialWindowCenter c (384*c) (z k) (e k) j) (z k) (e k))
    calc
      _ ≤ O 16384*μ (f '' P (A k) (B k) (384*c) (z k) (e k)) := hh
      _ ≤ O 16384*O (3145728*11520*α*θ) := mul_le_mul' le_rfl (hvol k)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16384)]
        congr 1
        dsimp [clippedWindowConstant]
        ring

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
