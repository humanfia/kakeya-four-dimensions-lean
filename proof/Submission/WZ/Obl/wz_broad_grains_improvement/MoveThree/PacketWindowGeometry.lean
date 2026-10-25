-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketWindowGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketWindowGeometry.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, PacketWindowGeometry.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketAffineGeometry
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConvexEnclosure
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PrescribedWindows

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement packetPiece packetLabelUniverse)

/-- Relative volume comparisons survive a common affine change of variables. -/
theorem affine_volume_comparison (f : V ≃ᵃ[ℝ] V) {U W : Set V} {D : ENNReal}
    (h : μ U ≤ D * μ W) : μ (f '' U) ≤ D * μ (f '' W) := by
  have hvol (Q : Set V) : μ (f '' Q) =
      O |LinearMap.det (f.linear : V →ₗ[ℝ] V)| * μ Q :=
    WangZahlLot.Obl.wz_regular_transverse_affine_cells.affineEquiv_volume f Q
  simpa only [hvol, mul_left_comm, mul_assoc] using mul_le_mul' (le_refl
    (O |LinearMap.det (f.linear : V →ₗ[ℝ] V)|)) h

/-- Cutting only the long dimension and enlarging the two transverse sides
costs the square of the transverse enlargement in volume. -/
theorem prescribed_length_single_window_volume {A B c ℓ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c) (hcℓ : c ≤ ℓ)
    (z z₀ : V) (e : V ≃ₗᵢ[ℝ] V) :
    μ (P (128*A) (128*B) c z e) ≤ O 16384 * μ (P A B ℓ z₀ e) := by
  change volume (WangZahlLot.Obl.wz_move_three_thick_grains_gain.P (128*A) (128*B) c z e) ≤
    ENNReal.ofReal 16384 * volume (WangZahlLot.Obl.wz_move_three_thick_grains_gain.P A B ℓ z₀ e)
  rw [WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P
      (by positivity : 0 ≤ 128*A) (by positivity : 0 ≤ 128*B) hc z e,
    WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P hA hB (hc.trans hcℓ) z₀ e,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16384)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [mul_le_mul_of_nonneg_left hcℓ (show 0 ≤ 16384*A*B by positivity)]

/-- The numerical loss from inverse enclosure, transverse enlargement, and
normalized slab-prism volume. The number is independent of every scale. -/
def packetWindowConstant : ℝ := 16384 * 110592 * 11520

/-- Actual normalized packet labels have physical enclosures of length
`128 c`. Their exact-length outer windows have controlled normalized volume,
and their short cores cover every original packet row. -/
theorem affine_packet_window_geometry {β δ d θ a₀ a b c : ℝ} {n : ℕ}
    {x ν zOld : Fin n → V} {eOld : Fin n → V ≃ₗᵢ[ℝ] V}
    {Y Z : Fin n → Set V} {packets : V → Finset (Finset (Fin n))}
    {center : V → Finset (Fin n) → Fin n}
    (hpack : PacketRefinement β δ θ ν Y Z packets center)
    (hδd : δ ≤ d) (hdθ : d ≤ θ) (hθ : 0 < θ)
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (ha₀ : 0 < a₀) (ha₀8 : a₀ ≤ 1/8) (hν : ∀ i, ‖ν i‖ = 1)
    (hY : ∀ i, Y i ⊆ P a b c (zOld i) (eOld i))
    (f : V ≃ᵃ[ℝ] V)
    (hInv : ∀ p q, dist (f.symm p) (f.symm q) ≤ (4*c)*dist p q)
    (hT : ∀ i, (Y i).Nonempty → f '' P a b c (zOld i) (eOld i) ⊆ T d (x i) (ν i))
    (hball : ∀ i, (Y i).Nonempty → f '' P a b c (zOld i) (eOld i) ⊆ ball (0 : V) 1)
    (normal : V) (offset : ℝ) (hnormal : ‖normal‖ = 1)
    (hslab : ∀ i, (Y i).Nonempty → f '' P a b c (zOld i) (eOld i) ⊆
      {p | |inner ℝ normal p-offset| ≤ a₀/2})
    (hflat : ∀ i, (Y i).Nonempty → |inner ℝ normal (ν i)| ≤ 4*a₀) :
    ∃ (A B : packetLabelUniverse θ x ν → ℝ)
      (z : packetLabelUniverse θ x ν → V)
      (e : packetLabelUniverse θ x ν → V ≃ₗᵢ[ℝ] V),
      (∀ k, 0 ≤ A k ∧ A k ≤ B k ∧ B k ≤ 128*c) ∧
      (∀ (k : packetLabelUniverse θ x ν), (⋃ i, affinePacketPiece f θ ν Z packets center k i).Nonempty → a ≤ A k) ∧
      (∀ (k : packetLabelUniverse θ x ν) i, (affinePacketPiece f θ ν Z packets center k i).Nonempty →
        P a b c (zOld i) (eOld i) ⊆ P (A k) (B k) (128*c) (z k) (e k)) ∧
      (∀ (k : packetLabelUniverse θ x ν) i, affinePacketPiece f θ ν Z packets center k i ⊆
        ⋃ j : Fin 2049, P (A k) (B k) (c/8)
          (axialWindowCenter c (128*c) (z k) (e k) j) (e k)) ∧
      ∀ k (j : Fin 2049), μ (f '' P (128*A k) (128*B k) c
        (axialWindowCenter c (128*c) (z k) (e k) j) (e k)) ≤
          O (packetWindowConstant * a₀ * θ) := by
  classical
  have hc : 0 < c := ha.trans_le (hab.trans hbc)
  let Λ := packetLabelUniverse θ x ν
  let A₀ := min (36*a₀) (min (80*θ) 4)
  let B₀ := min (80*θ) 4
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  have hAB₀ : A₀ ≤ B₀ := min_le_right _ _
  have hB₀ : B₀ ≤ 4 := min_le_right _ _
  have hgeo (k : Λ) : ∃ (A B : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V),
      (0 ≤ A ∧ A ≤ B ∧ B ≤ 128*c) ∧
      ((⋃ i, affinePacketPiece f θ ν Z packets center k i).Nonempty → a ≤ A) ∧
      (∀ i, (affinePacketPiece f θ ν Z packets center k i).Nonempty →
        P a b c (zOld i) (eOld i) ⊆ P A B (128*c) z e) ∧
      μ (f '' P A B (128*c) z e) ≤ O (110592*11520*a₀*θ) := by
    by_cases hk : (⋃ i, affinePacketPiece f θ ν Z packets center k i).Nonempty
    · obtain ⟨i₀, hi₀⟩ := nonempty_iUnion.mp hk
      obtain ⟨z₀, e₀, hwhole, hvol₀⟩ := affine_packet_piece_prism
        (packet_refinement_mono_base hpack hδd) ha₀ ha₀8 hθ hdθ hν hY f
        hT hball normal hnormal hslab hflat k ⟨i₀, hi₀⟩
      obtain ⟨A, B, z, e, haA, hAB, hB, hbox, hvol⟩ :=
        inverse_prism_enclosure ha hab hbc hA₀.le hAB₀ hB₀
          (by norm_num : (0 : ℝ) < 4) (by norm_num : (0 : ℝ) < 4)
          (zOld i₀) z₀ (eOld i₀) e₀ f hInv (hwhole i₀ hi₀)
      norm_num only [show (8:ℝ)*4*4 = 128 by norm_num,
        show (6912:ℝ)*4*4 = 110592 by norm_num] at hB hbox hvol
      refine ⟨A, B, z, e, ⟨ha.le.trans haA, hAB, hB⟩, fun _ => haA, ?_, ?_⟩
      · intro i hi p hp
        exact hbox ⟨f p, hwhole i hi (mem_image_of_mem f hp), f.symm_apply_apply p⟩
      · have hh := affine_volume_comparison f hvol
        simp only [image_image, f.apply_symm_apply, image_id'] at hh
        calc
          _ ≤ O 110592 * μ (P A₀ B₀ 4 z₀ e₀) := hh
          _ ≤ O 110592 * O (11520*a₀*θ) := mul_le_mul' le_rfl hvol₀
          _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 110592)]; congr 1; ring
    · refine ⟨0, 0, 0, LinearIsometryEquiv.refl ℝ V, ⟨le_rfl, le_rfl, by positivity⟩,
        fun hh => (hk hh).elim, fun i hi => (hk (nonempty_iUnion.mpr ⟨i, hi⟩)).elim, ?_⟩
      have hvol : μ (P 0 0 (128*c) (0:V) (LinearIsometryEquiv.refl ℝ V)) = 0 := by
        change volume (WangZahlLot.Obl.wz_move_three_thick_grains_gain.P 0 0 (128*c) (0:V)
          (LinearIsometryEquiv.refl ℝ V)) = 0
        rw [WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P
          (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) ≤ 0)
          (by positivity : 0 ≤ 128*c) (0:V) (LinearIsometryEquiv.refl ℝ V)]
        norm_num [O]
      change volume (f '' P 0 0 (128*c) (0:V) (LinearIsometryEquiv.refl ℝ V)) ≤ _
      rw [WangZahlLot.Obl.wz_regular_transverse_affine_cells.affineEquiv_volume f]
      change O _ * μ (P 0 0 (128*c) (0:V) (LinearIsometryEquiv.refl ℝ V)) ≤ _
      rw [hvol, mul_zero]
      exact bot_le
  choose A B z e hdim haA hbody hvol using hgeo
  refine ⟨A, B, z, e, hdim, haA, hbody, ?_, ?_⟩
  · intro k i p hp
    have hcont := hbody k i ⟨p, hp⟩
      (hY i ((hpack.1 i).2 (affinePacketPiece_subset f θ ν Z packets center k i hp)))
    exact prescribed_length_core_cover_fixed (N := 2048) hc
      (by rw [← mul_assoc, mul_div_cancel_right₀ _ hc.ne']; norm_num) (z k) (e k) hcont
  · intro k j
    have hh := affine_volume_comparison f (prescribed_length_single_window_volume
      (hdim k).1 ((hdim k).1.trans (hdim k).2.1) hc.le (by linarith : c ≤ 128*c)
      (axialWindowCenter c (128*c) (z k) (e k) j) (z k) (e k))
    calc
      _ ≤ O 16384 * μ (f '' P (A k) (B k) (128*c) (z k) (e k)) := hh
      _ ≤ O 16384 * O (110592*11520*a₀*θ) := mul_le_mul' le_rfl (hvol k)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16384)]
        congr 1
        dsimp [packetWindowConstant]
        ring

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
