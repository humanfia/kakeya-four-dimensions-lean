-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClippedWindowFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClippedWindowFilling.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, ClippedWindowFilling.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ClippedWindowGeometry
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AffineWindowFilling
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.WindowColor

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_broad_grains_initialization (PacketRefinement packetLabelUniverse)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

/-- The actual clipped chart supplies dense physical windows with separated
rows, controlled middle width, and the original long length. All fixed
enclosure, window, and colour losses are uniform in the scales. -/
theorem clipped_packet_window_fillings {β t s u h ε vLoss : ℝ}
    (hβ : 0 < β) (hs : 0 < s) (hst : s ≤ t) (hhu : h < u)
    (hgap : 3*u+s+vLoss < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1/100 ∧ ∀ δ ρ θ a c Ac Bc Cc : ℝ,
      0 < δ → δ ≤ d₀ → δ ≤ 2*ρ → 2*ρ ≤ 1/100 →
      δ^(-t)*(2*ρ) ≤ θ → θ ≤ 1/2^35 →
      ∀ (ha : 0 < a) (hρ : 0 < ρ) (hc : 0 < c) (hAc : 0 < Ac),
      a ≤ ρ*c → ρ*Ac/(4*min Ac (ρ*c)) ≤ 1/8 →
      ρ*Ac/(4*min Ac (ρ*c)) ≤ δ^(-vLoss)*(2*ρ) →
      ∀ (n : ℕ) (zOld : Fin n → V) (eOld : Fin n → V ≃ₗᵢ[ℝ] V)
        (z₀ zc : V) (g : V ≃ₗᵢ[ℝ] V),
      let f := carrierAffine (lt_min hAc (mul_pos hρ hc)) hc hρ z₀ zc g
      let ν := fun j => unit (f.linear (boxAxis (eOld j) 2))
      let x := fun j => f (zOld j)-(1/2:ℝ) • ν j
      ∀ (Y Z : Fin n → Set V) (packets : V → Finset (Finset (Fin n)))
        (center : V → Finset (Fin n) → Fin n),
      PacketRefinement β δ θ ν Y Z packets center →
      (∀ j, Y j ⊆ P a (ρ*c) c (zOld j) (eOld j)) →
      (∀ j, (Y j).Nonempty →
        P a (ρ*c) c (zOld j) (eOld j) ⊆ P Ac Bc Cc zc g ∩ ball z₀ (2*c)) →
      ∀ S : Finset (Fin n), (∀ j, j ∉ S → Z j = ∅) →
      O (δ^h*S.card*(2*ρ)^2) ≤ ∑ j, μ (f '' Z j) →
      ∃ (A B : packetLabelUniverse θ x ν → ℝ)
        (z : packetLabelUniverse θ x ν → V)
        (e : packetLabelUniverse θ x ν → V ≃ₗᵢ[ℝ] V)
        (W : (packetLabelUniverse θ x ν) × Fin 6145 → Fin n → Set V),
        (∀ k, 0 ≤ A k ∧ A k ≤ B k ∧ 128*B k ≤ c ∧ B k ≤ 83886080*θ*c) ∧
        (∀ (k : packetLabelUniverse θ x ν),
          (⋃ i, affinePacketPiece f θ ν Z packets center k i).Nonempty → a ≤ A k) ∧
        (∀ (k : packetLabelUniverse θ x ν) i,
          (affinePacketPiece f θ ν Z packets center k i).Nonempty →
          P a (ρ*c) c (zOld i) (eOld i) ⊆ P (A k) (B k) (384*c) (z k) (e k)) ∧
        (∀ p i, MeasurableSet (W p i) ∧ W p i ⊆
          affinePacketPiece f θ ν Z packets center p.1 i ∩
          P (A p.1) (B p.1) (c/8)
            (axialWindowCenter c (384*c) (z p.1) (e p.1) p.2) (e p.1)) ∧
        (∀ i, Pairwise fun p p' => Disjoint (W p i) (W p' i)) ∧
        (1/34:ENNReal)*(∑ i, μ (Z i)) ≤ ∑ p, ∑ i, μ (W p i) ∧
        (∀ p i, (W p i).Nonempty → O (δ^u*(2*ρ)^2) ≤ μ (f '' W p i)) ∧
        (∀ p x' u' r, 2*ρ ≤ r → q n {i | x' ∈ W p i ∧ pd (ν i) u' ≤ r} ≤
          8*(r/θ)^β*q n {i | x' ∈ W p i}) ∧
        ∀ p, (⋃ i, W p i).Nonempty →
          O (δ^ε)*μ (P (128*A p.1) (128*B p.1) c
            (axialWindowCenter c (384*c) (z p.1) (e p.1) p.2) (e p.1)) ≤ μ (⋃ i, W p i) := by
  classical
  obtain ⟨d₀, hd₀, hd₀small, Hfill⟩ := affine_window_fillings_of_cover
    (N := 6145) (Cvol := clippedWindowConstant)
    hβ hs hst hhu hgap (by norm_num [clippedWindowConstant]) (by decide)
  refine ⟨d₀, hd₀, hd₀small, ?_⟩
  intro δ ρ θ a c Ac Bc Cc hδ hδ0 hδρ hρsmall hgrow hθmax ha hρ hc hAc
    hac hα hawidth n zOld eOld z₀ zc g
  dsimp only
  let f := carrierAffine (lt_min hAc (mul_pos hρ hc)) hc hρ z₀ zc g
  let ν := fun j => unit (f.linear (boxAxis (eOld j) 2))
  let x := fun j => f (zOld j)-(1/2:ℝ) • ν j
  let α := ρ*Ac/(4*min Ac (ρ*c))
  intro Y Z packets center hpack hY hbody S hzero hmass
  have hρ1 : ρ ≤ 1 := by linarith
  have hθ1 : θ ≤ 1 := hθmax.trans (by norm_num)
  have hδ1 : δ ≤ 1 := (hδ0.trans hd₀small).trans (by norm_num)
  have hρθ : 2*ρ ≤ θ := by
    have hh : 1 ≤ δ^(-t) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hδ hδ1 (by linarith)
    exact (show 2*ρ ≤ δ^(-t)*(2*ρ) by nlinarith).trans hgrow
  have hθ : 0 < θ := (by positivity : 0 < 2*ρ).trans_le hρθ
  obtain ⟨A, B, z, e, hdim, haA, hwhole, hcover, hvol⟩ :=
    clipped_packet_window_geometry ha hρ hρ1 hc hac hAc hδρ hρθ hα hθmax
      zOld eOld z₀ zc g Y Z packets center hpack hY hbody
  let Λ := packetLabelUniverse θ x ν
  let Core := fun (k : Λ) (j : Fin 6145) => P (A k) (B k) (c/8)
    (axialWindowCenter c (384*c) (z k) (e k) j) (e k)
  let Outer := fun (p : Λ × Fin 6145) => P (128*A p.1) (128*B p.1) c
    (axialWindowCenter c (384*c) (z p.1) (e p.1) p.2) (e p.1)
  have hν (j : Fin n) : ‖ν j‖ = 1 := by
    apply norm_unit
    intro hh
    have hz : boxAxis (eOld j) 2 = 0 := f.linear.injective (hh.trans (map_zero _).symm)
    have hn := boxAxis_norm (eOld j) 2
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hphysical (j : Fin n) (hj : (Y j).Nonempty) :
      P a (ρ*c) c (zOld j) (eOld j) ⊆ P Ac Bc Cc zc g := (hbody j hj).trans inter_subset_left
  have hZT (j : Fin n) : f '' Z j ⊆ T (2*ρ) (x j) (ν j) := by
    rintro _ ⟨p, hp, rfl⟩
    have hj : (Y j).Nonempty := ⟨p, (hpack.1 j).2 hp⟩
    apply (clipped_carrier_grain_tube ha.le hρ hρ1 hc hac hAc
      (zOld j) z₀ zc (eOld j) g (hphysical j hj)).2.2.2.2
    exact mem_image_of_mem f (hY j ((hpack.1 j).2 hp))
  have hZball (j : Fin n) : f '' Z j ⊆ ball (0:V) 1 := by
    rintro _ ⟨p, hp, rfl⟩
    have hj : (Y j).Nonempty := ⟨p, (hpack.1 j).2 hp⟩
    exact ((image_mono (hbody j hj)).trans
      (carrierAffine_ball_and_slab _ hc hρ hα z₀ zc g)).trans inter_subset_left
      (mem_image_of_mem f (hY j ((hpack.1 j).2 hp)))
  have hCoreOuter (p : Λ × Fin 6145) : Core p.1 p.2 ⊆ Outer p := by
    intro q hq
    exact ⟨hq.1.trans (by nlinarith [(hdim p.1).1]),
      hq.2.1.trans (by nlinarith [(hdim p.1).1.trans (hdim p.1).2.1]),
      hq.2.2.trans (by linarith)⟩
  have hUvol (p : Λ × Fin 6145) : μ (f '' Outer p) ≤
      O (clippedWindowConstant*δ^(-vLoss)*(2*ρ)*θ) := by
    refine (hvol p.1 p.2).trans (ENNReal.ofReal_le_ofReal ?_)
    have hh := mul_le_mul_of_nonneg_left hawidth
      (show 0 ≤ clippedWindowConstant*θ by dsimp [clippedWindowConstant]; positivity)
    nlinarith
  obtain ⟨W₀, hW₀, hkeep, hrows, hBr, hden⟩ :=
    Hfill δ (2*ρ) θ hδ hδ0 hδρ hρsmall hgrow hθ1 n x ν Y Z packets center hpack hν f
      hZT hZball S hzero hmass Core Outer
      (fun k j => WangZahlLot.Obl.wz_move_three_thick_grains_gain.measurableSet_P _ _ _ _ _)
      hcover (fun p i => inter_subset_right.trans (hCoreOuter p)) hUvol
  have hdisj (i : Fin n) : Pairwise fun k k' : Λ =>
      Disjoint (affinePacketPiece f θ ν Z packets center k i)
        (affinePacketPiece f θ ν Z packets center k' i) := by
    intro k k' hkk'
    exact ((packet_refinement_affine_image hpack f).piece_disjoint i
      (Subtype.coe_injective.ne hkk')).preimage f
  obtain ⟨r, hcolorMass, hcolorDisj, hcolorSub, hcolorEq⟩ := select_axial_window_color
    hc A B z e (fun k i => affinePacketPiece f θ ν Z packets center k i) W₀ hdisj
      (fun p i => (hW₀ p i).2)
  obtain ⟨hCm, hCBr, hCden⟩ := color_window_properties W₀ r ν Outer
    (fun p i => (hW₀ p i).1) hBr hden
  refine ⟨A, B, z, e, colorWindowRows W₀ r, hdim, haA, hwhole,
    fun p i => ⟨hCm p i, (hcolorSub p i).trans (hW₀ p i).2⟩, hcolorDisj, ?_, ?_, hCBr, hCden⟩
  · have hcfrac : (1/17:ENNReal)*(1/2) = 1/34 := by
      have he (v : ℝ) (hv : 0 < v) : O (1/v) = (1:ENNReal)/O v := by
        dsimp only [O]
        rw [ENNReal.ofReal_div_of_pos hv]
        norm_num [O]
      rw [← show O (17:ℝ) = (17:ENNReal) by norm_num [O],
        ← show O (2:ℝ) = (2:ENNReal) by norm_num [O],
        ← show O (34:ℝ) = (34:ENNReal) by norm_num [O],
        ← he 17 (by norm_num), ← he 2 (by norm_num), ← he 34 (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/17)]
      norm_num [O]
    calc
      _ = (1/17:ENNReal)*((1/2)*(∑ i, μ (Z i))) := by rw [← mul_assoc, hcfrac]
      _ ≤ (1/17:ENNReal)*(∑ p, ∑ i, μ (W₀ p i)) := mul_le_mul' le_rfl hkeep
      _ ≤ _ := hcolorMass
  · intro p i hi
    have he := hcolorEq p (nonempty_iUnion.mpr ⟨i, hi⟩)
    rw [he]
    exact hrows p i (hi.mono (hcolorSub p i))

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
