-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.AffineWindowFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/AffineWindowFilling.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, AffineWindowFilling.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.WindowFillingAssembly
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FilledPacketPullback

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement packetPiece packetLabelUniverse)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

/-- The affine window-filling kernel permits any fixed finite window
geometry. All volume estimates are made in normalized coordinates, and
the resulting mass, density, and broadness statements are physical. -/
theorem affine_window_fillings_of_cover {β t s u h ε vLoss Cvol : ℝ} {N : ℕ}
    (hβ : 0 < β) (hs : 0 < s) (hst : s ≤ t) (hhu : h < u)
    (hgap : 3*u+s+vLoss < ε) (hCvol : 0 < Cvol) (hN : 0 < N) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1/100 ∧ ∀ δ d θ : ℝ,
      0 < δ → δ ≤ d₀ → δ ≤ d → d ≤ 1/100 →
      δ^(-t)*d ≤ θ → θ ≤ 1 →
      ∀ (n : ℕ) (x ν : Fin n → V) (Y Z : Fin n → Set V)
        (packets : V → Finset (Finset (Fin n))) (center : V → Finset (Fin n) → Fin n),
      PacketRefinement β δ θ ν Y Z packets center → (∀ i, ‖ν i‖ = 1) →
      ∀ f : V ≃ᵃ[ℝ] V,
      (∀ i, f '' Z i ⊆ T d (x i) (ν i)) →
      (∀ i, f '' Z i ⊆ ball (0:V) 1) →
      ∀ S : Finset (Fin n), (∀ i, i ∉ S → Z i = ∅) →
      O (δ^h*S.card*d^2) ≤ ∑ i, μ (f '' Z i) →
      ∀ (windows : packetLabelUniverse θ x ν → Fin N → Set V)
        (U : (packetLabelUniverse θ x ν) × Fin N → Set V),
      (∀ k j, MeasurableSet (windows k j)) →
      (∀ (k : packetLabelUniverse θ x ν) i,
        affinePacketPiece f θ ν Z packets center k i ⊆ ⋃ j, windows k j) →
      (∀ p i, affinePacketPiece f θ ν Z packets center p.1 i ∩ windows p.1 p.2 ⊆ U p) →
      (∀ p, μ (f '' U p) ≤ O (Cvol*δ^(-vLoss)*d*θ)) →
      ∃ W : (packetLabelUniverse θ x ν) × Fin N → Fin n → Set V,
        (∀ p i, MeasurableSet (W p i) ∧ W p i ⊆
          affinePacketPiece f θ ν Z packets center p.1 i ∩ windows p.1 p.2) ∧
        (1/2:ENNReal)*(∑ i, μ (Z i)) ≤ ∑ p, ∑ i, μ (W p i) ∧
        (∀ p i, (W p i).Nonempty → O (δ^u*d^2) ≤ μ (f '' W p i)) ∧
        (∀ p x' u' r, d ≤ r → q n {i | x' ∈ W p i ∧ pd (ν i) u' ≤ r} ≤
          8*(r/θ)^β*q n {i | x' ∈ W p i}) ∧
        ∀ p, (⋃ i, W p i).Nonempty → O (δ^ε)*μ (U p) ≤ μ (⋃ i, W p i) := by
  classical
  obtain ⟨d₀, hd₀, hd₀small, Hfill⟩ := window_filling_uniform
    (N := N) (L := 2) (Ccount := 2*6^3*22^3) (Cvol := Cvol)
    hβ hs hst hhu hgap (by norm_num) (by norm_num) hCvol hN
  refine ⟨d₀, hd₀, hd₀small, ?_⟩
  intro δ d θ hδ hδ0 hδd hd1 hgrow hθ1 n x ν Y Z packets center hpack hν f
    hZT hZball S hzero hmass windows U hwm hcover hWinU hUvol
  have hd : 0 < d := hδ.trans_le hδd
  have hθ : 0 < θ := (mul_pos (Real.rpow_pos_of_pos hδ _) hd).trans_le hgrow
  have hδ1 : δ ≤ 1 := (hδ0.trans hd₀small).trans (by norm_num)
  have hdθ : d ≤ θ := by
    have hh : 1 ≤ δ^(-t) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hδ hδ1 (by linarith)
    exact (show d ≤ δ^(-t)*d by nlinarith).trans hgrow
  let Λ := packetLabelUniverse θ x ν
  let Piece := fun (k : Λ) i => packetPiece θ ν (fun i => f '' Z i)
    (fun p => packets (f.symm p)) (fun p Q => center (f.symm p) Q) k i
  let windows' := fun k j => f '' windows k j
  let U' := fun p => f '' U p
  have hnormpack := packet_refinement_affine_image (packet_refinement_radius_mono hpack hδd) f
  have htotal : (∑ k, ∑ i, μ (Piece k i)) = ∑ i, μ (f '' Z i) :=
    (Finset.sum_coe_sort _ _).trans (hnormpack.piece_mass hθ hdθ hν hZT)
  have hcount : (∑ k, q n {i | (Piece k i).Nonempty}) ≤ (2*6^3*22^3:ℝ)*S.card :=
    (Finset.sum_coe_sort (packetLabelUniverse θ x ν)
      (fun k => q n {i | (packetPiece θ ν (fun i => f '' Z i)
        (fun p => packets (f.symm p)) (fun p Q => center (f.symm p) Q) k i).Nonempty})).le.trans
      (WangZahlLot.Obl.wz_move_two_dense_broad_prisms.packet_piece_card_sum_support
        hnormpack hθ hdθ hν hZT S (fun i hi => by rw [hzero i hi, image_empty]))
  have hcover' (k : Λ) (i : Fin n) : Piece k i ⊆ ⋃ j, windows' k j := by
    intro p hp
    have hp' : f.symm p ∈ affinePacketPiece f θ ν Z packets center k i := by
      simpa only [affinePacketPiece, mem_preimage, f.apply_symm_apply] using hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover k i hp')
    exact mem_iUnion.mpr ⟨j, f.symm p, hj, f.apply_symm_apply p⟩
  have hU' (p : Λ × Fin N) (i : Fin n) : windowRows Piece windows' p i ⊆ U' p := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := hq.2
    exact mem_image_of_mem f (hWinU p i ⟨hq.1, hq'⟩)
  obtain ⟨W₀, hW₀, hW₀U, hkeep, hrows, hcounts, hBr, hden⟩ :=
    Hfill δ d θ S.card hδ hδ0 hδd hd1 (by linarith) hgrow hθ1 (Nat.cast_nonneg _)
      n x ν Piece hν (fun k i => hnormpack.measurable_piece k i)
      (fun k i p hp => hZT i hp.1) hcount (htotal.symm ▸ hmass)
      (fun k p u' r hr => WangZahlLot.Obl.wz_move_two_dense_broad_prisms.packet_piece_broad
        hnormpack k p u' r hr) (fun _ => 0) windows' U'
      (fun k i => by simpa only [show (2:ℝ)/2=1 by norm_num] using
        (show Piece k i ⊆ ball (0:V) 1 from fun p hp => hZball i hp.1))
      (fun k j => f.toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
        (hwm k j)) hcover' hU' hUvol
  let W := fun p i => f.symm '' W₀ p i
  have hmem (p : Λ × Fin N) (i : Fin n) (x' : V) : x' ∈ W p i ↔ f x' ∈ W₀ p i := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa only [f.apply_symm_apply] using hq
    · intro hp
      exact ⟨f x', hp, f.symm_apply_apply x'⟩
  have himage (p : Λ × Fin N) (i : Fin n) : f '' W p i = W₀ p i := by
    simp only [W, image_image, f.apply_symm_apply, image_id']
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  · intro p i
    refine ⟨f.symm.toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (hW₀ p i).1, ?_⟩
    intro x' hx'
    have hh := (hW₀ p i).2 ((hmem p i x').mp hx')
    exact ⟨hh.1, f.injective.mem_set_image.mp hh.2⟩
  · apply affine_family_mass_pullback f Z W₀
    simpa only [htotal] using hkeep
  · intro p i hi
    rw [himage]
    exact hrows p i (image_nonempty.mp hi)
  · intro p x' u' r hr
    simpa only [hmem] using hBr p (f x') u' r hr
  · intro p hp
    have hne : (⋃ i, W₀ p i).Nonempty := by
      obtain ⟨i, x', hx'⟩ := nonempty_iUnion.mp hp
      exact nonempty_iUnion.mpr ⟨i, f x', (hmem p i x').mp hx'⟩
    have hh := affine_incidence_mass (n := 1) (Y := fun _ => U' p)
      (Z := fun _ => ⋃ i, W₀ p i) (by simpa only [Fin.sum_univ_one] using hden p hne) f.symm
    simpa only [Fin.sum_univ_one, U', image_image, f.symm_apply_apply, image_id', image_iUnion]
      using hh

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
