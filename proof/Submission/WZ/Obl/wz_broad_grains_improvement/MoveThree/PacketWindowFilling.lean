-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketWindowFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketWindowFilling.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, PacketWindowFilling.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketWindowGeometry
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AffineWindowFilling

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_broad_grains_initialization
  (PacketRefinement packetPiece packetLabelUniverse)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

/-- Window filling applied to the actual affine packet geometry. Each occupied
physical outer window is dense; the whole family retains half the original
packet mass, at the original prescribed long length. -/
theorem affine_packet_window_fillings {β t s u h ε vLoss : ℝ}
    (hβ : 0 < β) (hs : 0 < s) (hst : s ≤ t) (hhu : h < u)
    (hgap : 3*u+s+vLoss < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1/100 ∧ ∀ δ d θ a₀ a b c : ℝ,
      0 < δ → δ ≤ d₀ → δ ≤ d → d ≤ 1/100 →
      δ^(-t)*d ≤ θ → θ ≤ 1 → 0 < a → a ≤ b → b ≤ c →
      0 < a₀ → a₀ ≤ 1/8 → a₀ ≤ δ^(-vLoss)*d →
      ∀ (n : ℕ) (x ν zOld : Fin n → V) (eOld : Fin n → V ≃ₗᵢ[ℝ] V)
        (Y Z : Fin n → Set V) (packets : V → Finset (Finset (Fin n)))
        (center : V → Finset (Fin n) → Fin n),
      PacketRefinement β δ θ ν Y Z packets center → (∀ i, ‖ν i‖ = 1) →
      (∀ i, Y i ⊆ P a b c (zOld i) (eOld i)) → ∀ f : V ≃ᵃ[ℝ] V,
      (∀ p q, dist (f.symm p) (f.symm q) ≤ (4*c)*dist p q) →
      (∀ i, (Y i).Nonempty → f '' P a b c (zOld i) (eOld i) ⊆ T d (x i) (ν i)) →
      (∀ i, (Y i).Nonempty → f '' P a b c (zOld i) (eOld i) ⊆ ball (0:V) 1) →
      ∀ (normal : V) (offset : ℝ), ‖normal‖ = 1 →
      (∀ i, (Y i).Nonempty → f '' P a b c (zOld i) (eOld i) ⊆
        {p | |inner ℝ normal p-offset| ≤ a₀/2}) →
      (∀ i, (Y i).Nonempty → |inner ℝ normal (ν i)| ≤ 4*a₀) →
      ∀ S : Finset (Fin n), (∀ i, i ∉ S → Z i = ∅) →
      O (δ^h*S.card*d^2) ≤ ∑ i, μ (f '' Z i) →
      ∃ (A B : packetLabelUniverse θ x ν → ℝ)
        (z : packetLabelUniverse θ x ν → V)
        (e : packetLabelUniverse θ x ν → V ≃ₗᵢ[ℝ] V)
        (W : (packetLabelUniverse θ x ν) × Fin 2049 → Fin n → Set V),
        (∀ k, 0 ≤ A k ∧ A k ≤ B k ∧ B k ≤ 128*c) ∧
        (∀ (k : packetLabelUniverse θ x ν),
          (⋃ i, affinePacketPiece f θ ν Z packets center k i).Nonempty → a ≤ A k) ∧
        (∀ (k : packetLabelUniverse θ x ν) i,
          (affinePacketPiece f θ ν Z packets center k i).Nonempty →
          P a b c (zOld i) (eOld i) ⊆ P (A k) (B k) (128*c) (z k) (e k)) ∧
        (∀ p i, MeasurableSet (W p i) ∧ W p i ⊆
          affinePacketPiece f θ ν Z packets center p.1 i ∩
          P (A p.1) (B p.1) (c/8)
            (axialWindowCenter c (128*c) (z p.1) (e p.1) p.2) (e p.1)) ∧
        (1/2:ENNReal)*(∑ i, μ (Z i)) ≤ ∑ p, ∑ i, μ (W p i) ∧
        (∀ p i, (W p i).Nonempty → O (δ^u*d^2) ≤ μ (f '' W p i)) ∧
        (∀ p x' u' r, d ≤ r → q n {i | x' ∈ W p i ∧ pd (ν i) u' ≤ r} ≤
          8*(r/θ)^β*q n {i | x' ∈ W p i}) ∧
        ∀ p, (⋃ i, W p i).Nonempty →
          O (δ^ε)*μ (P (128*A p.1) (128*B p.1) c
            (axialWindowCenter c (128*c) (z p.1) (e p.1) p.2) (e p.1)) ≤ μ (⋃ i, W p i) := by
  classical
  obtain ⟨d₀, hd₀, hd₀small, Hfill⟩ := affine_window_fillings_of_cover
    (N := 2049) (Cvol := packetWindowConstant)
    hβ hs hst hhu hgap (by norm_num [packetWindowConstant]) (by decide)
  refine ⟨d₀, hd₀, hd₀small, ?_⟩
  intro δ d θ a₀ a b c hδ hδ0 hδd hd1 hgrow hθ1 ha hab hbc ha₀ ha₀8 hawidth
    n x ν zOld eOld Y Z packets center hpack hν hY f hInv hT hball normal offset hnormal hslab hflat
    S hzero hmass
  have hc : 0 < c := ha.trans_le (hab.trans hbc)
  have hd : 0 < d := hδ.trans_le hδd
  have hθ : 0 < θ := (mul_pos (Real.rpow_pos_of_pos hδ _) hd).trans_le hgrow
  have hδ1 : δ ≤ 1 := (hδ0.trans hd₀small).trans (by norm_num)
  have hdθ : d ≤ θ := by
    have hh : 1 ≤ δ^(-t) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hδ hδ1 (by linarith)
    exact (show d ≤ δ^(-t)*d by nlinarith).trans hgrow
  obtain ⟨A, B, z, e, hdim, haA, hbody, hcover, hvol⟩ := affine_packet_window_geometry
    hpack hδd hdθ hθ ha hab hbc ha₀ ha₀8 hν hY f hInv hT hball normal offset hnormal hslab hflat
  let Λ := packetLabelUniverse θ x ν
  let Core := fun (k : Λ) (j : Fin 2049) => P (A k) (B k) (c/8)
    (axialWindowCenter c (128*c) (z k) (e k) j) (e k)
  let Outer := fun (p : Λ × Fin 2049) => P (128*A p.1) (128*B p.1) c
    (axialWindowCenter c (128*c) (z p.1) (e p.1) p.2) (e p.1)
  have hZT (i : Fin n) : f '' Z i ⊆ T d (x i) (ν i) := by
    rintro _ ⟨p, hp, rfl⟩
    exact hT i ⟨p, (hpack.1 i).2 hp⟩ ⟨p, hY i ((hpack.1 i).2 hp), rfl⟩
  have hZball (i : Fin n) : f '' Z i ⊆ ball (0:V) 1 := by
    rintro _ ⟨p, hp, rfl⟩
    exact hball i ⟨p, (hpack.1 i).2 hp⟩ ⟨p, hY i ((hpack.1 i).2 hp), rfl⟩
  have hCoreOuter (p : Λ × Fin 2049) : Core p.1 p.2 ⊆ Outer p := by
    intro x hx
    exact ⟨hx.1.trans (by nlinarith [(hdim p.1).1]),
      hx.2.1.trans (by nlinarith [(hdim p.1).1.trans (hdim p.1).2.1]),
      hx.2.2.trans (by linarith)⟩
  have hUvol (p : Λ × Fin 2049) : μ (f '' Outer p) ≤
      O (packetWindowConstant*δ^(-vLoss)*d*θ) := by
    refine (hvol p.1 p.2).trans (ENNReal.ofReal_le_ofReal ?_)
    have hh := mul_le_mul_of_nonneg_left hawidth
      (show 0 ≤ packetWindowConstant*θ by dsimp [packetWindowConstant]; positivity)
    nlinarith
  obtain ⟨W, hW, hkeep, hrows, hBr, hden⟩ :=
    Hfill δ d θ hδ hδ0 hδd hd1 hgrow hθ1 n x ν Y Z packets center hpack hν f
      hZT hZball S hzero hmass Core Outer
      (fun k j => WangZahlLot.Obl.wz_move_three_thick_grains_gain.measurableSet_P _ _ _ _ _)
      hcover (fun p i => inter_subset_right.trans (hCoreOuter p)) hUvol
  exact ⟨A, B, z, e, W, hdim, haA, hbody, hW, hkeep, hrows, hBr, hden⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
