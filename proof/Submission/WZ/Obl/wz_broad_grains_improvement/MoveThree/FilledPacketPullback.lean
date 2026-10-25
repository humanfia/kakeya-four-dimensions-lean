-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FilledPacketPullback.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FilledPacketPullback.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, FilledPacketPullback.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FilledPacketPrisms
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PacketAffineMass

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_broad_grains_initialization (PacketRefinement PacketLabel packetPiece)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

/-- A common inverse Jacobian cancels in a relative mass bound even when
the output has an additional finite label index. -/
theorem affine_family_mass_pullback {κ : Type*} [Fintype κ] {n : ℕ}
    (f : V ≃ᵃ[ℝ] V) (Y : Fin n → Set V) (W : κ → Fin n → Set V) {t : ENNReal}
    (h : t * (∑ i, μ (f '' Y i)) ≤ ∑ k, ∑ i, μ (W k i)) :
    t * (∑ i, μ (Y i)) ≤ ∑ k, ∑ i, μ (f.symm '' W k i) := by
  have hvol (U : Set V) : μ (f.symm '' U) =
      O |LinearMap.det (f.symm.linear : V →ₗ[ℝ] V)| * μ U :=
    WangZahlLot.Obl.wz_regular_transverse_affine_cells.affineEquiv_volume f.symm U
  have hh : t * (∑ i, μ (f.symm '' (f '' Y i))) ≤ ∑ k, ∑ i, μ (f.symm '' W k i) := by
    simp only [hvol, ← Finset.mul_sum, mul_left_comm t]
    exact mul_le_mul' le_rfl h
  simpa only [Set.image_image, f.symm_apply_apply, Set.image_id'] using hh

/-- All labels can be pulled back simultaneously. Relative mass and angular
counts are unchanged; every occupied label has a growing physical prism.
Disjointness is only asserted for pieces of the same old grain. -/
theorem physicalize_packet_fillings {β q₀ jump : ℝ}
    (hβ : 0 ≤ β) (hjump : 0 < jump) (hgap : β + 3 * jump < q₀) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ {κ : Type*} [Fintype κ]
        {h ρ a c b g m A₀ B₀ C₀ K D θ rmin : ℝ} {n N L : ℕ}
        {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
        {y w : Fin N → V} {f₀ : Fin n → Fin N}
        {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
        {Hs H Zp : Fin L → Set V} {γ : Fin L → Fin N} {ν : Fin L → V}
        {packets : V → Finset (Finset (Fin L))}
        {center : V → Finset (Fin L) → Fin L},
      0 < ρ → δ ≤ θ → (∀ k, ‖w k‖ = 1) → X ρ N y w →
      GrainWitnesses δ h n x v S Z ρ N y w f₀ a c b g L z e Hs γ m →
      (∀ j, H j ⊆ Hs j) →
      (∀ p ∈ ⋃ j, H j, δ ^ (-q₀) < q L {j | p ∈ H j}) →
      PacketRefinement β δ θ ν H Zp packets center →
      0 ≤ A₀ → A₀ ≤ B₀ → B₀ ≤ C₀ → 0 < C₀ → 0 < K → 0 ≤ D →
      ∀ (f : V ≃ᵃ[ℝ] V) (label : κ → PacketLabel), Function.Injective label →
      ∀ (z₀ : κ → V) (e₀ : κ → V ≃ₗᵢ[ℝ] V) (W : κ → Fin L → Set V) (keep : ENNReal),
      (∀ p q, dist (f.symm p) (f.symm q) ≤ (K * c) * dist p q) →
      (∀ k j, (affinePacketPiece f θ ν Zp packets center (label k) j).Nonempty →
        f '' P a (ρ * c) c (z j) (e j) ⊆ P A₀ B₀ C₀ (z₀ k) (e₀ k)) →
      (∀ k j, MeasurableSet (W k j) ∧ W k j ⊆
        packetPiece θ ν (fun j => f '' Zp j) (fun p => packets (f.symm p))
          (fun p Q => center (f.symm p) Q) (label k) j) →
      (∀ k j, W k j ⊆ P A₀ B₀ C₀ (z₀ k) (e₀ k)) →
      keep * (∑ j, μ (f '' Zp j)) ≤ ∑ k, ∑ j, μ (W k j) →
      (∀ k p u r, rmin ≤ r → q L {j | p ∈ W k j ∧ pd (ν j) u ≤ r} ≤
        8 * (r / θ) ^ β * q L {j | p ∈ W k j}) →
      (∀ k, (⋃ j, W k j).Nonempty →
        O D * μ (P A₀ B₀ C₀ (z₀ k) (e₀ k)) ≤ μ (⋃ j, W k j)) →
      ∃ B : κ → Fin L → Set V,
        (∀ k j, MeasurableSet (B k j) ∧ B k j ⊆
          affinePacketPiece f θ ν Zp packets center (label k) j) ∧
        (∀ j, Pairwise fun k k' => Disjoint (B k j) (B k' j)) ∧
        keep * (∑ j, μ (Zp j)) ≤ ∑ k, ∑ j, μ (B k j) ∧
        (∀ k p u r, rmin ≤ r → q L {j | p ∈ B k j ∧ pd (ν j) u ≤ r} ≤
          8 * (r / θ) ^ β * q L {j | p ∈ B k j}) ∧
        ∀ k, (⋃ j, B k j).Nonempty →
          ∃ (A B' : ℝ) (z' : V) (e' : V ≃ₗᵢ[ℝ] V),
            a ≤ A ∧ A ≤ B' ∧ B' ≤ 8 * K * C₀ * c ∧ δ ^ (-jump) * ρ * c ≤ B' ∧
            (∀ j, (affinePacketPiece f θ ν Zp packets center (label k) j).Nonempty →
              P a (ρ * c) c (z j) (e j) ⊆ P A B' (8 * K * C₀ * c) z' e') ∧
            (⋃ j, B k j) ⊆ P A B' (8 * K * C₀ * c) z' e' ∧
            O (D / (6912 * K * C₀)) * μ (P A B' (8 * K * C₀ * c) z' e') ≤ μ (⋃ j, B k j) := by
  obtain ⟨d₀, hd₀, hd₀1, Hphysical⟩ := HB_filled_affine_label_prism hβ hjump hgap
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδd κ inst h ρ a c b g m A₀ B₀ C₀ K D θ rmin n N L x v S Z y w f₀ z e
    Hs H Zp γ ν packets center hρ hδθ hw hX hHB hsub hhigh hpack hA₀ hAB₀ hBC₀ hC₀ hK hD
    f label hinj z₀ e₀ W keep hInv hwhole hW hWbox hmass hbroad hdense
  let B := fun k j => f.symm '' W k j
  have hmem (k : κ) (j : Fin L) (p : V) : p ∈ B k j ↔ f p ∈ W k j := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa only [f.apply_symm_apply] using hq
    · intro hp
      exact ⟨f p, hp, f.symm_apply_apply p⟩
  have hB (k : κ) (j : Fin L) : MeasurableSet (B k j) ∧
      B k j ⊆ affinePacketPiece f θ ν Zp packets center (label k) j := by
    refine ⟨f.symm.toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (hW k j).1, ?_⟩
    intro p hp
    exact (hW k j).2 ((hmem k j p).mp hp)
  have hBunion (k : κ) : (⋃ j, B k j) = f.symm '' (⋃ j, W k j) := by
    exact (image_iUnion).symm
  refine ⟨B, hB, ?_, affine_family_mass_pullback f Zp W hmass, ?_, ?_⟩
  · intro j k k' hkk'
    exact ((packet_refinement_affine_image hpack f).piece_disjoint j (hinj.ne hkk')).preimage f |>.mono
      (hB k j).2 (hB k' j).2
  · intro k p u r hr
    simpa only [hmem] using hbroad k (f p) u r hr
  · intro k hk
    have hWne : (⋃ j, W k j).Nonempty := by
      rw [hBunion k] at hk
      exact image_nonempty.mp hk
    have hne : (⋃ j, affinePacketPiece f θ ν Zp packets center (label k) j).Nonempty :=
      hk.mono (iUnion_mono fun j => (hB k j).2)
    obtain ⟨A, B', z', e', haA, hAB, hB', hgrow, hbody, _, hshade, hden⟩ :=
      Hphysical δ hδ hδd hρ hδθ hw hX hHB hsub hhigh hpack hA₀ hAB₀ hBC₀ hC₀ hK hD
        f (label k) (z₀ k) (e₀ k) (⋃ j, W k j) hInv (hwhole k) hne
        (MeasurableSet.iUnion fun j => (hW k j).1) (iUnion_subset fun j => hWbox k j)
        (hdense k hWne)
    exact ⟨A, B', z', e', haA, hAB, hB', hgrow, hbody,
      (hBunion k).symm ▸ hshade, (hBunion k).symm ▸ hden⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
