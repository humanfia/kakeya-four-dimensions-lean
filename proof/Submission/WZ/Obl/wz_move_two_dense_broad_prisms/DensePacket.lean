-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.DensePacket.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.SubprismGeometry
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.CutDensity

/-! A uniformly massful broad packet yields a dense longer prism. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set Metric
open scoped ENNReal
open wz_measurable_angular_selection (pd)

/-- The local dense-prism step with its numerical density budget explicit.
The hypothesis `d ≤ θ*c` controls the loss from rounding the short sides. -/
theorem dense_broad_packet_prism {n : ℕ} {d a b c θ β r mass D : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hd1 : d ≤ 1/100)
    (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c/100) (hasmall : a ≤ c/1000000)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hround : d ≤ θ*c)
    (hdr : d ≤ r) (hr1 : r ≤ 1) (hmass : 0 ≤ mass) (hD : 0 ≤ D)
    (hcap : 8*(r/θ)^β < 1)
    (hbudget : (1000000000*c*d^5*(1+Real.log (1/d)))*D*
      (100000000000000*(a^2/d)*θ*c^2) ≤ mass^3*r)
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (Y : Fin n → Set V) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hbox : ∀ i, Y i ⊆ P a b c z e) (hball : ∀ i, Y i ⊆ ball z (c/2))
    (hcross : ∀ i, (Y i).Nonempty → Crosses d a b c (x i) (v i) z e)
    (hends : ∀ i p, p ∈ Y i → 40*c ≤ dist p (x i) ∧ 40*c ≤ dist p (x i+v i))
    (hYmass : ∀ i, (Y i).Nonempty → O mass ≤ volume (Y i))
    (hBr : ∀ p u t, d ≤ t →
      q n {i | p ∈ Y i ∧ pd (v i) u ≤ t} ≤ 8*(t/θ)^β*q n {i | p ∈ Y i})
    (i₀ : Fin n) (hi₀ : (Y i₀).Nonempty)
    (hangle : ∀ i, (Y i).Nonempty → pd (v i) (v i₀) ≤ 8*θ) :
    ∃ z' : V, ∃ g : V ≃ₗᵢ[ℝ] V, ∃ W : Fin n → Set V,
      d ≤ 1000000*a ∧ 1000000*a ≤ packetWidth a c θ ∧ packetWidth a c θ ≤ 10*c ∧
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i ∩ P (1000000*a) (packetWidth a c θ) (10*c) z' g) ∧
      O D * volume (P (1000000*a) (packetWidth a c θ) (10*c) z' g) ≤ volume (⋃ i, W i) ∧
      (∀ i, (W i).Nonempty →
        Crosses d (1000000*a) (packetWidth a c θ) (10*c) (x i) (v i) z' g) ∧
      ∀ p u t, d ≤ t → q n {i | p ∈ W i ∧ pd (v i) u ≤ t} ≤
        8*(t/θ)^β*q n {i | p ∈ W i} := by
  have ha : 0 < a := hd.trans_le hda
  have hc : 0 < c := by linarith
  have hr : 0 < r := hd.trans_le hdr
  obtain ⟨z', g, hda', hab', hbc', hpartner, hcross'⟩ := packet_subprism hd hda hab hbc
    hasmall hθ x v hv Y hYT z e hbox hball hcross hends i₀ hi₀ hangle
  let Q := P (1000000*a/8) (packetWidth a c θ/8) (10*c/8) z' g
  let W := fun i => Y i ∩ Q
  have hQm : MeasurableSet Q :=
    (wz_two_scale_flat_box_estimate.box_isClosed _ _ _ _ _).measurableSet
  have hQP : Q ⊆ P (1000000*a) (packetWidth a c θ) (10*c) z' g := by
    intro p hp
    refine ⟨?_, ?_, ?_⟩
    · change |g (p-z') 0| ≤ 1000000*a/2
      have hh : |g (p-z') 0| ≤ (1000000*a/8)/2 := hp.1
      linarith
    · change |g (p-z') 1| ≤ packetWidth a c θ/2
      have hh : |g (p-z') 1| ≤ (packetWidth a c θ/8)/2 := hp.2.1
      linarith
    · change |g (p-z') 2| ≤ 10*c/2
      have hh : |g (p-z') 2| ≤ (10*c/8)/2 := hp.2.2
      linarith
  have hcor := broad_packet_cut_mass hn hd hd1 hr hr1 (by linarith) hmass x v hv Y
    hYm hYT z hball hYmass i₀ hi₀ hcap (fun p _ => hBr p (v i₀) r hdr) Q hQm hpartner
  have hvol : volume (P (1000000*a) (packetWidth a c θ) (10*c) z' g) =
      O ((1000000*a)*packetWidth a c θ*(10*c)) :=
    wz_two_scale_flat_box_estimate.box_volume (by positivity) (by linarith)
      (by positivity) z' g
  have hUfin : volume (⋃ i, W i) ≠ ∞ := by
    apply measure_ne_top_of_subset
      (iUnion_subset (fun i => inter_subset_right.trans hQP))
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  have hsize := (packetWidth_bound hd hda hc hθ hθ1 hround).2.2
  have hlog : 0 < 1+Real.log (1/d) := by
    have hh : (1 : ℝ) ≤ 1/d := (le_div_iff₀ hd).mpr (by linarith)
    linarith [Real.log_nonneg hh]
  have hcoef : 0 < 1000000000*c*d^5*(1+Real.log (1/d)) := by positivity
  have hdense : D*((1000000*a)*packetWidth a c θ*(10*c)) ≤ volume.real (⋃ i, W i) := by
    apply (mul_le_mul_iff_right₀ hcoef).mp
    calc
      _ = (1000000000*c*d^5*(1+Real.log (1/d)))*D*
          ((1000000*a)*packetWidth a c θ*(10*c)) := by ring
      _ ≤ (1000000000*c*d^5*(1+Real.log (1/d)))*D*
          (100000000000000*(a^2/d)*θ*c^2) := by gcongr
      _ ≤ mass^3*r := hbudget
      _ ≤ _ := hcor
  refine ⟨z', g, W, hda', hab', hbc', fun i => ⟨(hYm i).inter hQm,
    fun p hp => ⟨hp.1, hQP hp.2⟩⟩, ?_, hcross', ?_⟩
  · rw [hvol, ← ENNReal.ofReal_mul hD]
    exact (ENNReal.ofReal_le_ofReal hdense).trans_eq (ENNReal.ofReal_toReal hUfin)
  · intro p u t ht
    exact broad_common_cut Q (by have : 0 < t := hd.trans_le ht; positivity) (hBr p u t ht)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
