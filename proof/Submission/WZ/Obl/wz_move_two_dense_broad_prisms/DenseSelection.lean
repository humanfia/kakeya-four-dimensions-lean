-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.DenseSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.DenseInput
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.DensePacket
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PacketPruning
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PacketScale

/-! Angular selection inside the dense enlarged prism, with finite scale labels. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set Metric
open scoped ENNReal
open wz_broad_grains_initialization (PacketRefinement)
open wz_measurable_angular_selection (pd)

/-- The enlarged prism has positive finite volume. -/
lemma DensePrismInput.volume_pos {ω d lam a b L s : ℝ} {n N : ℕ}
    {x v : Fin n → V} {y w : Fin N → V} {Y : Fin n → Set V}
    (B : DensePrismInput ω d lam a b L s x v y w Y) (hd : 0 < d) :
    0 < volume (P a b L B.center B.frame) := by
  have ha : 0 < a := hd.trans_le B.delta_le_thickness
  have hb : 0 < b := ha.trans_le B.thickness_le_width
  have hL : 0 < L := hb.trans_le B.width_le_length
  have hvol : volume (P a b L B.center B.frame) = O (a*b*L) :=
    wz_two_scale_flat_box_estimate.box_volume ha.le hb.le hL.le B.center B.frame
  rw [hvol]
  exact ENNReal.ofReal_pos.mpr (by positivity)

/-- Finite dyadic angular selection retains the requested incidence fraction.
The integrated Katz--Tao bound also excludes scales below `r₀`. -/
theorem DensePrismInput.angular_packet {ω d lam a b L s β m t r₀ : ℝ} {n N K : ℕ}
    {x v : Fin n → V} {y w : Fin N → V} {Y : Fin n → Set V}
    (B : DensePrismInput ω d lam a b L s x v y w Y)
    (hn : 0 < n) (hd : 0 < d) (hd1 : d ≤ 1) (hv : ∀ i, ‖v i‖ = 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hm : 0 ≤ m) (ht : 0 < t)
    (hdK : d ≤ (1/2 : ℝ)^K) (hK2 : (1/2 : ℝ)^K < 2*d)
    (htK : t ≤ 1/(2*((K : ℝ)+1)))
    (hKT : ∀ W : Set V, Convex ℝ W →
      O (q n {i | T d (x i) (v i) ⊆ W}*d^2) ≤ O m*volume W)
    (hbudget : 1728*m*r₀^(2-β) < (t*d^(-ω/2))*d^2) :
    ∃ (k : Fin (K+1)) (Z : Fin n → Set V)
      (F : V → Finset (Finset (Fin n))) (j : V → Finset (Fin n) → Fin n),
      d ≤ (1/2 : ℝ)^(k : ℕ) ∧ (1/2 : ℝ)^(k : ℕ) ≤ 1 ∧
      r₀ < (1/2 : ℝ)^(k : ℕ) ∧
      PacketRefinement β d ((1/2 : ℝ)^(k : ℕ)) v B.shading Z F j ∧
      O t*(∑ i, volume (B.shading i)) ≤ ∑ i, volume (Z i) ∧
      0 < ∑ i, volume (Z i) := by
  obtain ⟨k, Z, F, j, hR, hret⟩ := wz_broad_grains_initialization.measurable_angular_packets
    hn v hv B.shading B.measurable hβ hβ1 hd hK2
  have hdθ : d ≤ (1/2 : ℝ)^(k : ℕ) := hdK.trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.lt_succ_iff.mp k.isLt))
  have hθ : 0 < (1/2 : ℝ)^(k : ℕ) := by positivity
  have hret' : O t*(∑ i, volume (B.shading i)) ≤ ∑ i, volume (Z i) :=
    (mul_le_mul' (ENNReal.ofReal_le_ofReal htK) le_rfl).trans hret
  have hinc : O (t*d^(-ω/2))*volume (P a b L B.center B.frame) ≤
      ∑ i, volume (Z i) := by
    change ENNReal.ofReal (t*d^(-ω/2))*_ ≤ _
    rw [ENNReal.ofReal_mul ht.le, mul_assoc]
    exact (mul_le_mul_right B.incidence (O t)).trans hret'
  have hvolfin : volume (P a b L B.center B.frame) ≠ ∞ := by
    have ha : 0 < a := hd.trans_le B.delta_le_thickness
    have hb : 0 < b := ha.trans_le B.thickness_le_width
    have hvol : volume (P a b L B.center B.frame) = O (a*b*L) :=
      wz_two_scale_flat_box_estimate.box_volume ha.le hb.le
        (hb.le.trans B.width_le_length) B.center B.frame
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  have hlow := packet_scale_lower hd hd1 hθ (by linarith) hm (by positivity)
    (by linarith : β ≤ 2) hv B.in_tube hKT hR
    (wz_two_scale_flat_box_estimate.box_isClosed _ _ _ _ _).measurableSet
    (fun i => (hR.1 i).2.trans (fun _ hp => (B.subset i hp).2))
    (B.volume_pos hd).ne' hvolfin hinc hbudget
  refine ⟨k, Z, F, j, hdθ, pow_le_one₀ (by norm_num) (by norm_num), hlow,
    hR, hret', lt_of_lt_of_le ?_ hinc⟩
  exact bot_lt_iff_ne_bot.mpr (mul_ne_zero
    (ENNReal.ofReal_pos.mpr (by positivity)).ne' (B.volume_pos hd).ne')

/-- A rounded-width-compatible angular refinement of dense input supplies one
fully packaged good prism at the prescribed finite scale label. -/
theorem DensePrismInput.good_piece_of_packet {ω ζ d lam a b L s ε θ mass t r : ℝ}
    {n N J : ℕ} {x v : Fin n → V} {y w : Fin N → V} {Y Z : Fin n → Set V}
    {F : V → Finset (Finset (Fin n))} {j : V → Finset (Fin n) → Fin n}
    (B : DensePrismInput ω d lam a b L s x v y w Y)
    (hn : 0 < n) (hd : 0 < d) (hd1 : d ≤ 1/100)
    (hv : ∀ i, ‖v i‖ = 1) (hθ : 0 < θ) (hdθ : d ≤ θ) (hθ1 : θ ≤ 1)
    (hround : d ≤ θ*L) (hmass : 0 ≤ mass) (ht : 0 ≤ t)
    (hR : PacketRefinement (ω*ζ/100) d θ v B.shading Z F j)
    (hZpos : 0 < ∑ i, volume (Z i))
    (hret : O t*(∑ i, volume (B.shading i)) ≤ ∑ i, volume (Z i))
    (hprune : (2*6^3*22^3 : ℝ)*mass ≤ t*(lam*L*d^2/256)/4)
    (hdr : d ≤ r) (hr1 : r ≤ 1) (hcap : 8*(r/θ)^(ω*ζ/100) < 1)
    (hdensity : (1000000000*L*d^5*(1+Real.log (1/d)))*(d^ε)*
      (100000000000000*(a^2/d)*θ*L^2) ≤ mass^3*r)
    (k : Fin J) (ρ : Fin J → ℝ) (hρ : ρ k = packetWidth a L θ/(10*L))
    (hbroad : 8*(ρ k/θ)^(ω*ζ/100) ≤ d^(-ε)) :
    ∃ Q : PrismPiece n N J, Q.scale = k ∧
      Q.Good ω ζ d ε (1000000*a) (10*L) s ρ x v y w ∧ ∀ i, Q.piece i ⊆ Y i := by
  have ha : 0 < a := hd.trans_le B.delta_le_thickness
  have hL : 0 < L := (hd.trans_le B.delta_le_thickness).trans_le
    (B.thickness_le_width.trans B.width_le_length)
  obtain ⟨R, i₀, hRm, hi₀, hmassR, hangle, hBr⟩ :=
    exists_massful_broad_packet_of_retention hR hd hθ hdθ hmass ht hv B.in_tube
      B.tube_mass hZpos hret hprune
  have hRB (i) : R i ⊆ B.shading i := (hRm i).2.trans (hR.1 i).2
  obtain ⟨z', e', W, hda', hab', hbc', hW, hden, hcross, hBrW⟩ :=
    dense_broad_packet_prism hn hd hd1 B.delta_le_thickness B.thickness_le_width
      B.width_small B.thickness_small hθ hθ1 hround hdr hr1 hmass
      (Real.rpow_nonneg hd.le _) hcap hdensity x v hv R (fun i => (hRm i).1)
      (fun i => (hRB i).trans (B.in_tube i)) B.center B.frame
      (fun i p hp => (B.subset i (hRB i hp)).2)
      (fun i => (hRB i).trans (B.in_ball i))
      (fun i hi => (B.crossing i (hi.mono (hRB i))).2)
      (fun i p hp => by
        have hh := B.endpoints i p (hRB i hp)
        constructor <;> linarith)
      hmassR hBr i₀ hi₀ hangle
  have hwidth : ρ k*(10*L) = packetWidth a L θ := by
    rw [hρ, div_mul_cancel₀ _ (by positivity)]
  have hρpos : 0 < ρ k := by
    rw [hρ]
    exact div_pos (lt_of_lt_of_le (by positivity) hab') (by positivity)
  refine ⟨⟨k, B.coarse, z', e', W⟩, rfl, ?_, ?_⟩
  · change d ≤ 1000000*a ∧ 1000000*a ≤ ρ k*(10*L) ∧ ρ k*(10*L) ≤ 10*L ∧ _
    rw [hwidth]
    refine ⟨hda', hab', hbc', B.ten_length_le_one,
      fun i => ⟨(hW i).1, fun p hp => ((hW i).2 hp).2⟩, hden, ?_, ?_⟩
    · intro i hi
      refine ⟨(B.crossing i (hi.mono (fun p hp => hRB i ((hW i).2 hp).1))).1,
        hcross i hi⟩
    · intro p u r' _ hdr' _
      exact broad_scale_change (hd.trans_le hdr') hθ hρpos hbroad (hBrW p u r' hdr')
  · intro i p hp
    exact (B.subset i (hRB i ((hW i).2 hp).1)).1

/-- The unresolved narrow case retains its full measurable angular refinement,
rather than only the numerical inequality on the scale. -/
def DensePrismInput.Narrow {ω d lam a b L s : ℝ} {n N : ℕ}
    {x v : Fin n → V} {y w : Fin N → V} {Y : Fin n → Set V}
    (B : DensePrismInput ω d lam a b L s x v y w Y) (β r₀ t : ℝ) (K : ℕ) : Prop :=
  ∃ (k : Fin (K+1)) (Z : Fin n → Set V)
    (F : V → Finset (Finset (Fin n))) (j : V → Finset (Fin n) → Fin n),
    d ≤ (1/2 : ℝ)^(k : ℕ) ∧ (1/2 : ℝ)^(k : ℕ) ≤ 1 ∧
    r₀ < (1/2 : ℝ)^(k : ℕ) ∧ (1/2 : ℝ)^(k : ℕ)*L < d ∧
    PacketRefinement β d ((1/2 : ℝ)^(k : ℕ)) v B.shading Z F j ∧
    O t*(∑ i, volume (B.shading i)) ≤ ∑ i, volume (Z i)

/-- Dense local input produces a good prism at one of finitely many fixed
scales, unless its retained angular packet lies below the width-rounding scale. -/
theorem DensePrismInput.piece_or_narrow {ω ζ d lam a b L s ε m t mass r₀ : ℝ}
    {n N K : ℕ} {x v : Fin n → V} {y w : Fin N → V} {Y : Fin n → Set V}
    (B : DensePrismInput ω d lam a b L s x v y w Y)
    (hn : 0 < n) (hd : 0 < d) (hd1 : d ≤ 1/100) (hv : ∀ i, ‖v i‖ = 1)
    (hβ : 0 < ω*ζ/100) (hβ1 : ω*ζ/100 ≤ 1)
    (hm : 0 ≤ m) (ht : 0 < t) (hmass : 0 ≤ mass)
    (hdK : d ≤ (1/2 : ℝ)^K) (hK2 : (1/2 : ℝ)^K < 2*d)
    (htK : t ≤ 1/(2*((K : ℝ)+1)))
    (hKT : ∀ W : Set V, Convex ℝ W →
      O (q n {i | T d (x i) (v i) ⊆ W}*d^2) ≤ O m*volume W)
    (hscale : 1728*m*r₀^(2-ω*ζ/100) < (t*d^(-ω/2))*d^2)
    (hprune : (2*6^3*22^3 : ℝ)*mass ≤ t*(lam*L*d^2/256)/4)
    (ρ : Fin (K+1) → ℝ)
    (hρ : ∀ k, ρ k = packetWidth a L ((1/2 : ℝ)^(k : ℕ))/(10*L))
    (hparams : ∀ k : Fin (K+1), r₀ < (1/2 : ℝ)^(k : ℕ) →
      d ≤ (1/2 : ℝ)^(k : ℕ)*L →
      ∃ r : ℝ, d ≤ r ∧ r ≤ 1 ∧ 8*(r/((1/2 : ℝ)^(k : ℕ)))^(ω*ζ/100) < 1 ∧
        (1000000000*L*d^5*(1+Real.log (1/d)))*(d^ε)*
          (100000000000000*(a^2/d)*((1/2 : ℝ)^(k : ℕ))*L^2) ≤ mass^3*r ∧
        8*(ρ k/((1/2 : ℝ)^(k : ℕ)))^(ω*ζ/100) ≤ d^(-ε)) :
    B.Narrow (ω*ζ/100) r₀ t K ∨
    ∃ Q : PrismPiece n N (K+1), Q.Good ω ζ d ε (1000000*a) (10*L) s ρ x v y w ∧
      (∀ i, Q.piece i ⊆ Y i) ∧ r₀ < ρ Q.scale := by
  obtain ⟨k, Z, F, j, hdθ, hθ1, hlow, hR, hret, hZpos⟩ :=
    B.angular_packet hn hd (by linarith) hv hβ hβ1 hm ht hdK hK2 htK hKT hscale
  by_cases hround : d ≤ (1/2 : ℝ)^(k : ℕ)*L
  · obtain ⟨r, hdr, hr1, hcap, hden, hBr⟩ := hparams k hlow hround
    obtain ⟨Q, hQk, hQ, hQY⟩ := B.good_piece_of_packet hn hd hd1 hv
      (by positivity) hdθ hθ1 hround hmass ht.le hR hZpos hret hprune
      hdr hr1 hcap hden k ρ (hρ k) hBr
    refine Or.inr ⟨Q, hQ, hQY, ?_⟩
    rw [hQk, hρ]
    exact hlow.trans_le (packetWidth_bound hd B.delta_le_thickness
      ((hd.trans_le B.delta_le_thickness).trans_le
        (B.thickness_le_width.trans B.width_le_length))
      (by positivity) hθ1 hround).1
  · exact Or.inl ⟨k, Z, F, j, hdθ, hθ1, hlow, lt_of_not_ge hround, hR, hret⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
