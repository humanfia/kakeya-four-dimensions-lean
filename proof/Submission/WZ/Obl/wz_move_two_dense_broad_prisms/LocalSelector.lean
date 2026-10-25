-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.LocalSelector.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.WideSelector
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.NarrowBundle
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.NarrowBudgets
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RadiusPalette
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.ShapePalette
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Parameters
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RealMass

/-! Both angular regimes give a dense broad prism at a finite shape label. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal

/-- A dense input inside a simultaneously regular shading always supplies a
longer good prism. Narrow packets are extended before the common high-count cut. -/
theorem regular_dense_local_selector {ω ζ ε d h a b c s : ℝ} {n N K : ℕ}
    (par : LengtheningParameters ω ζ ε)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) (hε : 0 < ε)
    (hd : 0 < d) (hd100 : d ≤ 1/100) (hh : h ≤ par.eta/8)
    (hdc : d ≤ c) (hc : c ≤ d^(9*ω/20)) (ha : a ≤ 2*d^(1-par.thin))
    (hsmall : (10:ℝ)^40*d^(par.eta/4) ≤ 1)
    (hlog : (10:ℝ)^40*(1+Real.log (1/d))*d^(ε/2) ≤ 1)
    (hdK : d ≤ (1/2:ℝ)^K) (hK2 : (1/2:ℝ)^K < 2*d)
    (hcount : d^(par.eta/2) ≤ 1/(2*((K:ℝ)+1)))
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1) (hn : 0 < n)
    (y w : Fin N → V) (U : Fin n → Set V)
    (hUm : ∀ i, MeasurableSet (U i)) (hUT : ∀ i, U i ⊆ T d (x i) (v i))
    (hends : ∀ i p, p ∈ U i → d^(ω/1000) < dist p (x i) ∧ d^(ω/1000) < dist p (x i+v i))
    (hreg : ∀ i p, p ∈ U i → ∀ j,
      O (d^par.eta*radiusPalette d (d^(-ω/100)*c) K j*d^2/32) ≤
        volume (U i ∩ ball p (radiusPalette d (d^(-ω/100)*c) K j)))
    (B : DensePrismInput ω d (d^par.eta) (10000*a) b (d^(-ω/100)*c) s x v y w U)
    (hKT : ∀ W : Set V, Convex ℝ W →
      O (q n {i | T d (x i) (v i) ⊆ W}*d^2) ≤ O (d^(-h))*volume W) :
    ∃ Q : PrismPiece n N ((K+1)+(K+1)),
      Q.Good ω ζ d ε (thicknessPalette d a K Q.scale)
        (lengthPalette d (d^(-ω/100)*c) K Q.scale) s
        (broadnessPalette d a (d^(-ω/100)*c) K) x v y w ∧
      (∀ i, Q.piece i ⊆ U i) ∧
      d^(1-ω/100) ≤ broadnessPalette d a (d^(-ω/100)*c) K Q.scale ∧
      d^(-ω/150)*c ≤ lengthPalette d (d^(-ω/100)*c) K Q.scale := by
  have hη := par.eta_pos
  have hd1 : d ≤ 1 := hd100.trans (by norm_num)
  have hcp : 0 < c := hd.trans_le hdc
  have hL : 0 < d^(-ω/100)*c := by positivity
  obtain ⟨hβ, hβ1, hβω⟩ := broadness_exponent_bounds hω hω1 hζ hζω
  have hs : (10:ℝ)^40*d^(par.eta/2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hd hd1
      (by linarith [par.eta_pos] : par.eta/4 ≤ par.eta/2)) (by positivity)).trans hsmall
  have hpalette := palette_count_budget hd hd1 par.eta_pos par.eta_epsilon hsmall hcount
  have hwide := B.quantitative_piece_or_narrow hn hd hd100 hv hω hβ hβ1 hβω
    par.eta_pos hε par.eta_omega par.eta_beta_omega par.eta_epsilon par.eta_beta_epsilon
    par.thin_pos.le par.thin_epsilon (by linarith : h ≤ par.eta/4)
    (by nlinarith : 10000*a ≤ 20000*d^(1-par.thin)) hs hlog hdK hK2 hpalette.2.1 hKT
  have hlengthgain := longer_prism_length_budget hd hd1 hω.le hcp.le
  rcases hwide with hN | ⟨Q, hQ, hQU, hlow⟩
  · obtain ⟨k, p, u, F, hu, hF, hdθ, hθ1, hlow, hnarrow, hp, hang, hcap⟩ :=
      hN.fixed_packet hd (Real.rpow_pos_of_pos hd _) hv
    have hθ : 0 < (1/2:ℝ)^(k:ℕ) := by positivity
    have hθsmall := narrow_scale_upper hd hd1 par.eta_pos par.eta_omega hdc hθ.le hnarrow.le hsmall
    have hroom := (regular_endpoint_budgets hd hd1 hω hω1 par.eta_pos par.eta_omega hc hsmall).2.2.2
      ((1/2:ℝ)^(k:ℕ)) hlow.le
    have hR1 : d^(ω/1000) ≤ 1 := Real.rpow_le_one hd.le hd1 (by positivity)
    have hell1 : d/((1/2:ℝ)^(k:ℕ)) ≤ 1 := by linarith
    have hlength : 10*(d/((1/2:ℝ)^(k:ℕ))) ≤ 1 := by linarith
    have hcost := narrow_cut_budgets hd hd1 par.eta_pos par.eta_epsilon hβ.le hβ1 hsmall
    have hmass : (d^par.eta/1000000000000)*
        ((10000*d)*(10000*d)*(10*(d/((1/2:ℝ)^(k:ℕ))))) ≤
        d^par.eta*(d/((1/2:ℝ)^(k:ℕ)))*d^2/64 := by
      have hh' := mul_le_mul_of_nonneg_right (by norm_num : (1/1000:ℝ) ≤ 1/64)
        (show 0 ≤ d^par.eta*(d/((1/2:ℝ)^(k:ℕ)))*d^2 by positivity)
      convert hh' using 1 <;> ring
    have hrow (i : Fin n) (hi : i ∈ F) :
        O (d^par.eta*(d/((1/2:ℝ)^(k:ℕ)))*d^2/64) ≤
          volume (U i ∩ ball p ((d/((1/2:ℝ)^(k:ℕ)))/2)) := by
      have hh' := hreg i p ((B.subset i (hp i hi)).1) k.succ
      rw [radiusPalette_narrow k hd hθsmall hell1] at hh'
      convert hh' using 1 <;> congr 1 <;> ring
    obtain ⟨Q, hQk, _, hQ, hQU⟩ := narrow_fixed_packet_good hd hθ hθsmall hlength
      (by positivity : 0 < d^par.eta/1000000000000) hmass hcost.1 hcost.2
      x v hv y w B.coarse (fun k => 1000*((1/2:ℝ)^(k:ℕ))) k rfl U hUm hUT F hF p u hu
      (fun i hi => (B.subset i (hp i hi)).1) hang
      (fun i hi => ⟨hroom.trans (hends i p ((B.subset i (hp i hi)).1)).1.le,
        hroom.trans (hends i p ((B.subset i (hp i hi)).1)).2.le⟩)
      (fun i hi => (B.crossing i ⟨p, hp i hi⟩).1) hrow hcap
    have hQ' : Q.Good ω ζ d ε (10000*d) (10*(d/((1/2:ℝ)^(Q.scale:ℕ)))) s
        (fun k => 1000*((1/2:ℝ)^(k:ℕ))) x v y w := by simpa only [hQk] using hQ
    refine ⟨Q.relabel (Fin.natAdd (K+1)), narrow_piece_relabel hQ', hQU, ?_, ?_⟩
    · simp only [PrismPiece.relabel, broadnessPalette, Fin.addCases_right, hQk]
      linarith
    · simp only [PrismPiece.relabel, lengthPalette, Fin.addCases_right, hQk]
      have hext : d^(-ω/100)*c ≤ d/((1/2:ℝ)^(k:ℕ)) :=
        (le_div_iff₀ hθ).mpr (by nlinarith)
      exact hlengthgain.trans (mul_le_mul_of_nonneg_left hext (by norm_num))
  · refine ⟨Q.relabel (Fin.castAdd (K+1)), wide_piece_relabel hQ, hQU, ?_, ?_⟩
    · simpa only [PrismPiece.relabel, broadnessPalette, Fin.addCases_left] using hlow.le
    · simpa only [PrismPiece.relabel, lengthPalette, Fin.addCases_left] using hlengthgain

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
