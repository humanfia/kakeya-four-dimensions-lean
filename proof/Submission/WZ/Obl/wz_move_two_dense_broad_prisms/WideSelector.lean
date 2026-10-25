-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.WideSelector.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.DenseSelection
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PacketBudgets

/-! The wide-packet selector with all scalar budgets discharged. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory

/-- A dense prism gives a wide good piece or the full narrow packet data.
Every numerical hypothesis now concerns only the common small parameters. -/
theorem DensePrismInput.quantitative_piece_or_narrow {ω ζ d η a b L s ε h thin : ℝ}
    {n N K : ℕ} {x v : Fin n → V} {y w : Fin N → V} {Y : Fin n → Set V}
    (B : DensePrismInput ω d (d^η) a b L s x v y w Y)
    (hn : 0 < n) (hd : 0 < d) (hd1 : d ≤ 1/100) (hv : ∀ i, ‖v i‖ = 1)
    (hω : 0 < ω) (hβ : 0 < ω*ζ/100) (hβ1 : ω*ζ/100 ≤ 1)
    (hβω : ω*ζ/100 ≤ ω/1000)
    (hη : 0 < η) (hε : 0 < ε) (hηω : η ≤ ω/1000)
    (hηβω : η ≤ (ω*ζ/100)*ω/1000)
    (hηε : η ≤ ε/1000) (hηβε : η ≤ (ω*ζ/100)*ε/1000)
    (hthin : 0 ≤ thin) (hthinε : thin ≤ ε/100) (hh : h ≤ η/4)
    (hAmax : a ≤ 20000*d^(1-thin))
    (hsmall : (10:ℝ)^40*d^(η/2) ≤ 1)
    (hlog : (10:ℝ)^40*(1+Real.log (1/d))*d^(ε/2) ≤ 1)
    (hdK : d ≤ (1/2:ℝ)^K) (hK2 : (1/2:ℝ)^K < 2*d)
    (htK : d^η ≤ 1/(2*((K:ℝ)+1)))
    (hKT : ∀ W : Set V, Convex ℝ W →
      O (q n {i | T d (x i) (v i) ⊆ W}*d^2) ≤ O (d^(-h))*volume W) :
    B.Narrow (ω*ζ/100) (d^(1-ω/100)) (d^η) K ∨
    ∃ Q : PrismPiece n N (K+1),
      Q.Good ω ζ d ε (1000000*a) (10*L) s
        (fun k => packetWidth a L ((1/2:ℝ)^(k:ℕ))/(10*L)) x v y w ∧
      (∀ i, Q.piece i ⊆ Y i) ∧
      d^(1-ω/100) < packetWidth a L ((1/2:ℝ)^(Q.scale:ℕ))/(10*L) := by
  have hdle1 : d ≤ 1 := hd1.trans (by norm_num)
  have ha : 0 < a := hd.trans_le B.delta_le_thickness
  have hL : 0 < L := ha.trans_le (B.thickness_le_width.trans B.width_le_length)
  apply B.piece_or_narrow hn hd hd1 hv hβ hβ1 (Real.rpow_nonneg hd.le _)
    (Real.rpow_pos_of_pos hd _) (show 0 ≤ d^(3*η)*L*d^2 by positivity)
    hdK hK2 htK hKT
    (packet_lower_angle_budget hd hdle1 hω hβ.le hβω hη hηω hh hsmall)
    (packet_row_budget hd hdle1 hη hL.le hsmall)
    (fun k => packetWidth a L ((1/2:ℝ)^(k:ℕ))/(10*L)) (fun _ => rfl)
  intro k hlow hround
  have hθ : 0 < (1/2:ℝ)^(k:ℕ) := by positivity
  have hθ1 : (1/2:ℝ)^(k:ℕ) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨hdr, hr1, hcap⟩ := packet_partner_radius hd hdle1 hβ hη hηβω hlow.le hθ1 hsmall
  refine ⟨_, hdr, hr1, hcap,
    packet_cordoba_budget hd hdle1 hβ hη hε hthinε hηε hηβε ha.le hAmax hL.le hθ.le hlog, ?_⟩
  have hwidth := (packetWidth_bound hd B.delta_le_thickness hL hθ hθ1 hround).2.1
  have hratio : (packetWidth a L ((1/2:ℝ)^(k:ℕ))/(10*L))/((1/2:ℝ)^(k:ℕ)) ≤ 1000000*a/d := by
    apply (div_le_iff₀ hθ).mpr
    simpa only [mul_div_assoc] using hwidth
  have hratio0 : 0 ≤ (packetWidth a L ((1/2:ℝ)^(k:ℕ))/(10*L))/((1/2:ℝ)^(k:ℕ)) :=
    div_nonneg (hθ.le.trans (packetWidth_bound hd B.delta_le_thickness hL hθ hθ1 hround).1) hθ.le
  exact (show 8*((packetWidth a L ((1/2:ℝ)^(k:ℕ))/(10*L))/((1/2:ℝ)^(k:ℕ)))^(ω*ζ/100) ≤
      8*(1000000*a/d)^(ω*ζ/100) by
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hratio0 hratio hβ.le) (by norm_num)).trans
    (packet_broadness_budget hd hdle1 hη hε hβ hβ1 hthin hthinε hηε ha.le hAmax hsmall)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
