-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.Glue, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The glue from the per-sample stages to the per-sample producer (session x1088).

`sampleProducer_of_stages : StagesProducer → SampleProducer`: at a late sample of the front's
broad branch the stages give a root surviving family `E`; x1096's
`exists_dense_good_descendant_after_preparation` chooses a child `b` at level
`i + childOffset` whose events in `E` carry `κ⁻¹/64` of its full reference, with its active
ancestor `a` at level `i`; the child stage gives the cap, state, row and qualification clauses;
this file adds the scalar clauses (`Source.Numerics`), the pointwise clauses (x1082's
`Forward.relative_pointwise`) and the natural-unit format (`rA = r_i`, block of `a`, `cA = 0`,
`A_A = A_a`, `H₀ = H_(γ b)`, `RA = R_a`), and packs `RelRowCoreNat`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Stages
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Numerics
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalDescendantReferences
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentSignalFacts

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open MeasureTheory Filter Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

noncomputable section

/-- The broad residual lies in the prepared base. -/
theorem broadResidual_subset_base {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {m : ℕ} {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a₁ A : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a₁ A θ} {r fraction : ℝ} (R : BroadResidual F r fraction)
    (w : Fin (d.W k)) : R.residual w ⊆ Q.base w := by
  intro x hx
  obtain ⟨b, -, hbγ, -, hact, hU, -⟩ := R.witness w x hx
  have h1 := F.subset_coarse b hact hU
  have h2 : x ∈ Q.residual (p.γ b) := h1.1
  rw [hbγ] at h2
  exact Q.residual_subset w h2

/-- `RelativeRowPacket` from the clause groups stated at the child's own clock and block. -/
theorem relativeRowPacket_of_clauses_at (M Ep : ℕ) (precision loss Nk L d₁ gain κ : ℝ)
    (ν : Measure (ℕ × (Fin 6 → ℝ))) (B : ℝ) (TA jA : ℕ) (aA : ℝ) (RA : MvPolynomial (Fin 4) ℝ)
    (Tb jb T' j' : ℕ) (hT : TA + T' = Tb) (hj : jA * 2 ^ T' + j' = jb)
    (cb ub : EuclideanSpace ℝ (Fin 2)) (aB a' : ℝ) (Ab : Set (ℕ × (Fin 6 → ℝ)))
    (Fb H : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (K ε pv θ : ℝ) (Se Er bad : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (st : ((ℕ × (Fin 6 → ℝ)) × ℝ) → ℕ) (G : ℕ → Fin 3 → ℝ) (pal : Measure (Fin 2 → ℤ))
    (hsc : ScalarClauses Ep Nk L gain loss (O204.Split.δ Nk (precision * gain * L)) κ K ε pv θ a'
      ((2 : ℝ) ^ T')⁻¹)
    (hSe : Se ⊆ H ∩ Fb) (hEr : Se ⊆ Er)
    (hpt : PointClauses K aA B ((jA : ℝ) * ((2 : ℝ) ^ TA)⁻¹) ((2 : ℝ) ^ TA)⁻¹
      ((2 : ℝ) ^ Tb)⁻¹ jb RA (O204.Tangent.packetBase Tb jb cb ub) Ab Se)
    (href : 0 < ENNReal.ofReal ((2 : ℝ) ^ Tb)⁻¹ * ν Ab)
    (hmass : (ENNReal.ofReal ((2 : ℝ) ^ Tb)⁻¹ * ν Ab) / ENNReal.ofReal K ≤
      ((ν.prod volume).restrict Se) Set.univ)
    (hcap : CapClauses K ε d₁ ((2 : ℝ) ^ T')⁻¹ a' (ENNReal.ofReal ((2 : ℝ) ^ Tb)⁻¹ * ν Ab) ν
      (O204.Tangent.packetBase Tb jb cb ub) (fun z => O204.Tangent.packetSignal RA z / aB) Se)
    (hst : StateClauses K ε pv ν (O204.Tangent.packetBase Tb jb cb ub)
      (fun z => O204.Tangent.packetSignal RA z / aB) Se st pal)
    (hrow : RowClauses K θ aA ((2 : ℝ) ^ TA)⁻¹ RA (O204.Tangent.packetBase Tb jb cb ub) Se Er
      st G)
    (hq : QualClauses M K θ aA ((2 : ℝ) ^ TA)⁻¹ jb ((2 : ℝ) ^ Tb)⁻¹ ν Se Er bad st G) :
    O204.Tangent.RelativeRowPacket M Ep precision loss Nk L d₁ gain κ ν B TA jA aA RA T' j' cb ub
      aB a' Ab Fb H := by
  subst hT
  subst hj
  exact relativeRowPacket_of_clauses M Ep precision loss Nk L d₁ gain κ ν B TA jA aA RA T' j' cb
    ub aB a' Ab Fb H K ε pv θ Se Er bad st G pal hsc hSe hEr hpt href hmass hcap hst hrow hq

/-- The block of a descendant lies in the block of its ancestor, in integer form. -/
theorem block_nesting {ja jb Ta Tb : ℕ} (hT : Ta ≤ Tb)
    (h0 : (ja : ℝ) / (2 : ℝ) ^ Ta ≤ (jb : ℝ) / (2 : ℝ) ^ Tb)
    (h1 : ((jb : ℝ) + 1) / (2 : ℝ) ^ Tb ≤ ((ja : ℝ) + 1) / (2 : ℝ) ^ Ta) :
    ja * 2 ^ (Tb - Ta) ≤ jb ∧ jb < (ja + 1) * 2 ^ (Tb - Ta) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ) ^ n := fun n => by positivity
  have hsplit : (2 : ℝ) ^ Tb = (2 : ℝ) ^ Ta * (2 : ℝ) ^ (Tb - Ta) := by
    rw [← pow_add, Nat.add_sub_cancel' hT]
  constructor
  · have : (ja : ℝ) * (2 : ℝ) ^ (Tb - Ta) ≤ jb := by
      rw [div_le_div_iff₀ (hpos Ta) (hpos Tb), hsplit] at h0
      have := hpos Ta
      nlinarith
    exact_mod_cast this
  · have : (jb : ℝ) + 1 ≤ ((ja : ℝ) + 1) * (2 : ℝ) ^ (Tb - Ta) := by
      rw [div_le_div_iff₀ (hpos Tb) (hpos Ta), hsplit] at h1
      have := hpos Ta
      nlinarith
    have : ((jb + 1 : ℕ) : ℝ) ≤ (((ja + 1) * 2 ^ (Tb - Ta) : ℕ) : ℝ) := by push_cast; linarith
    have := (Nat.cast_le (α := ℝ)).mp this
    omega

/-- The constants of the pointwise clauses fit under `K = N^kexp` once `N^(kexp/4) ≥ 16`,
`κ ≤ N^(kexp/8)` and `K_d ≤ N^(kexp/4)`. -/
theorem constants_le_K {N kexp κ Kd : ℝ} (hN : 1 < N) (hk : 0 < kexp)
    (h16 : 16 ≤ N ^ (kexp / 4)) (hκ1 : 1 ≤ κ) (hκ : κ ≤ N ^ (kexp / 8)) (hKd0 : 0 ≤ Kd)
    (hKd : Kd ≤ N ^ (kexp / 4)) :
    2 ≤ N ^ kexp ∧ 2 * κ ≤ N ^ kexp ∧ 1 + 2 * (κ ^ 2 + (Kd + 2 * κ ^ 2)) ≤ N ^ kexp ∧
      2 * Kd ≤ N ^ kexp ∧ κ ≤ N ^ kexp := by
  have hNp : 0 < N := by linarith
  have hYX : (N ^ (kexp / 8)) ^ 2 = N ^ (kexp / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; congr 1; push_cast; ring
  have hX4 : N ^ kexp = (N ^ (kexp / 4)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; congr 1; push_cast; ring
  generalize N ^ (kexp / 4) = X at h16 hKd hYX hX4
  generalize N ^ (kexp / 8) = Y at hκ hYX
  rw [hX4]
  have hX1 : 1 ≤ X := by linarith
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX24 : X ^ 2 ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
  have hY4 : 4 ≤ Y := by nlinarith
  have h2Y : 2 * Y ≤ X := by nlinarith
  have hκ2 : κ ^ 2 ≤ X := by rw [← hYX]; nlinarith
  have h9 : 9 * X ≤ X ^ 2 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The child offset fits in the front window. -/
theorem childOffset_le_window {tune : Tuning} {κ₁ d₁ precision loss gain : ℝ} {Ep m C : ℕ}
    (hκ : 0 < κ₁)
    (hκ1 : κ₁ ≤ 1) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1) (hprec : 1 ≤ precision) (hg : 0 < gain) (hm : 0 < m)
    (hgm : 8 ≤ gain * m) (hC : windowOf tune κ₁ d₁ Ep precision loss gain * m ≤ C) :
    childOffset κ₁ Ep precision gain m ≤ C := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hP : 0 ≤ ((Ep : ℝ) + 1) * precision := by positivity
  have hco_hi : (childOffset κ₁ Ep precision gain m : ℝ) ≤
      2 * (((Ep : ℝ) + 1) * precision + 2) * gain * m / κ₁ + 2 := by
    unfold childOffset; push_cast
    have := (Nat.ceil_lt_add_one (show 0 ≤ 2 * (((Ep : ℝ) + 1) * precision + 2) * gain * m / κ₁
      by positivity)).le
    linarith
  have hd1' : 0 < 1 - d₁ := by linarith
  have hκd' : 0 < (1 - d₁) * κ₁ := by positivity
  have hW0 : 1024 * (((Ep : ℝ) + 1) * precision + 3) * gain / ((1 - d₁) * κ₁) ≤
      windowOf tune κ₁ d₁ Ep precision loss gain := by
    unfold windowOf
    apply div_le_div_of_nonneg_right _ hκd'.le
    have hD := tune.one_le_depth κ₁ d₁ Ep precision loss
    have h0 : 0 ≤ 1024 * (((Ep : ℝ) + 1) * precision + 3) * gain := by positivity
    calc 1024 * (((Ep : ℝ) + 1) * precision + 3) * gain
        = 1024 * (((Ep : ℝ) + 1) * precision + 3) * gain * 1 := by ring
      _ ≤ 1024 * (((Ep : ℝ) + 1) * precision + 3) * gain * tune.depth κ₁ d₁ Ep precision loss :=
          mul_le_mul_of_nonneg_left hD h0
  have hwin2 : 2 * (((Ep : ℝ) + 1) * precision + 2) * gain * m / κ₁ + 2 ≤
      1024 * (((Ep : ℝ) + 1) * precision + 3) * gain / ((1 - d₁) * κ₁) * m := by
    have hd1 : 0 < 1 - d₁ := by linarith
    have hκd : 0 < (1 - d₁) * κ₁ := by positivity
    have hκd1 : (1 - d₁) * κ₁ ≤ κ₁ := by nlinarith
    rw [div_mul_eq_mul_div, div_add' _ _ _ hκ.ne', div_le_div_iff₀ hκ hκd]
    have hA : 2 * (((Ep : ℝ) + 1) * precision + 2) * gain * m + 2 * κ₁ ≤
        4 * (((Ep : ℝ) + 1) * precision + 3) * gain * m := by
      have : κ₁ ≤ 4 * gain * m := by linarith
      nlinarith
    have h0 : 0 ≤ (((Ep : ℝ) + 1) * precision + 3) * gain * m := by positivity
    have hB : 4 * (((Ep : ℝ) + 1) * precision + 3) * gain * m * ((1 - d₁) * κ₁) ≤
        1024 * (((Ep : ℝ) + 1) * precision + 3) * gain * m * κ₁ := by nlinarith
    nlinarith
  have hW0m := mul_le_mul_of_nonneg_right hW0 hmR.le
  have : (childOffset κ₁ Ep precision gain m : ℝ) ≤ C := by linarith
  exact_mod_cast this

/-- The child offset is deep against `precision * gain` and the qualification budget. -/
theorem childOffset_lower {κ₁ precision gain : ℝ} {Ep m : ℕ} (hκ : 0 < κ₁) (hm : 0 < m) :
    2 * (((Ep : ℝ) + 1) * precision + 2) * gain / κ₁ ≤
      (childOffset κ₁ Ep precision gain m : ℝ) / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [le_div_iff₀ hmR]
  unfold childOffset; push_cast
  have := Nat.le_ceil (2 * (((Ep : ℝ) + 1) * precision + 2) * gain * m / κ₁)
  rw [div_mul_eq_mul_div]
  linarith

/-- The level arithmetic of the ancestor level (`sA`, `rA`, `TA`) and the child level. -/
theorem level_facts {κ₁ precision gain δ₀ L N rA rB sA sB K : ℝ} {Ep TA TB : ℕ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hprec : 1 ≤ precision) (hg : 0 < gain) (hδ0 : 0 < δ₀)
    (hδg : δ₀ ≤ gain / 100) (hL : 0 < L) (hN1 : 1 < N)
    (hsep0 : 2 * (((Ep : ℝ) + 1) * precision + 2) * gain ≤ κ₁ * (sB - sA))
    (hTA1 : N ^ ((κ₁ * sA - δ₀) * L) ≤ (2 : ℝ) ^ TA)
    (hTA2 : (2 : ℝ) ^ TA ≤ N ^ ((κ₁ * sA + δ₀) * L))
    (hTB1 : N ^ ((κ₁ * sB - δ₀) * L) ≤ (2 : ℝ) ^ TB)
    (hTB2 : (2 : ℝ) ^ TB ≤ N ^ ((κ₁ * sB + δ₀) * L))
    (hrA : |rA - sA * L| ≤ δ₀ * L) (hrB : |rB - sB * L| ≤ δ₀ * L)
    (hsB : sB ≤ 1 / 2) (hδ14 : δ₀ ≤ 1 / 4) (h4δ : 2 * N ^ (4 * δ₀ * L) ≤ K) :
    TA ≤ TB ∧ ((2 : ℝ) ^ (TB - TA))⁻¹ ≤ O204.Split.δ N (precision * gain * L) ∧
      O204.Split.δ N rB / O204.Split.δ N rA ≤ K * ((2 : ℝ) ^ (TB - TA))⁻¹ ∧
      rA ≤ rB ∧ rB + L / 4 ≤ L := by
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hX1 : (1 : ℝ) ≤ ((Ep : ℝ) + 1) * precision := by nlinarith
  have hsep1 : κ₁ * sA + δ₀ ≤ κ₁ * sB - δ₀ := by nlinarith
  have hsep2 : precision * gain + 2 * δ₀ ≤ κ₁ * (sB - sA) := by nlinarith
  have hsab : sA ≤ sB := by
    by_contra hcon
    push_neg at hcon
    have : κ₁ * (sB - sA) < 0 := mul_neg_of_pos_of_neg hκ (by linarith)
    nlinarith
  have hTab : TA ≤ TB := clock_mono hN1 hL.le hTA2 hTB1 hsep1
  have hrA' : rA ≤ (sA + δ₀) * L := by have := (abs_le.mp hrA).2; linarith
  have hrB' : (sB - δ₀) * L ≤ rB := by have := (abs_le.mp hrB).1; linarith
  have hrB'' : rB ≤ (sB + δ₀) * L := by have := (abs_le.mp hrB).2; linarith
  have hsep3 : 2 * δ₀ ≤ sB - sA := by
    have : κ₁ * (sB - sA) ≤ sB - sA := by nlinarith
    nlinarith
  refine ⟨hTab, rel_clock_le_zeta hN1 hL.le hTab hTA2 hTB1 hsep2,
    rel_thickness_le hN1 hL.le hκ1 hTab hrA' hrB' hsab hTA1 hTB2 h4δ, by nlinarith, by nlinarith⟩

/-- `2 N^(4 δ₀ L) ≤ N^kexp` for `δ₀ ≤ loss gain/(10^4 (Ep+1))` and `N^(kexp/4) ≥ 16`. -/
theorem two_rpow_le_K {N L loss gain δ₀ : ℝ} {Ep : ℕ} (hN1 : 1 < N) (hL : 0 < L)
    (hδ0 : 0 ≤ δ₀) (hloss : 0 < loss) (hg : 0 < gain)
    (htol : δ₀ ≤ loss * gain / (10000 * ((Ep : ℝ) + 1)))
    (h16 : 16 ≤ N ^ (loss * gain * L / ((Ep : ℝ) + 1) / 4)) :
    2 * N ^ (4 * δ₀ * L) ≤ N ^ (loss * gain * L / ((Ep : ℝ) + 1)) := by
  have hNp : 0 < N := by linarith
  have hE0 : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
  have hexp : 4 * δ₀ * L + loss * gain * L / ((Ep : ℝ) + 1) / 4 ≤
      loss * gain * L / ((Ep : ℝ) + 1) := by
    have h1 : 4 * δ₀ * L ≤ 4 * (loss * gain / (10000 * ((Ep : ℝ) + 1))) * L := by gcongr
    have h2 : 4 * (loss * gain / (10000 * ((Ep : ℝ) + 1))) * L =
        (loss * gain * L / ((Ep : ℝ) + 1)) / 2500 := by field_simp; ring
    have h3 : 0 < loss * gain * L / ((Ep : ℝ) + 1) := by positivity
    linarith
  calc 2 * N ^ (4 * δ₀ * L) ≤ N ^ (loss * gain * L / ((Ep : ℝ) + 1) / 4) * N ^ (4 * δ₀ * L) := by
        gcongr; linarith
    _ = N ^ (4 * δ₀ * L + loss * gain * L / ((Ep : ℝ) + 1) / 4) := by
        rw [← Real.rpow_add hNp]; ring_nf
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1.le hexp

/-- **The glue.** The per-sample stages give the per-sample producer. -/
theorem sampleProducer_of_stages (tune : Tuning) (hSt : StagesProducer tune) :
    SampleProducer tune := by
  intro hmk d₁ κ₁ ρ Ep precision loss e0 hd₁ hd₁1 hκ₁ hκ₁1 hρ hdρ hprec hloss hloss1 he0
    m s δ₀ C target indices hgrid hδtol hδm hm8 hgm htarget hstarget hm2 hC1 hCge hCle hCt hind
    d hd hprof Mp Dp budget hbud hbud1
  obtain ⟨σS, hσS, hevS⟩ := hSt hmk d₁ κ₁ ρ Ep precision loss e0 hd₁ hd₁1 hκ₁ hκ₁1 hρ hdρ hprec
    hloss hloss1 he0 m s δ₀ C target indices hgrid hδtol hδm hm8 hgm htarget hstarget hm2 hC1 hCge
    hCle hCt hind d hd hprof Mp Dp budget hbud hbud1
  have hL : 0 < d.L := hd.2.2.2.1
  have hg : 0 < gainOf tune κ₁ d₁ Ep precision loss e0 := gainOf_pos hκ₁ hd₁1 hprec hloss he0
  have hkexp0 : 0 < loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1) := by
    have : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
    positivity
  have hNt : Tendsto d.N atTop atTop := hd.2.1
  have hev1 : ∀ᶠ k in atTop, (16 : ℝ) ≤
      d.N k ^ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1) / 4) :=
    ((tendsto_rpow_atTop (by positivity)).comp hNt).eventually_ge_atTop 16
  have hev2 : ∀ᶠ k in atTop, d.K k ≤
      d.N k ^ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1) / 4) :=
    hd.2.2.1.2 _ (by positivity)
  refine ⟨min σS (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1) / 8),
    lt_min hσS (by positivity), ?_⟩
  filter_upwards [hevS, hev1, hev2] with k hkS hk16 hkKd
  intro p hp H hHm hHsub hmass Qp hpure hbuf i hi Fp Rp hRmass hgood
  have hN2 : 2 ≤ d.N k := hd.1 k
  have hN1 : 1 < d.N k := by linarith
  have hpS := PathTolerance.mono hp hN1.le (min_le_left _ _)
  have hκN := hp.2.1.trans (Real.rpow_le_rpow_of_exponent_le hN1.le (min_le_right σS
    (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1) / 8)))
  have hκ1 : 1 ≤ p.κ := hp.1
  have hKd0 : 0 ≤ d.K k := le_trans zero_le_one (hd.2.2.1.1 k)
  obtain ⟨hK2, h2κK, hbaseK, hvK, hκK⟩ := constants_le_K hN1 hkexp0 hk16 hκ1
    (by simpa only [div_div] using hκN) hKd0 hkKd
  obtain ⟨density, E, hdens, hE, hEmass, hchild⟩ :=
    hkS p hpS H hHm hHsub hmass Qp hpure hbuf i hi Fp Rp hRmass hgood
  -- the child level
  have hiC : i + C ≤ target := by
    rw [hind, Finset.mem_range] at hi; omega
  have hgm' : 8 ≤ gainOf tune κ₁ d₁ Ep precision loss e0 * m := by
    have hfg := gridFineOf_le_gain tune (κ₁ := κ₁) (d₁ := d₁) (Ep := Ep) (precision := precision)
      hloss hloss1 hg
    have hmR0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact hgm.trans (mul_le_mul_of_nonneg_right hfg hmR0)
  have hcoC := childOffset_le_window (Ep := Ep) hκ₁ hκ₁1 hd₁ hd₁1 hprec hg (by omega) hgm' hCge
  have hib : i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m ≤ m - 1 := by
    omega
  obtain ⟨b, hblev, hω, hA0, hfloor, hal, hag, haF, haA, hact, -⟩ :=
    Forward.exists_dense_good_descendant_after_preparation hd hpS Fp Rp hHsub E hE
      density hdens hEmass
      (i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m) (by omega) hib
  have hsub : i + childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m - i =
      childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m := by omega
  rw [hsub] at hal hag haF haA hact
  have hfloor' : ENNReal.ofReal density *
      (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) ≤
      ((d.ν k (p.γ b)).prod volume) (E (p.γ b) ∩ p.F b) := by rw [hblev]; exact hfloor
  obtain ⟨Se, Er, bad, st, G, pal, hSeE, hSeEr, hmassSe, hcap, hstc, hrow, hqual⟩ :=
    hchild b hblev hact hA0 hfloor'
  -- the grid and the path at the two levels
  obtain ⟨-, -, hg18, hδ0, -, -, -, hs, -, hδg, -, -, -, -⟩ := hgrid
  have hi_m : i < m := by omega
  have hb_m : p.lev b < m := by omega
  obtain ⟨hri, hri0, hTi1, hTi2, -⟩ := hpS.2.2.2.2.1 i hi_m
  obtain ⟨hrb, hrb0, hTb1, hTb2, -⟩ := hpS.2.2.2.2.1 (p.lev b) hb_m
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hco_low := childOffset_lower (Ep := Ep) (precision := precision)
    (gain := gainOf tune κ₁ d₁ Ep precision loss e0) hκ₁ hmpos
  have hsd : s (p.lev b) - s i =
      (childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m : ℝ) / m := by
    rw [hs, hs, hblev]; push_cast; ring
  have hsep0 : 2 * (((Ep : ℝ) + 1) * precision + 2) * gainOf tune κ₁ d₁ Ep precision loss e0 ≤
      κ₁ * (s (p.lev b) - s i) := by
    rw [hsd]
    have := mul_le_mul_of_nonneg_left hco_low hκ₁.le
    rwa [mul_div_cancel₀ _ hκ₁.ne'] at this
  have hsb : s (p.lev b) ≤ 1 / 2 := by
    rw [← hstarget, hs, hs]
    apply div_le_div_of_nonneg_right _ hmR.le
    have : p.lev b ≤ target := by omega
    exact_mod_cast (by omega : p.lev b + 1 ≤ target + 1)
  have hδ14 : δ₀ ≤ 1 / 4 := by linarith only [hδg, hg18]
  have h4δ := two_rpow_le_K (Ep := Ep) hN1 hL hδ0.le hloss hg
    (hδtol.trans (tolOf_le tune κ₁ d₁ Ep hloss hg)) hk16
  obtain ⟨hTab, hhζ, haK, hr_le, hr_room⟩ := level_facts hκ₁ hκ₁1 hprec hg hδ0 hδg hL hN1 hsep0
    hTi1 hTi2 hTb1 hTb2 hri hrb hsb hδ14 h4δ
  -- the ancestor's block contains the child's block
  have hfc := hpS.iterate_par_fullCylinder
    (childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m) b (by omega)
  obtain ⟨l, hl⟩ := nonempty_of_measure_ne_zero hA0
  have hpos2 : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ) ^ n := fun n => by positivity
  have hleft : ((l, (p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b)) : (ℕ × (Fin 6 → ℝ)) × ℝ) ∈
      p.fullCylinder b :=
    ⟨hl, le_rfl, by apply div_le_div_of_nonneg_right _ (hpos2 _).le; linarith⟩
  have hright : ((l, ((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) : (ℕ × (Fin 6 → ℝ)) × ℝ) ∈
      p.fullCylinder b :=
    ⟨hl, by apply div_le_div_of_nonneg_right _ (hpos2 _).le; linarith, le_rfl⟩
  have hL0 := (hfc hleft).2.1
  have hR0 := (hfc hright).2.2
  rw [hal] at hL0 hR0
  obtain ⟨hjle, hjlt⟩ := block_nesting hTab hL0 hR0
  -- the chart of the ancestor
  obtain ⟨-, -, -, -, -, -, hRdeg, hRcoeff, hAm, -⟩ := hpS.2.2.2.2.2.2.2
    (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b)
  -- the scalar clauses
  have hζ0 := O204.Tangent.δ_pos (d.N k) (precision * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L)
  have hprec0 : (0 : ℝ) ≤ precision := le_trans zero_le_one hprec
  have hpgl : 0 ≤ precision * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L := by positivity
  have hζ1 := O204.Tangent.δ_le_one (d.N k) (precision * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L)
    hN1.le hpgl
  have ha'0 : 0 < O204.Split.δ (d.N k) (p.r (p.lev b)) / O204.Split.δ (d.N k) (p.r i) :=
    div_pos (O204.Tangent.δ_pos _ _) (O204.Tangent.δ_pos _ _)
  have hh'0 : 0 < ((2 : ℝ) ^ (p.T (p.lev b) - p.T i))⁻¹ := by positivity
  have hKEp : (d.N k ^ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1))) ^ Ep ≤
      d.N k ^ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith only [hN1])]
    apply Real.rpow_le_rpow_of_exponent_le hN1.le
    have hE0 : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
    have hlg : 0 ≤ loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hE0]
    nlinarith only [hlg, hE0]
  have hsc := scalarClauses_of (Ep := Ep) (Nk := d.N k) (L := d.L)
    (gain := gainOf tune κ₁ d₁ Ep precision loss e0) (loss := loss) (κ := 2 * p.κ) ha'0 hh'0 haK hhζ
    hζ0 hζ1 hK2 h2κK hKEp
  -- the pointwise clauses
  have hB0 : 0 < d.B k (p.γ b) := (hd.parent_signal_data k (p.γ b)).1
  have hpt : PointClauses (d.N k ^ (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * d.L / ((Ep : ℝ) + 1)))
      (O204.Split.δ (d.N k) (p.r i)) (d.B k (p.γ b))
      ((p.j (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b) : ℝ) *
        ((2 : ℝ) ^ p.T i)⁻¹) ((2 : ℝ) ^ p.T i)⁻¹ ((2 : ℝ) ^ p.T (p.lev b))⁻¹ (p.j b)
      (p.R (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b))
      (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b)) (p.A b) Se := by
    intro z hz
    have hzE : z ∈ E (p.γ b) := (hSeE hz).1
    have hzF : z ∈ p.F b := (hSeE hz).2
    have hzbase : z ∈ Qp.base (p.γ b) := broadResidual_subset_base Rp _ (hE _ hzE)
    obtain ⟨hA, hTb, hTa, hbase, hv, hjets, hfl⟩ :=
      Forward.relative_pointwise hd hpS Qp _ b hag haF haA hzF hzbase
    rw [hal] at hTa hjets
    have hδpos := O204.Tangent.δ_pos (d.N k) (p.r i)
    refine ⟨⟨hA, hTb, hTa⟩, hbase.trans hbaseK, hv.trans hvK, fun t ht => ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hjets t ht
      refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_⟩
      · exact mul_le_mul_of_nonneg_right hκK hδpos.le
      · exact mul_le_mul_of_nonneg_right hκK hB0.le
      · rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hκK (by positivity)
    · exact le_trans (div_le_div_of_nonneg_left hB0.le (by linarith only [hκ1]) hκK) hfl
  have hSeHF : Se ⊆ H (p.γ b) ∩ p.F b := fun z hz =>
    ⟨Rp.subset_H _ (hE _ (hSeE hz).1), (hSeE hz).2⟩
  have href : 0 < ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b) :=
    ENNReal.mul_pos (by simp) hA0
  refine ⟨b, p.r i, p.j (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b),
    p.T i, 0, p.A (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b),
    H (p.γ b), p.R (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b),
    hri0.le, hr_le, hr_room, hTab, hjle, hjlt, hAm, haA, fun h0 => hA0 (measure_mono_null haA h0),
    hHm _, subset_rfl, hRdeg,
    fun e => (hRcoeff e).trans (pow_le_pow_right₀ hN1.le (Nat.le_succ Mp)),
    by rw [norm_zero]; positivity, ?_⟩
  exact relativeRowPacket_of_clauses_at (qualDegree κ₁) Ep precision loss (d.N k) d.L d₁
    (gainOf tune κ₁ d₁ Ep precision loss e0) (2 * p.κ) (d.ν k (p.γ b)) (d.B k (p.γ b)) (p.T i)
    (p.j (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b))
    (O204.Split.δ (d.N k) (p.r i))
    (p.R (p.par^[childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m] b))
    (p.T (p.lev b)) (p.j b) _ _ (Nat.add_sub_cancel' hTab) (Nat.add_sub_cancel' hjle) (p.c b)
    (p.u b) (O204.Split.δ (d.N k) (p.r (p.lev b)))
    (O204.Split.δ (d.N k) (p.r (p.lev b)) / O204.Split.δ (d.N k) (p.r i)) (p.A b) (p.F b)
    (H (p.γ b)) _ _ _ _ Se Er bad st G pal hsc hSeHF hSeEr hpt href hmassSe hcap hstc hrow hqual

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
