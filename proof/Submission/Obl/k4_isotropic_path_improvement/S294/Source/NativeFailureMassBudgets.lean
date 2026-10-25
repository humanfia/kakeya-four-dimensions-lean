-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeFailureMassBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootCosts
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ResidualSelectionBudget

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.Qualification
open scoped ENNReal BigOperators

noncomputable section

private theorem entry_count_base_bound {X H C K : ℝ}
    (hX : (10:ℝ)^100 ≤ X) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hC : 0 ≤ C) (hCX : C ≤ X) (hK : 0 ≤ K) (hKX : K ≤ X^8) :
    ((⌈256*(12*H+4)^7*(C*K/(X^4)⁻¹)⌉₊*256:ℕ):ℝ) ≤ X^24 := by
  have hX1 : 1 ≤ X := by linarith only [hX]
  have hX0 : 0 ≤ X := zero_le_one.trans hX1
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hfour : 12*H+4 ≤ 16*X := by linarith only [hHX,hX1]
  have hratio : C*K/(X^4)⁻¹ ≤ X^13 := by
    calc
      _ = C*K*X^4 := by rw [div_inv_eq_mul]
      _ ≤ X*X^8*X^4 := by gcongr
      _ = _ := by ring
  have hraw : 256*(12*H+4)^7*(C*K/(X^4)⁻¹) ≤ (256*16^7:ℝ)*X^20 := by
    calc
      _ ≤ 256*(16*X)^7*X^13 := by gcongr
      _ = _ := by ring
  have hraw0 : 0 ≤ 256*(12*H+4)^7*(C*K/(X^4)⁻¹) := by positivity
  have hceil := (Nat.ceil_lt_add_one hraw0).le
  have hX20 : 1 ≤ X^20 := one_le_pow₀ hX1
  have hCbig : (256*(256*16^7+1):ℝ) ≤ X^4 := by
    have hc : (256*(256*16^7+1):ℝ) ≤ X := by norm_num at hX ⊢; linarith only [hX]
    have hp : X ≤ X^4 := by
      calc
        X = X*1 := by ring
        _ ≤ X*X^3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hX1) hX0
        _ = _ := by ring
    exact hc.trans hp
  push_cast
  calc
    _ ≤ ((256*16^7:ℝ)*X^20+1)*256 := by nlinarith only [hceil,hraw]
    _ ≤ (256*(256*16^7+1):ℝ)*X^20 := by nlinarith only [hX20]
    _ ≤ X^4*X^20 := mul_le_mul_of_nonneg_right hCbig (by positivity)
    _ = _ := by ring

private theorem residual_complexity_base_bound {X C K Krow Cstate : ℝ}
    (hX : (10:ℝ)^100 ≤ X)
    (hC : 0 ≤ C) (hCX : C ≤ X) (hK : 0 ≤ K) (hKX : K ≤ X^8)
    (hrow : 0 ≤ Krow) (hrowX : Krow ≤ X^2)
    (hstate : 0 ≤ Cstate) (hstateX : Cstate ≤ X) :
    0 ≤ 3*((C*K/(X^4)⁻¹)*(22*Krow^2+5))*(Cstate/(X^32)⁻¹) ∧
      3*((C*K/(X^4)⁻¹)*(22*Krow^2+5))*(Cstate/(X^32)⁻¹) ≤ X^52 := by
  have hX1 : 1 ≤ X := by linarith only [hX]
  have hX0 : 0 ≤ X := zero_le_one.trans hX1
  have hratio : C*K/(X^4)⁻¹ ≤ X^13 := by
    calc
      _ = C*K*X^4 := by rw [div_inv_eq_mul]
      _ ≤ X*X^8*X^4 := by gcongr
      _ = _ := by ring
  have hrow2 : Krow^2 ≤ X^4 := by
    calc
      _ ≤ (X^2)^2 := pow_le_pow_left₀ hrow hrowX 2
      _ = _ := by ring
  have hrow4 : 22*Krow^2+5 ≤ 27*X^4 := by
    have hh : 1 ≤ X^4 := one_le_pow₀ hX1
    linarith only [hrow2,hh]
  have hstateRatio : Cstate/(X^32)⁻¹ ≤ X^33 := by
    calc
      _ = Cstate*X^32 := by rw [div_inv_eq_mul]
      _ ≤ X*X^32 := mul_le_mul_of_nonneg_right hstateX (by positivity)
      _ = _ := by ring
  have hconstant : (81:ℝ) ≤ X^2 := by
    have h9 : (9:ℝ) ≤ X := by linarith only [hX]
    nlinarith only [sq_nonneg (X-9),h9]
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ 3*(X^13*(27*X^4))*X^33 := by gcongr
    _ = 81*X^50 := by ring
    _ ≤ X^2*X^50 := mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = _ := by ring

private theorem rpow_natural_power {N e : ℝ} (hN : 0 < N) (n : ℕ) :
    (N^e)^n=N^((n:ℝ)*e) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
  congr 1
  ring

private theorem rpow_negative_natural_power {N e : ℝ} (hN : 0 < N) (n : ℕ) :
    N^(-(n:ℝ)*e)=((N^e)^n)⁻¹ := by
  rw [rpow_natural_power hN,←Real.rpow_neg hN.le]
  congr 1
  ring

private theorem visit_mass_bound {N e C : ℝ} {count : ENNReal}
    (hN : 0 < N) (_hC : 0 ≤ C) (hCX : C ≤ N^e)
    (hcount : count ≤ ENNReal.ofReal (N^e)) :
    count*ENNReal.ofReal (N^(-4*e)*C) ≤ ENNReal.ofReal (N^(-2*e)) := by
  calc
    _ ≤ ENNReal.ofReal (N^e)*ENNReal.ofReal (N^(-4*e)*C) :=
      mul_le_mul' hcount le_rfl
    _ = ENNReal.ofReal (N^e*(N^(-4*e)*C)) :=
      (ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _)).symm
    _ ≤ ENNReal.ofReal (N^e*(N^(-4*e)*N^e)) := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
    _ = _ := by
      congr 1
      rw [←mul_assoc,←Real.rpow_add hN,←Real.rpow_add hN]
      congr 1
      ring

/-- All native failure charges fit a common original-reference
allowance. This is uniform in the actual source, prior, row and root;
only the scalar choices of root preparation occur in the hypotheses. -/
theorem native_failure_mass_bound
    (s : Parent.Qualification.PhysicalModel.OriginalRootScales) {e : ℝ}
    (hN : 1 ≤ s.incidence.N) (he : 0 < e)
    (hlarge : (10:ℝ)^100 ≤ s.incidence.N^e)
    (hH : s.H ≤ s.incidence.N^e)
    (hcanonical : s.canonicalConstant ≤ s.incidence.N^e)
    (hstate : s.incidence.Cstate ≤ s.incidence.N^e)
    (hrow : s.Krow ≤ s.incidence.N^(2*e))
    (hcap : s.Kcap ≤ s.incidence.N^(8*e))
    (hentry0 : s.incidence.entryCut0=s.incidence.N^(-4*e))
    (hentry : ∀ i < s.incidence.L, s.incidence.entryCut i=s.incidence.N^(-4*e))
    (hcut : ∀ i < s.incidence.L, s.incidence.cut i=s.incidence.N^(-32*e))
    (hnative : s.incidence.nativeCut=s.incidence.N^(-4*e))
    (hlength : ((s.incidence.L+1:ℕ):ℝ) ≤ s.incidence.N^e)
    (hlevels : ((Jets2.parameterLevel s.zeta+1:ℕ):ℝ) ≤ s.incidence.N^e)
    (hgap : (200*(s.incidence.L:ℝ)+100)*e ≤ s.incidence.ch*s.incidence.alpha) :
    s.nativeFailureBound ≤ ENNReal.ofReal (s.incidence.N^(-e)) := by
  let N := s.incidence.N
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hX1 : 1 ≤ N^e := Real.one_le_rpow hN he.le
  have hC : 0 ≤ s.canonicalConstant := by
    unfold Parent.Qualification.PhysicalModel.OriginalRootScales.canonicalConstant
    have hh := s.hCpure
    have hh' := s.hH
    positivity
  have hK : 0 ≤ s.Kcap := s.hKcap.le
  have hrow0 : 0 ≤ s.Krow := (zero_le_one.trans s.hB).trans s.hBKrow
  have hKX : s.Kcap ≤ (N^e)^8 := by rw [rpow_natural_power hNp]; exact hcap
  have hrowX : s.Krow ≤ (N^e)^2 := by rw [rpow_natural_power hNp]; exact hrow
  have h4 : s.incidence.N^(-4*e)=((N^e)^4)⁻¹ := by
    simpa only [N,Nat.cast_ofNat] using rpow_negative_natural_power (e := e) hNp 4
  have h32 : s.incidence.N^(-32*e)=((N^e)^32)⁻¹ := by
    simpa only [N,Nat.cast_ofNat] using rpow_negative_natural_power (e := e) hNp 32
  let count : ℕ := ⌈256*(12*s.H+4)^7*(s.canonicalConstant*s.Kcap/s.incidence.entryCut0)⌉₊*256
  have hcount : (count:ℝ) ≤ N^(24*e) := by
    dsimp only [count]
    rw [hentry0,h4]
    have hh := entry_count_base_bound (X := N^e) hlarge (zero_le_one.trans s.hH) hH hC hcanonical hK hKX
    have hp24 : (N^e)^24=N^(24*e) := by
      simpa only [Nat.cast_ofNat] using rpow_natural_power (e := e) hNp 24
    exact hh.trans_eq hp24
  have hcountE : (count:ENNReal) ≤ ENNReal.ofReal (N^(24*e)) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcount
  let complexity := fun i : ℕ =>
    3*((s.canonicalConstant*s.Kcap/s.incidence.entryCut i)*(22*s.Krow^2+5))*
      (s.incidence.Cstate/s.incidence.cut i)
  have hcomplexity : ∀ i < s.incidence.L,
      0 ≤ complexity i ∧ complexity i ≤ N^(52*e) := by
    intro i hi
    dsimp only [complexity]
    rw [hentry i hi,hcut i hi,h4,h32]
    have hh := residual_complexity_base_bound (X := N^e) hlarge hC hcanonical hK hKX
      hrow0 hrowX s.incidence.hCstate hstate
    have hp52 : (N^e)^52=N^(52*e) := by
      simpa only [Nat.cast_ofNat] using rpow_natural_power (e := e) hNp 52
    exact ⟨hh.1,hh.2.trans_eq hp52⟩
  have hlarge52 : (1024:ℝ) ≤ N^(52*e) := by
    calc
      _ ≤ N^e := by norm_num at hlarge ⊢; linarith only [hlarge]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith only [he])
  have hresidual : s.residualSelectionFactor*
      ENNReal.ofReal (2*N^(-(s.incidence.ch*s.incidence.alpha))) ≤
        ENNReal.ofReal (N^(-2*e)) := by
    have hgap' : 2*(52*e)*(s.incidence.L:ℝ)+2*e ≤ s.incidence.ch*s.incidence.alpha := by
      have hh : 0 ≤ (s.incidence.L:ℝ)*e := mul_nonneg (Nat.cast_nonneg _) he.le
      nlinarith only [hgap,hh,he]
    have htwo : 2 ≤ N^(s.incidence.ch*s.incidence.alpha-2*(52*e)*(s.incidence.L:ℝ)-2*e) := by
      calc
        _ ≤ N^e := by norm_num at hlarge ⊢; linarith only [hlarge]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by
          have hh : 0 ≤ (s.incidence.L:ℝ)*e := mul_nonneg (Nat.cast_nonneg _) he.le
          nlinarith only [hgap,hh,he])
    have hh := Jets2.residual_selection_native_error_le (native := s.incidence.ch*s.incidence.alpha)
      (target := 2*e) hN s.incidence.L complexity hlarge52 hcomplexity hgap' htwo
    simpa only [Parent.Qualification.PhysicalModel.OriginalRootScales.residualSelectionFactor,
      complexity,neg_mul] using hh
  have hlengthE : ((s.incidence.L+1:ℕ):ENNReal) ≤ ENNReal.ofReal (N^e) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hlength
  have hlengthR : (s.incidence.L:ℝ) ≤ N^e := by
    have hh := hlength
    push_cast at hh
    linarith only [hh]
  have hlengthE' : (s.incidence.L:ENNReal) ≤ ENNReal.ofReal (N^e) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hlengthR
  have hlevelsE : ((Jets2.parameterLevel s.zeta+1:ℕ):ENNReal) ≤ ENNReal.ofReal (N^e) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hlevels
  have hvisit0 : 0 ≤ Jets2.zoomBlockVisitConstant := by
    unfold Jets2.zoomBlockVisitConstant
    positivity
  have hvisit : Jets2.zoomBlockVisitConstant ≤ N^e := by
    unfold Jets2.zoomBlockVisitConstant
    norm_num at hlarge ⊢
    linarith only [hlarge]
  have hspatial : ((Jets2.parameterLevel s.zeta+1:ℕ):ENNReal)*
      ENNReal.ofReal (s.incidence.nativeCut*Jets2.zoomBlockVisitConstant) ≤
        ENNReal.ofReal (N^(-2*e)) := by
    rw [hnative]
    exact visit_mass_bound hNp hvisit0 hvisit hlevelsE
  have hfiber : (∑ i : Fin s.incidence.L,
      ENNReal.ofReal (s.incidence.cut i.val)*(count:ENNReal)) ≤
        ENNReal.ofReal (N^(-7*e)) := by
    have hsingle : ENNReal.ofReal (N^(-32*e))*(count:ENNReal) ≤
        ENNReal.ofReal (N^(-8*e)) := by
      calc
        _ ≤ ENNReal.ofReal (N^(-32*e))*ENNReal.ofReal (N^(24*e)) :=
          mul_le_mul' le_rfl hcountE
        _ = _ := by
          rw [←ENNReal.ofReal_mul (Real.rpow_nonneg hNp.le _)]
          congr 1
          rw [←Real.rpow_add hNp]
          congr 1
          ring
    calc
      _ ≤ ∑ _i : Fin s.incidence.L, ENNReal.ofReal (N^(-8*e)) := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [hcut i.val i.isLt]
        exact hsingle
      _ = (s.incidence.L:ENNReal)*ENNReal.ofReal (N^(-8*e)) := by simp
      _ ≤ ENNReal.ofReal (N^e)*ENNReal.ofReal (N^(-8*e)) :=
        mul_le_mul' hlengthE' le_rfl
      _ = _ := by
        rw [←ENNReal.ofReal_mul (Real.rpow_nonneg hNp.le _)]
        congr 1
        rw [←Real.rpow_add hNp]
        congr 1
        ring
  have hentryVisit : ENNReal.ofReal (s.incidence.entryCut0*Jets2.zoomBlockVisitConstant)+
      (∑ i : Fin s.incidence.L,
        ENNReal.ofReal (s.incidence.entryCut i.val*Jets2.zoomBlockVisitConstant)) ≤
          ENNReal.ofReal (N^(-2*e)) := by
    calc
      _ = ENNReal.ofReal (N^(-4*e)*Jets2.zoomBlockVisitConstant)+
          (s.incidence.L:ENNReal)*ENNReal.ofReal (N^(-4*e)*Jets2.zoomBlockVisitConstant) := by
        rw [hentry0]
        congr 1
        calc
          _ = ∑ _i : Fin s.incidence.L,
              ENNReal.ofReal (N^(-4*e)*Jets2.zoomBlockVisitConstant) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hentry i.val i.isLt]
          _ = _ := by simp
      _ = ((s.incidence.L+1:ℕ):ENNReal)*
          ENNReal.ofReal (N^(-4*e)*Jets2.zoomBlockVisitConstant) := by push_cast; ring
      _ ≤ _ := visit_mass_bound hNp hvisit0 hvisit hlengthE
  have hentryLoss : s.residualEntryLoss ≤
      ENNReal.ofReal (N^(-7*e))+ENNReal.ofReal (N^(-2*e)) := add_le_add hfiber hentryVisit
  unfold Parent.Qualification.PhysicalModel.OriginalRootScales.nativeFailureBound
  calc
    _ ≤ ENNReal.ofReal (N^(-2*e))+ENNReal.ofReal (N^(-2*e))+
        (ENNReal.ofReal (N^(-7*e))+ENNReal.ofReal (N^(-2*e))) :=
      add_le_add (add_le_add hspatial hresidual) hentryLoss
    _ = ENNReal.ofReal (N^(-2*e)+N^(-2*e)+(N^(-7*e)+N^(-2*e))) := by
      repeat rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h7 : N^(-7*e) ≤ N^(-2*e) :=
        Real.rpow_le_rpow_of_exponent_le hN (by linarith only [he])
      calc
        _ ≤ 4*N^(-2*e) := by linarith only [h7]
        _ ≤ N^e*N^(-2*e) := mul_le_mul_of_nonneg_right
          (by norm_num at hlarge ⊢; linarith only [hlarge] : (4:ℝ) ≤ N^e)
          (Real.rpow_nonneg hNp.le _)
        _ = _ := by rw [←Real.rpow_add hNp]; congr 1; ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
