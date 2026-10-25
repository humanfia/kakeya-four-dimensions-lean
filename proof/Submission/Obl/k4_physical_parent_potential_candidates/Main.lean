import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.CoefficientReturn
import Submission.Obl.k4_physical_parent_potential_candidates.Statement

/-!
# o288 from the palette-free restoration

`completion_of_restoration` proves the readable form `CompletionAssertion` of the frozen
statement from `RestorationAssertion`. The choices: `precision = 2`; after `J`, a loss
`ρ / (4 (517 + 2E + q + P))` absorbing every polynomial power of the source constant `K`;
`ag = gain` and the group width `w = N^(-(1-ρ) gain L) / (4 C0 K^E)`; the output format
`Mc = Ecoef (⌈L⌉ + 3⌈gain L⌉ + Mp + Mr + 4) + 1`; and a cutoff making `N^(ρ gain L / 4)` dominate
all fixed constants. The heavy one-branch group is x1038's
`PhysicalSource.exists_physical_heavy_group`; the exit is `direct_of_quadratic_test`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MeasureTheory Set MvPolynomial PhysicalPotentialData

noncomputable section

set_option maxHeartbeats 4000000 in
/-- **o288 from the restoration.** -/
theorem completion_of_restoration (hR : RestorationAssertion) : CompletionAssertion := by
  intro hmk q hq cc hcc d₁ ρ hd₁ hd₁1 hρ hd₁ρ
  obtain ⟨Cmk, hCmk, hMK⟩ := hmk 3 (by norm_num) (by norm_num)
  have hCden : (1:ℝ) ≤ 1 + 2 * physicalMassLoss Cmk := by
    have := physicalMassLoss_pos hCmk; linarith
  obtain ⟨P, E, Ecoef, C0, hC0, hrest⟩ := hR (1 + 2 * physicalMassLoss Cmk) hCden q hq
  have hρ1 : ρ < 1 := by linarith
  refine ⟨2, by norm_num, ?_⟩
  intro D hD J hJ hjet
  -- the loss
  obtain ⟨Ltot, hLtot⟩ : ∃ Ltot : ℝ, Ltot = 517 + 2 * (E : ℝ) + (q : ℝ) + (P : ℝ) := ⟨_, rfl⟩
  have hLtot1 : 1 ≤ Ltot := by
    have := (Nat.cast_nonneg (α := ℝ) E); have := (Nat.cast_nonneg (α := ℝ) q); linarith
  obtain ⟨loss, hlossdef⟩ : ∃ loss : ℝ, loss = ρ / (4 * Ltot) := ⟨_, rfl⟩
  have hloss0 : 0 < loss := by rw [hlossdef]; exact div_pos hρ (by linarith)
  have hloss1 : loss ≤ 1 := by
    rw [hlossdef, div_le_one (by linarith)]; linarith
  have hlossE : loss * ((309 : ℝ) + 2 * (E : ℝ) + (q : ℝ) + (P : ℝ)) ≤ ρ / 4 := by
    have hle : (309 : ℝ) + 2 * (E : ℝ) + (q : ℝ) + (P : ℝ) ≤ Ltot := by rw [hLtot]; linarith
    calc loss * ((309 : ℝ) + 2 * (E : ℝ) + (q : ℝ) + (P : ℝ)) ≤ loss * Ltot :=
          mul_le_mul_of_nonneg_left hle hloss0.le
      _ = ρ / 4 := by rw [hlossdef]; field_simp
  have hloss208 : loss * ((208 : ℕ) : ℝ) ≤ ρ / 4 := by
    have hle : ((208 : ℕ) : ℝ) ≤ Ltot := by
      rw [hLtot]; push_cast
      have := (Nat.cast_nonneg (α := ℝ) E); have := (Nat.cast_nonneg (α := ℝ) q); linarith
    calc loss * ((208 : ℕ) : ℝ) ≤ loss * Ltot := mul_le_mul_of_nonneg_left hle hloss0.le
      _ = ρ / 4 := by rw [hlossdef]; field_simp
  refine ⟨loss, hloss0, hloss1, ?_⟩
  intro L gain hL hgain hgain8 Mp Dp Mr
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = gain * L := ⟨_, rfl⟩
  have hG : 0 < G := by rw [hGdef]; exact mul_pos hgain hL
  refine ⟨Ecoef * (⌈L⌉₊ + 3*⌈G⌉₊ + Mp + Mr + 4) + 1, ?_⟩
  intro Mi hMi τ hτ
  obtain ⟨PML, hPML⟩ : ∃ PML : ℝ, PML = physicalMassLoss Cmk := ⟨_, rfl⟩
  have hPML0 : 0 < PML := by rw [hPML]; exact physicalMassLoss_pos hCmk
  obtain ⟨Cbig, hCbig⟩ : ∃ Cbig : ℝ, Cbig = 8 * resolutionConst q * C0 + 4 * PML * C0 ^ 2 + 8 * C0 ^ 2 + 3 := ⟨_, rfl⟩
  have hCbig1 : 1 ≤ Cbig := by
    have h1 : 0 < 8 * resolutionConst q * C0 :=
      mul_pos (mul_pos (by norm_num) (resolutionConst_pos q)) (by linarith)
    have h2 : 0 ≤ 4 * PML * C0 ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hPML0.le) (sq_nonneg _)
    have h3 : 0 ≤ C0 ^ 2 := sq_nonneg C0
    rw [hCbig]; linarith
  refine ⟨max (max 2 C0) (Cbig ^ (1 / (ρ * G / 4))), le_max_of_le_left (le_max_left _ _), ?_⟩
  intro Nk hNk W ν B κ r T C lev γ j c u Q R A F H ex b P0 hκ hT hprob hB hBup hBinv
    hP0deg hP0coef hch hjb hr hroom hpacket
  haveI : IsProbabilityMeasure (ν (γ b)) := hprob
  have hN2 : 2 ≤ Nk := (le_max_left _ _).trans ((le_max_left _ _).trans hNk)
  have hN1 : 1 ≤ Nk := by linarith
  have hN0 : 0 < Nk := by linarith
  have hC0N : C0 ≤ Nk := (le_max_right _ _).trans ((le_max_left _ _).trans hNk)
  have hbigN : Cbig ≤ Nk ^ (ρ * G / 4) :=
    const_le_rpow_of_large (div_pos (mul_pos hρ hG) (by norm_num)) hCbig1 ((le_max_right _ _).trans hNk)
  -- the source
  obtain ⟨source, hκK, hKN⟩ := physical_source_of_packet hpacket
  have hK2 : 2 ≤ source.K := source.K_two
  have hK1 : 1 ≤ source.K := by linarith
  have hKG : source.K ≤ Nk ^ (loss * G) := by
    rw [hGdef, ← mul_assoc]; exact hKN
  -- the chart facts
  have hFdata := hch.2.2.2.2.2.2.2.2.2.2.1
  have hh0 : 0 < ((2:ℝ) ^ T (lev b))⁻¹ := by positivity
  have hblock : ∀ t, t ∈ Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)) ↔
      t ∈ Icc ((j b : ℝ) * ((2:ℝ) ^ T (lev b))⁻¹)
        ((j b : ℝ) * ((2:ℝ) ^ T (lev b))⁻¹ + ((2:ℝ) ^ T (lev b))⁻¹) := by
    intro t
    have e1 : (j b : ℝ) / (2:ℝ) ^ T (lev b) = (j b : ℝ) * ((2:ℝ) ^ T (lev b))⁻¹ :=
      div_eq_mul_inv _ _
    have e2 : ((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b) =
        (j b : ℝ) * ((2:ℝ) ^ T (lev b))⁻¹ + ((2:ℝ) ^ T (lev b))⁻¹ := by
      field_simp
    rw [e1, e2]
  have hSA : source.S ⊆ A b ×ˢ Icc ((j b : ℝ) * ((2:ℝ) ^ T (lev b))⁻¹)
      ((j b : ℝ) * ((2:ℝ) ^ T (lev b))⁻¹ + ((2:ℝ) ^ T (lev b))⁻¹) := by
    intro p hp
    have hpF := (source.subset_S hp).2
    obtain ⟨_, hpA, hpt, _⟩ := hFdata p hpF
    exact ⟨hpA, (hblock p.2).1 hpt⟩
  -- the numerics
  obtain ⟨Cr, hCrdef⟩ : ∃ Cr : ℝ, Cr = C0 * source.K ^ E := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = Nk ^ (-((1 - ρ) * G)) / (4 * Cr) := ⟨_, rfl⟩
  obtain ⟨hw0, hw1, hCr1, hCrN, hres, hval6, hcurv7, hmass8⟩ :=
    exit_numerics (q := q) (E := E) (m := 208) (P := P) hN1 hG hρ hρ1 hd₁ hd₁1 hτ hloss0 hlossE
      hloss208 hC0 hK1 hKG hPML0 hCbig.symm.le hbigN Cr w hCrdef hwdef
  have hCr0 : 0 < Cr := by linarith
  -- the resolution of the counting
  have hζ : δ Nk (2 * gain * L) ≤ 2 * Nk ^ (-(2 * G)) := by
    have := δ_le_two_rpow_neg (x := 2 * gain * L) hN0
    rw [hGdef]; convert this using 3; ring
  have hresolve : countingResolution source.K (physicalPotentialLip q source.K) * δ Nk (2 * gain * L) ≤ w := by
    calc countingResolution source.K (physicalPotentialLip q source.K) * δ Nk (2 * gain * L)
        ≤ resolutionConst q * source.K ^ (100 + q + P) * (2 * Nk ^ (-(2 * G))) :=
          mul_le_mul ((countingResolution_le hK1).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK1 (by omega))
              (resolutionConst_pos q).le)) hζ (Broad.δ_pos _ _).le
            (mul_nonneg (resolutionConst_pos q).le (pow_nonneg (by linarith) _))
      _ ≤ w := hres
  have hmargin : source.K^P * δ Nk (2*gain*L) ≤ w := by
    have hconst : 1 ≤ resolutionConst q := by
      unfold resolutionConst
      have hnn : (0:ℝ) ≤ 9*(q:ℝ)*((q+1)^3:ℕ) := by positivity
      linarith only [hnn]
    have hfactor : source.K^P ≤ resolutionConst q*source.K^(100+q+P) :=
      (pow_le_pow_right₀ hK1 (by omega)).trans
        (le_mul_of_one_le_left (by positivity) hconst)
    exact (mul_le_mul hfactor hζ (Broad.δ_pos _ _).le (by positivity)).trans hres
  -- the heavy one-branch group (x1038)
  obtain ⟨g, β, Gev, hGm, hGsub, hfloor, hlines, hbreadth, hdens⟩ :=
    source.exists_physical_heavy_group hSA hCmk hMK hw0 hw1 hresolve
  have hfloorpos : 0 < physicalHeavyFloor ((2:ℝ) ^ T (lev b))⁻¹ ((ν (γ b)).real (A b)) Cmk source.K w d₁ := by
    have href := source.reference_pos
    have hνA : 0 < (ν (γ b)).real (A b) := by
      rw [measureReal_def]
      apply ENNReal.toReal_pos
      · intro h0; rw [h0, mul_zero] at href; exact lt_irrefl _ href
      · exact measure_ne_top _ _
    unfold physicalHeavyFloor
    have hK0 : 0 < source.K := by linarith
    have hKr : 0 < source.K ^ (-100:ℝ) := Real.rpow_pos_of_pos hK0 _
    have hwd : 0 < w ^ d₁ := Real.rpow_pos_of_pos hw0 _
    positivity
  have hGpos : 0 < ((ν (γ b)).prod volume) Gev := by
    have h1 : 0 < ((ν (γ b)).prod volume).real Gev := hfloorpos.trans_le hfloor
    rw [measureReal_def] at h1
    exact ENNReal.toReal_pos_iff.mp h1 |>.1
  -- the density relative to the group's own mass (x1038's group_base_density)
  have hdensrel : ∀ U : Set P3, MeasurableSet U →
      ((ν (γ b)).prod volume).restrict Gev {e | packetBase (T (lev b)) (j b) (c b) (u b) e ∈ U} ≤
        ENNReal.ofReal ((1 + 2 * physicalMassLoss Cmk) * source.K ^ 209) *
          (((ν (γ b)).prod volume).restrict Gev) univ * volume U := by
    intro U hU
    refine (source.group_base_density hSA hCmk hw0 hd₁1.le hGm
      (fun e he => (hGsub he).1.1.1) hfloor hdens U hU).trans ?_
    have hle : 2 * physicalMassLoss Cmk * source.K ^ 209 ≤
        (1 + 2 * physicalMassLoss Cmk) * source.K ^ 209 :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (by linarith) 209)
    exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl) le_rfl
  -- the restoration
  obtain ⟨Rt, A', G', hRdeg, hRcoef, hA'm, hA'sub, hG'm, hG'sub, hG'A, hval, hreg, hfrac⟩ :=
    hrest Nk Mp Dp Mr κ (T (lev b)) (j b) (r (lev b)) (B (γ b)) (δ Nk (2 * gain * L)) d₁
      (c b) (u b) (Q b) (R b) P0 (A b) (F b) (H (γ b)) ex (ν (γ b)) source hN2 hκ hκK hB hBup
      hBinv hT hP0deg hP0coef hch hjb hr hd₁ hd₁1 hSA w g β Gev hw0 hw1 hresolve hmargin hGm hGsub
      hlines hbreadth hdens hdensrel hGpos
  simp only [← hCrdef] at hval hreg hfrac
  -- the direct exit
  have ha0 : 0 < δ Nk (r (lev b)) := Broad.δ_pos _ _
  have haup : δ Nk (r (lev b)) ≤ 2 * Nk ^ (-(r (lev b))) := δ_le_two_rpow_neg hN0
  have halo : Nk ^ (-(r (lev b))) ≤ δ Nk (r (lev b)) := rpow_neg_le_δ hN0
  have hδ2up : δ Nk (r (lev b) + gain * L) ≤ 2 * Nk ^ (-(r (lev b))) * Nk ^ (-G) := by
    have := δ_le_two_rpow_neg (x := r (lev b) + gain * L) hN0
    rw [mul_assoc, ← Real.rpow_add hN0]
    convert this using 3; rw [hGdef]; ring
  have hδ2lo : Nk ^ (-(r (lev b))) * Nk ^ (-G) ≤ δ Nk (r (lev b) + gain * L) := by
    have := rpow_neg_le_δ (x := r (lev b) + gain * L) hN0
    rw [← Real.rpow_add hN0]
    convert this using 2; rw [hGdef]; ring
  have hρG : ρ * gain * L = ρ * G := by rw [hGdef]; ring
  have hNρ : Nk ^ (ρ * G / 2) ≤ Nk ^ (ρ * gain * L + τ) := by
    rw [hρG]; apply Real.rpow_le_rpow_of_exponent_le hN1; have := mul_pos hρ hG; linarith
  have hNρ0 : Nk ^ (ρ * G) ≤ Nk ^ (ρ * gain * L + τ) := by
    rw [hρG]; apply Real.rpow_le_rpow_of_exponent_le hN1; linarith
  have hCrbig : Cr ≤ Nk ^ (ρ * gain * L + τ) := hCrN.trans hNρ
  have hrN0 : 0 < Nk ^ (-(r (lev b))) := Real.rpow_pos_of_pos hN0 _
  have hBpos := hB
  refine cd_of_direct (direct_of_quadratic_test b hgain8 hroom Rt A' G'
    (Cr * (δ Nk (r (lev b)) * w)) (Cr * B (γ b)) (Cr * B (γ b) ^ 2 / (δ Nk (r (lev b)) * w)) (B (γ b) / Cr) hRdeg ?_ hA'm
    (hA'sub.trans (source.groupLines_subset (fun e he => (hSA he).1) w g)) ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · -- coefficients
    intro e
    have hKformat : source.K ≤ Nk^⌈G⌉₊ := by
      calc source.K ≤ Nk^(loss*G) := hKG
        _ ≤ Nk^((⌈G⌉₊:ℕ):ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le hN1
            exact (mul_le_of_le_one_left hG.le hloss1).trans (Nat.le_ceil G)
        _ = _ := Real.rpow_natCast _ _
    have hCrformat : Cr ≤ Nk^⌈G⌉₊ := by
      calc Cr ≤ Nk^(ρ*G/2) := hCrN
        _ ≤ Nk^((⌈G⌉₊:ℕ):ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le hN1
            exact (div_le_self (mul_nonneg hρ.le hG.le) (by norm_num : (1:ℝ) ≤ 2)).trans
              ((mul_le_of_le_one_left hG.le hρ1.le).trans (Nat.le_ceil G))
        _ = _ := Real.rpow_natCast _ _
    exact (hRcoef e).trans (restored_coeff_with_inverse_le hN2 hC0N
      (zero_le_one.trans hK1) hKformat hG.le (by nlinarith only [hroom, hgain.le, hL.le])
      hρ.le ha0 halo hCr0 hCrformat hwdef hMi)
  · -- values and jets along the retained lines
    intro l hl t ht
    exact hval l hl t ht
  · -- value bound
    calc Cr * (δ Nk (r (lev b)) * w) ≤ Cr * (2 * Nk ^ (-(r (lev b))) * w) := by gcongr
      _ = Nk ^ (-(r (lev b))) * (2 * (Cr * w)) := by ring
      _ ≤ Nk ^ (-(r (lev b))) * (Nk ^ (ρ * G) * Nk ^ (-G)) :=
          mul_le_mul_of_nonneg_left hval6 hrN0.le
      _ = Nk ^ (ρ * G) * (Nk ^ (-(r (lev b))) * Nk ^ (-G)) := by ring
      _ ≤ Nk ^ (ρ * gain * L + τ) * δ Nk (r (lev b) + gain * L) :=
          mul_le_mul hNρ0 hδ2lo (by positivity) (by positivity)
  · -- first hidden derivative
    exact mul_le_mul_of_nonneg_right hCrbig hB.le
  · -- hidden curvature
    have haw : 0 < δ Nk (r (lev b)) * w := mul_pos ha0 hw0
    rw [div_le_div_iff₀ haw (Broad.δ_pos _ _)]
    have hB2 : 0 ≤ B (γ b) ^ 2 := sq_nonneg _
    calc Cr * B (γ b) ^ 2 * δ Nk (r (lev b) + gain * L)
        ≤ Cr * B (γ b) ^ 2 * (2 * Nk ^ (-(r (lev b))) * Nk ^ (-G)) :=
          mul_le_mul_of_nonneg_left hδ2up (by positivity)
      _ = B (γ b) ^ 2 * Nk ^ (-(r (lev b))) * (2 * Cr * Nk ^ (-G)) := by ring
      _ ≤ B (γ b) ^ 2 * Nk ^ (-(r (lev b))) * (Nk ^ (ρ * G) * w) :=
          mul_le_mul_of_nonneg_left hcurv7 (by positivity)
      _ = Nk ^ (ρ * G) * B (γ b) ^ 2 * (Nk ^ (-(r (lev b))) * w) := by ring
      _ ≤ Nk ^ (ρ * gain * L + τ) * B (γ b) ^ 2 * (δ Nk (r (lev b)) * w) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hNρ0 hB2)
            (mul_le_mul_of_nonneg_right halo hw0.le) (by positivity) (by positivity)
  · -- counted incidences
    intro p hp
    have hpG := hG'sub hp
    have hpS : p ∈ source.S := (hGsub hpG).1.1.1
    have hpHF := source.subset_S hpS
    obtain ⟨_, _, hpt, _⟩ := hFdata p hpHF.2
    exact ⟨hpHF.1, hG'A p hp, hpt, hreg p hp⟩
  · -- lower hidden derivative
    exact div_le_div_of_nonneg_left hB.le hCr0 hCrbig
  · -- mass
    have hGfin : ((ν (γ b)).prod volume) Gev ≠ ⊤ := by
      apply ne_top_of_le_ne_top (b := ENNReal.ofReal ((2:ℝ) ^ T (lev b))⁻¹ * ν (γ b) (A b))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      simpa only [Measure.restrict_apply_univ] using
        original_block_mass_le (ν (γ b)) (A b) _ _ Gev
          (Set.Subset.trans (fun e he => (hGsub he).1.1.1) hSA)
    have hlow := physicalHeavyFloor_lower (h := ((2:ℝ) ^ T (lev b))⁻¹)
      (prior := (ν (γ b)).real (A b)) hh0.le measureReal_nonneg hCmk hK1 hw0 (d := d₁)
    have hexp : -((d₁ * gain + ρ * gain) * L) - τ = -((d₁ * G + ρ * G)) - τ := by
      rw [hGdef]; ring
    have hdiv : Nk ^ (-((d₁ * gain + ρ * gain) * L) - τ) / (2:ℝ) ^ T (lev b) =
        Nk ^ (-((d₁ * gain + ρ * gain) * L) - τ) * ((2:ℝ) ^ T (lev b))⁻¹ := div_eq_mul_inv _ _
    rw [hdiv]
    refine direct_mass_chain (measure_ne_top _ _) rfl hh0.le hCr0
      (Real.rpow_nonneg hN0.le _) hfloor hGfin hfrac ?_
    rw [hexp]
    have hnum := hmass8
    calc Nk ^ (-((d₁ * G + ρ * G)) - τ) * (((2:ℝ) ^ T (lev b))⁻¹ * (ν (γ b)).real (A b))
        ≤ w ^ d₁ / (PML * source.K ^ 208 * Cr) *
            (((2:ℝ) ^ T (lev b))⁻¹ * (ν (γ b)).real (A b)) :=
          mul_le_mul_of_nonneg_right hnum (mul_nonneg hh0.le measureReal_nonneg)
      _ = ((2:ℝ) ^ T (lev b))⁻¹ * (ν (γ b)).real (A b) * w ^ d₁ /
            (physicalMassLoss Cmk * source.K ^ 208) / Cr := by
          rw [hPML]; field_simp
      _ ≤ physicalHeavyFloor ((2:ℝ) ^ T (lev b))⁻¹ ((ν (γ b)).real (A b)) Cmk source.K w d₁ / Cr :=
          div_le_div_of_nonneg_right hlow hCr0.le

end

end Submission.Obl.k4_physical_parent_potential_candidates
