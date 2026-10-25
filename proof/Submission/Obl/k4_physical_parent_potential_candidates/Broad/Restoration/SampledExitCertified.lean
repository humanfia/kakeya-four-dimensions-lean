-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/SampledExitCertified.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/SampledExitCertified.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.RawAssembly
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.BranchConstruction
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.SampledPackaging
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.NativeCoordinates
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.GroupWitness

/-!
# The sampled exit of a heavy group, with a separate certificate test

`sampled_exit_of_group` is the end-to-end analytic exit: a group test `R0 - Pot` (old native
quadratic minus potential with its common intercept, physical coordinates) at an original packet,
a normalization `coordinateMap c M B` with explicit inverse, the native discriminant conditions
at the zoom centre, a common base set `E` of exact anchors with seven directions in general
position and nearby tubes of group points, and the frozen-coordinate group lines and counted
incidences with their original-law mass, give the frozen sampled alternative
`RawSampledCandidate`. The branch, its rational presentation and complex extensions are built
inside (`uniform_branch_with_presentation`); every jet test is derived (`rawBranchData_of_witnesses`).
The relation degree `864 * (2 * (d + 1)) + 2` depends only on the potential degree `d`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial
open scoped ContDiff

/-- A finite measure dominated by `β` times volume, of mass at least `m`, and concentrated on
a measurable set `U`, forces `volume U ≥ m / β`. -/
theorem volume_ge_of_dominated_ae (μ : Measure Base) {m β : ℝ} (hβ : 0 < β)
    (hmass : ENNReal.ofReal m ≤ μ univ)
    (hdom : ∀ U : Set Base, MeasurableSet U → μ U ≤ ENNReal.ofReal β * volume U)
    {U : Set Base} (hU : MeasurableSet U) (hae : ∀ᵐ u ∂μ, u ∈ U) :
    ENNReal.ofReal (m / β) ≤ volume U := by
  have hcover : μ univ ≤ μ U := by
    apply measure_mono_ae
    filter_upwards [hae] with u hu
    exact fun _ => hu
  have hmU : ENNReal.ofReal m ≤ ENNReal.ofReal β * volume U :=
    hmass.trans (hcover.trans (hdom U hU))
  rw [ENNReal.ofReal_div_of_pos hβ,
    ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hβ)) ENNReal.ofReal_ne_top]
  simpa only [mul_comm] using hmU

/-- The same for a measure on any space whose base map `Zc` pushes it below `β` times volume:
if `Zc` lands in a measurable `U` almost everywhere, then `volume U ≥ m / β`. -/
theorem volume_ge_of_dominated_map_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Zc : Ω → Base) {m β : ℝ} (hβ : 0 < β) (hmass : ENNReal.ofReal m ≤ μ univ)
    (hdom : ∀ U : Set Base, MeasurableSet U → μ (Zc ⁻¹' U) ≤ ENNReal.ofReal β * volume U)
    {U : Set Base} (hU : MeasurableSet U) (hae : ∀ᵐ x ∂μ, Zc x ∈ U) :
    ENNReal.ofReal (m / β) ≤ volume U := by
  have hcover : μ univ ≤ μ (Zc ⁻¹' U) := by
    apply measure_mono_ae
    filter_upwards [hae] with x hx
    exact fun _ => hx
  have hmU : ENNReal.ofReal m ≤ ENNReal.ofReal β * volume U :=
    hmass.trans (hcover.trans (hdom U hU))
  rw [ENNReal.ofReal_div_of_pos hβ,
    ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hβ)) ENNReal.ofReal_ne_top]
  simpa only [mul_comm] using hmU

/-- The sublevel set of a function continuous on the closed unit ball is measurable. -/
theorem measurableSet_ball_sublevel {g : Base → ℝ} (hg : ContinuousOn g (closedBall (0 : Base) 1))
    (V : ℝ) : MeasurableSet (closedBall (0 : Base) 1 ∩ g ⁻¹' Icc (-V) V) :=
  (hg.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Icc).measurableSet

theorem sampled_exit_of_certified_group (d : ℕ) (hd : 2 ≤ d) :
    ∃ Mexp : ℕ, 1 ≤ Mexp ∧ ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Cloc J : ℕ), DenseJetBound (864 * (2 * (d + 1)) + 2) J →
    ∀ (A : ℝ), 2 ≤ A →
    ∀ {Nk L : ℝ} {W : ℕ} {ν : Fin W → Measure Line} {B : Fin W → ℝ} {Mc : ℕ}
      {d₁ ρ gain ε : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {Cn : ℕ} {lev : Fin Cn → ℕ}
      {γ : Fin Cn → Fin W} {j : Fin Cn → ℕ} {Aset : Fin Cn → Set Line} {H : Fin W → Set Event}
      (b : Fin Cn) (ag : ℝ), gain ≤ ag → ag ≤ 1 / 8 → r (lev b) + 2 * ag * L ≤ L →
      0 < B (γ b) →
    ∀ (c c' : Fin 3 → ℝ) (M M' : Matrix (Fin 3) (Fin 3) ℝ) (B' : ℝ),
      M' * M = 1 → (∀ k, c' k = -∑ i : Fin 3, M' k i * c i) → B' * B (γ b) = 1 →
    ∀ (R0 Rc : Poly) (Pot : MvPolynomial (Fin 3) ℝ), R0.totalDegree ≤ 2 → Rc.totalDegree ≤ 2 →
      Pot.totalDegree ≤ d →
    ∀ σ : ℝ, σ ≠ 0 →
    (nativeA (transportPolynomial c' M' B' R0) = 0 →
      0 < eval (fun _ => (0 : ℝ))
        (baseDilation (A ^ Mexp) (nativeB (transportPolynomial c' M' B' R0))) * σ) →
    (∀ m, |(nativeBaseDiscriminant (nativeA (transportPolynomial c' M' B' R0))
        (baseDilation (A ^ Mexp) (nativeB (transportPolynomial c' M' B' R0)))
        (baseDilation (A ^ Mexp)
          (nativeC (transportPolynomial c' M' B' R0) (basePullback c' M' Pot)))).coeff m| ≤ A) →
    (A⁻¹) ^ 2 ≤ eval (fun _ => (0 : ℝ)) (nativeBaseDiscriminant
        (nativeA (transportPolynomial c' M' B' R0))
        (baseDilation (A ^ Mexp) (nativeB (transportPolynomial c' M' B' R0)))
        (baseDilation (A ^ Mexp)
          (nativeC (transportPolynomial c' M' B' R0) (basePullback c' M' Pot)))) →
    ∀ (Mz MH : ℕ) (A0 Z a0 b0 At θ h Vr εfit A₁ Wmax η Vc : ℝ) (p : Fin 7 → Base) (E : Set Base),
    2 ≤ A₁ → A₁ ≤ At → At ≤ A0 → 0 < εfit → 0 < b0 → b0 ≤ a0 → a0 ≤ 1 → 0 < θ → θ ≤ 1 →
    0 ≤ h → 0 ≤ Vr → Vr ≤ A0 → 0 ≤ Wmax →
    4 * |nativeA (transportPolynomial c' M' B' R0)| * εfit ≤ (2 * A₁ ^ 2)⁻¹ →
    εfit * A₁ ^ 19 ≤ At * b0 →
    (∀ (z : Base) (w : ℝ), |eval ![z 0, z 1, z 2, w]
      (pderiv 3 (pderiv 3 (transportPolynomial c' M' B' Rc)))| ≤ At / a0) →
    (∀ e, |(transportPolynomial c' M' B' Rc).coeff e| ≤ Z) →
    A0 ^ (J + 1) ≤ Z → b0⁻¹ ≤ Z → ∀ Av : ℝ, 2 ≤ Av → Av ^ J * (Wmax + At * b0) ≤ Z →
    K * θ ^ (-C) * At ^ 28 ≤ A0 / 2 →
    At ^ (J + 9) * h * ((A0 ^ (J + 1)) ^ Cloc * a0) ≤ A0 * b0 →
    A0 ^ J * Vr * At ^ 9 * h ≤ A0 / 2 * (b0 / a0) →
    (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ At) →
    (∀ i k l : Fin 7, i ≠ k → i ≠ l → k ≠ l →
      A0⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p k, p l] r) t)|) →
    MeasurableSet E → E ⊆ closedBall (0 : Base) 1 → ENNReal.ofReal A0⁻¹ ≤ volume E →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (Zc : Ω → Base) (Wc : Ω → ℝ) (mμ βμ : ℝ),
    0 < βμ → ENNReal.ofReal mμ ≤ μ univ →
    (∀ U : Set Base, MeasurableSet U → μ (Zc ⁻¹' U) ≤ ENNReal.ofReal βμ * volume U) →
    Av⁻¹ ≤ mμ / βμ →
    (∀ᵐ x ∂μ, Zc x ∈ closedBall (0 : Base) 1 ∧ CertifiedGroupPoint (transportPolynomial c' M' B' R0)
      (basePullback c' M' Pot) (transportPolynomial c' M' B' Rc) εfit A₁ σ Vc (Zc x) (Wc x) ∧
      |Wc x| ≤ Wmax) →
    0 ≤ Vc → Av ^ J * (Vc / a0 + At ^ 4 * b0 / a0) ≤ Vr →
    (∀ u ∈ E, ∀ i, CertifiedTubeWitness (transportPolynomial c' M' B' R0)
      (basePullback c' M' Pot) (transportPolynomial c' M' B' Rc) εfit A₁ σ Vc At θ h u (p i)) →
    Mz * Cloc + 2 * MH + 11 ≤ Mc → Z ≤ Nk ^ Mz →
    (∀ i, |c i| ≤ Nk ^ MH) → (∀ i k, |M i k| ≤ Nk ^ MH) → |B (γ b)| ≤ Nk ^ MH →
    b0 = dyadicThickness Nk (r (lev b) + ag * L) →
    0 < η → η ≤ 1 →
    restorationRemezFactor η * (A0 ^ (J + 1)) ^ Cloc ≤ Nk ^ (ρ * gain * L + ε) →
    ∀ (A' : Set Line), MeasurableSet A' → A' ⊆ Aset b → ∀ (S : Line → Set ℝ),
    (∀ l ∈ A', S l ⊆ Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (S l)) →
    (∀ l ∈ A', ∀ t ∈ S l, CertifiedNativeGroupPoint c M (B (γ b))
      (transportPolynomial c' M' B' R0) (basePullback c' M' Pot)
      (transportPolynomial c' M' B' Rc) εfit A₁ σ
      (graphPoint l ((j b : ℝ) / (2 : ℝ) ^ T (lev b) + ((2 : ℝ) ^ T (lev b))⁻¹ * t))) →
    ∀ (counted : Set Event),
    counted ⊆ {q | q ∈ H (γ b) ∧ q.1 ∈ A' ∧
      q.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
      CertifiedNativeGroupPoint c M (B (γ b)) (transportPolynomial c' M' B' R0)
        (basePullback c' M' Pot) (transportPolynomial c' M' B' Rc) εfit A₁ σ
        (graphPoint q.1 q.2)} →
    ENNReal.ofReal (Nk ^ (-((d₁ * ag + ρ * gain) * L) - ε) /
        (2 : ℝ) ^ T (lev b)) * ν (γ b) (Aset b) ≤ ((ν (γ b)).prod volume) counted →
    RawSampledCandidate Cloc J (864 * (2 * (d + 1)) + 2) Nk L W ν B Mc d₁ ρ gain ε r T Cn lev
      γ j Aset H := by
  obtain ⟨Mexp, hMexp, hbranch⟩ := uniform_branch_with_presentation d
  obtain ⟨K, C, hK, hC, hraw⟩ := rawBranchData_of_witnesses Submission.k4_algebraic_sheet_remez
    (2 * (d + 1)) (by omega)
  refine ⟨Mexp, hMexp, K, C, hK, hC, ?_⟩
  intro Cloc J hjet A hA Nk L W ν B Mc d₁ ρ gain ε r T Cn lev γ j Aset H b ag hg hg8 hroom hBpos
    c c' M M' B' hM hc hB R0 Rc Pot hR0 hRc hPot σ hσ hσ0 hdisc hcenter Mz MH A0 Z a0 b0 At θ h Vr
    εfit A₁ Wmax η Vc p E hA₁ hA₁t hAtA0 hε hb0 hba ha1 hθ hθ1 hh hVr hVrA hWmax hsmall hband hcurv
    hSZ hAZ hbZ Av hAv hfZ hconst hsmall2 hsmall3 hp hdet hEm hEsub hEvol Ω _ μ Zc Wc mμ βμ hβμ
    hmμ hdomμ
    hvolμ
    hanchor hVc hVcr hwit hformat hZN
    hcN hMN hBN hb0eq hη hη1 hbudget A' hA'm hA'b S hS hgp counted hcounted hmass
  set S0 := transportPolynomial c' M' B' R0 with hS0
  set P0 := basePullback c' M' Pot with hP0
  set Sc := transportPolynomial c' M' B' Rc with hScdef
  have hS0deg : S0.totalDegree ≤ 2 := (totalDegree_transportPolynomial_le _ _ _ _).trans hR0
  have hScdeg : Sc.totalDegree ≤ 2 := (totalDegree_transportPolynomial_le _ _ _ _).trans hRc
  have hBdeg : (baseDilation (A ^ Mexp) (nativeB S0)).totalDegree ≤ d :=
    (baseDilation_totalDegree _ _).trans ((totalDegree_nativeB S0 hS0deg).trans (by omega))
  have hCdeg : (baseDilation (A ^ Mexp) (nativeC S0 P0)).totalDegree ≤ d :=
    (baseDilation_totalDegree _ _).trans
      (totalDegree_nativeC S0 P0 hS0deg hd ((totalDegree_basePullback _ _ _).trans hPot))
  obtain ⟨F, f, Δ, U, V, Wp, sq, hF, hf6, hmatch, hroot0, hW0, hΔ, hU, hV, hW, hsq, hpres,
    hWne, hext⟩ := hbranch A hA _ _ (nativeA S0) σ hBdeg hCdeg hσ hσ0 hdisc hcenter
  -- the dilated coefficients are the normalized ones
  have hAM0 : (A ^ Mexp : ℝ) ≠ 0 := pow_ne_zero _ (by linarith)
  have hundil : ∀ (Q : MvPolynomial (Fin 3) ℝ) (z : Base),
      eval (fun i => z i) (baseDilation (A ^ Mexp)⁻¹ (baseDilation (A ^ Mexp) Q)) =
        eval (fun i => z i) Q := by
    intro Q z
    rw [eval_baseDilation, eval_baseDilation]
    apply congrArg (fun v : Fin 3 → ℝ => eval v Q)
    funext i
    rw [← mul_assoc, mul_inv_cancel₀ hAM0, one_mul]
  have hroot : ∀ z ∈ ball (0 : Base) 4, nativeA S0 * (f z) ^ 2 +
      eval (fun i => z i) (nativeB S0) * f z + eval (fun i => z i) (nativeC S0 P0) = 0 ∧
      0 < (2 * nativeA S0 * f z + eval (fun i => z i) (nativeB S0)) * σ := by
    intro z hz
    have h := hroot0 z hz
    rw [hundil, hundil] at h
    exact h
  have hSeq := native_equation S0 hS0deg P0
  have hSd := native_derivative S0 hS0deg
  have ha0 : 0 < a0 := hb0.trans_le hba
  have hAt2 : 2 ≤ At := hA₁.trans hA₁t
  -- the certificate residual at every group point, by the hidden Taylor shift
  have hresG : ∀ (u : Base) (w : ℝ), CertifiedGroupPoint S0 P0 Sc εfit A₁ σ Vc u w →
      |eval ![u 0, u 1, u 2, f u] Sc / a0| ≤ Vc / a0 + At ^ 4 * b0 / a0 := by
    intro u w hw
    have hbd := band_of_normalizedGroupPoint hA₁ hε hsmall hroot hSeq hSd hw.1
    have hdist : |w - f u| ≤ At * b0 := hbd.trans hband
    have hshift := quadratic_residual_hidden_shift_bound Sc hScdeg u (f u) w hAt2 ha0 hb0.le hba
      hdist (hw.2.2.1.trans hA₁t) (hcurv u w)
    have hval : |eval ![u 0, u 1, u 2, w] Sc / a0| ≤ Vc / a0 := by
      rw [abs_div, abs_of_pos ha0]
      exact div_le_div_of_nonneg_right hw.2.2.2 ha0.le
    calc |eval ![u 0, u 1, u 2, f u] Sc / a0|
        ≤ |eval ![u 0, u 1, u 2, f u] Sc / a0 - eval ![u 0, u 1, u 2, w] Sc / a0| +
            |eval ![u 0, u 1, u 2, w] Sc / a0| := by
          have := abs_sub_abs_le_abs_sub (eval ![u 0, u 1, u 2, f u] Sc / a0)
            (eval ![u 0, u 1, u 2, w] Sc / a0)
          linarith
      _ ≤ At ^ 4 * b0 / a0 + Vc / a0 := add_le_add hshift hval
      _ = Vc / a0 + At ^ 4 * b0 / a0 := by ring
  -- extension fields
  obtain ⟨hfext, hf2ext, hRext, hR3ext⟩ := hext Sc a0 hScdeg ha0.ne'
  have hA0two : 2 ≤ A0 := (hA₁.trans hA₁t).trans hAtA0
  have hfcont : ContinuousOn f (closedBall (0 : Base) 1) :=
    (hfext.contDiffOn.continuousOn).mono (closedBall_subset_ball (by norm_num))
  have hRcont : ContinuousOn (fun x : Base => eval ![x 0, x 1, x 2, f x] Sc / a0)
      (closedBall (0 : Base) 1) :=
    (hRext.contDiffOn.continuousOn).mono (closedBall_subset_ball (by norm_num))
  have hV0 : 0 ≤ Wmax + At * b0 := by
    have : 0 ≤ At := by linarith
    positivity
  have hVR0 : 0 ≤ Vc / a0 + At ^ 4 * b0 / a0 := by
    have : 0 ≤ At := by linarith
    positivity
  -- the group measure puts both sublevel sets at volume at least `A0⁻¹`
  set Uf := closedBall (0 : Base) 1 ∩ f ⁻¹' Icc (-(Wmax + At * b0)) (Wmax + At * b0)
  set UR := closedBall (0 : Base) 1 ∩ (fun x : Base => eval ![x 0, x 1, x 2, f x] Sc / a0) ⁻¹'
    Icc (-(Vc / a0 + At ^ 4 * b0 / a0)) (Vc / a0 + At ^ 4 * b0 / a0)
  have hUfm : MeasurableSet Uf := measurableSet_ball_sublevel hfcont _
  have hURm : MeasurableSet UR := measurableSet_ball_sublevel hRcont _
  have hUfae : ∀ᵐ x ∂μ, Zc x ∈ Uf := by
    filter_upwards [hanchor] with x hx
    obtain ⟨hu1, hw, hwmax⟩ := hx
    refine ⟨hu1, abs_le.mp ?_⟩
    have hbd := band_of_normalizedGroupPoint hA₁ hε hsmall hroot hSeq hSd hw.1
    have htri : |f (Zc x)| ≤ |Wc x| + |Wc x - f (Zc x)| := by
      have := abs_sub_abs_le_abs_sub (f (Zc x)) (Wc x)
      rw [abs_sub_comm] at this
      linarith
    linarith
  have hURae : ∀ᵐ x ∂μ, Zc x ∈ UR := by
    filter_upwards [hanchor] with x hx
    obtain ⟨hu1, hw, -⟩ := hx
    exact ⟨hu1, abs_le.mp (hresG (Zc x) (Wc x) hw)⟩
  have hvolA : ENNReal.ofReal Av⁻¹ ≤ ENNReal.ofReal (mμ / βμ) := ENNReal.ofReal_le_ofReal hvolμ
  have hUfvol : ENNReal.ofReal Av⁻¹ ≤ volume Uf :=
    hvolA.trans (volume_ge_of_dominated_map_ae μ Zc hβμ hmμ hdomμ hUfm hUfae)
  have hURvol : ENNReal.ofReal Av⁻¹ ≤ volume UR :=
    hvolA.trans (volume_ge_of_dominated_map_ae μ Zc hβμ hmμ hdomμ hURm hURae)
  have hjet0 : ∀ k : ℕ, k ≤ 6 → ‖iteratedFDeriv ℝ k f 0‖ ≤ Av ^ J * (Wmax + At * b0) :=
    fun k hk => (hjet Av hAv f hfext).1 Uf _ hUfm inter_subset_left hUfvol hV0
      (fun x hx => abs_le.mpr hx.2) k hk 0 (by simp)
  have hres : ∀ u ∈ E, |eval ![u 0, u 1, u 2, f u] Sc / a0| ≤ Vr := by
    intro u hu
    have hjR := (hjet Av hAv _ hRext).1 UR _ hURm inter_subset_left hURvol hVR0
      (fun x hx => abs_le.mpr hx.2) 0 (by norm_num) u
      (closedBall_subset_closedBall (by norm_num) (hEsub hu))
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hjR
    exact hjR.trans hVcr
  have hf0 : |f 0| ≤ Z := by
    have h0 := hjet0 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
    exact h0.trans hfZ
  have hDf0 : ‖fderiv ℝ f 0‖ ≤ Z := by
    have h1 := hjet0 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at h1
    exact h1.trans hfZ
  have hD2f0 : ‖iteratedFDeriv ℝ 2 f 0‖ ≤ Z := (hjet0 2 (by norm_num)).trans hfZ
  -- the presentation denominator does not vanish on the real unit ball
  have hWreal : ∀ y ∈ closedBall (0 : Base) 1,
      eval (fun i => (DenseJet.realSlice y) i) Wp ≠ 0 := by
    intro y hy
    apply hWne
    rw [mem_ball, dist_zero_right, DenseJet.norm_realSlice_apply]
    have := mem_closedBall_zero_iff.mp hy
    linarith
  -- tubes of group points are native line witnesses
  have hwitN : ∀ u ∈ E, ∀ i, NativeLineWitness f Sc At a0 b0 θ h u (p i) :=
    fun u hu i => nativeLineWitness_of_certifiedTube hA₁ hA₁t hε hsmall hband hcurv hroot hSeq
      hSd (hwit u hu i)
  have hcurv0 : ∀ (u : Base) (w : ℝ),
      |eval ![u 0, u 1, u 2, w] (pderiv 3 (pderiv 3 Sc))| ≤ A0 / a0 :=
    fun u w => (hcurv u w).trans (div_le_div_of_nonneg_right hAtA0 ha0.le)
  obtain ⟨h0, s0, hrawdata⟩ := hraw Δ U V Wp hΔ hU hV hW hW0 sq F f hsq hpres hF hmatch hWreal hf6
    Cloc J (864 * (2 * (d + 1)) + 2) hjet Sc p E A0 At Z a0 b0 θ h Vr hfext (fun i => hf2ext (p i))
    hRext (fun i => hR3ext (p i)) hScdeg hSZ hcurv0 (hA₁.trans hA₁t) hAtA0 hb0 hba ha1 hθ hθ1 hh
    hVr hVrA hAZ hbZ hf0 hDf0 hD2f0 hconst hsmall2 hsmall3 hp hdet hEm hEsub hEvol hres hwitN
  have hband0 : εfit * A₁ ^ 19 ≤ A0 * b0 :=
    hband.trans (mul_le_mul_of_nonneg_right hAtA0 hb0.le)
  exact rawSampledCandidate_of_certified_points b ag hg hg8 hroom hBpos Mz MH A0 Z a0 b0 h0 s0 Sc
    f p E hrawdata c M hformat hZN hcN hMN hBN hb0eq η hη hη1 hbudget S0 P0 (nativeA S0)
    (nativeB S0) (nativeC S0 P0) σ εfit A₁ hA₁ (hA₁t.trans hAtA0) hε hband0 hsmall hroot hSeq hSd
    A' hA'm hA'b S hS hgp counted hcounted hmass

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
