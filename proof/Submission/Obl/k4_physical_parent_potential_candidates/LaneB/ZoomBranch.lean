-- The zoom and branch steps follow the proofs of `sampled_exit_of_physical_group`
-- (Broad/Restoration/PhysicalExit.lean) and `sampled_exit_of_certified_group`
-- (Broad/Restoration/SampledExitCertified.lean) of the adapted back end (this LOT tree,
-- o265 x1031 2bb8b824, itself from o267 x0945 7135e2fb); here they stop at the branch.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.PhysicalExit
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.BranchRegular
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.ZoomDiscriminant

/-!
# The zoomed branch of a physical group (lane B, step 1)

From a physical group (the hypotheses of the back end's sampled exit, without the seven common
directions), localize to a zoom ball carrying a fixed power of its mass, and build the branch
`f` of the zoomed native equation with its holomorphic extension and its rational presentation.
Every event of the localized group keeps its physical group points along its own trajectory,
now in zoomed coordinates.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial

/-- **The zoomed branch of a physical group.** -/
theorem zoomed_branch_of_physical_group (d : ℕ) (hd : 2 ≤ d) :
    ∃ Mexp q : ℕ, 1 ≤ Mexp ∧ 1 ≤ q ∧
    ∀ (A_R : ℝ), 2 ≤ A_R →
    ∀ {ν : Measure Line} {Bv : ℝ}, 0 < Bv →
    ∀ (c₁ c₁' : Fin 3 → ℝ) (M₁ M₁' : Matrix (Fin 3) (Fin 3) ℝ) (B' : ℝ),
      M₁' * M₁ = 1 → (∀ k, c₁' k = -∑ i : Fin 3, M₁' k i * c₁ i) → B' * Bv = 1 →
    ∀ (R0 Rc : Poly) (Pot : MvPolynomial (Fin 3) ℝ), R0.totalDegree ≤ 2 → Rc.totalDegree ≤ 2 →
      Pot.totalDegree ≤ d →
    ∀ (σ εfit A₁ Vc : ℝ), σ ≠ 0 → 2 ≤ A₁ → 2 * A₁ ^ 2 ≤ A_R ^ 2 →
      4 * |nativeA (transportPolynomial c₁' M₁' B' R0)| * εfit ≤ (2 * A₁ ^ 2)⁻¹ →
      (∀ m, |(nativeBaseDiscriminant (nativeA (transportPolynomial c₁' M₁' B' R0))
        (nativeB (transportPolynomial c₁' M₁' B' R0))
        (nativeC (transportPolynomial c₁' M₁' B' R0) (basePullback c₁' M₁' Pot))).coeff m| ≤
          A_R) →
    ∀ (Gev : Set Event) (β mG τw : ℝ), MeasurableSet Gev → 0 < mG → 0 ≤ τw →
      ((ν.prod volume) Gev ≠ ⊤) →
      (∀ p ∈ Gev, normalizedBase c₁ M₁ Bv (graphPoint p.1 p.2) ∈ closedBall (0 : Base) 1 ∧
        ∀ t, |t - p.2| ≤ τw → PhysicalGroupPoint B' R0 Rc Pot εfit A₁ σ Vc (graphPoint p.1 t)) →
      (∀ U : Set Base, MeasurableSet U →
        (ν.prod volume) (Gev ∩
          (fun p : Event => normalizedBase c₁ M₁ Bv (graphPoint p.1 p.2)) ⁻¹' U) ≤
          ENNReal.ofReal β * volume U) →
      ENNReal.ofReal mG ≤ (ν.prod volume) Gev →
    ∃ (cz : Fin 3 → ℝ) (Gz : Set Event) (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ)
      (Δ U V Wp : MvPolynomial (Fin 3) ℂ) (sq : EuclideanSpace ℂ (Fin 3) → ℂ),
      -- the localized group, in the zoomed normalization
      (∀ i, |cz i| ≤ 1) ∧ MeasurableSet Gz ∧ Gz ⊆ Gev ∧
      ENNReal.ofReal (mG / (A_R ^ q) ^ (3 * (1 + (Mexp + 1)) + 14)) ≤ (ν.prod volume) Gz ∧
      (∀ U : Set Base, MeasurableSet U →
        (ν.prod volume) (Gz ∩ (fun p : Event => normalizedBase
          (zoomForwardShift c₁ cz ((A_R ^ q) ^ Mexp)) (((A_R ^ q) ^ Mexp) • M₁) Bv
            (graphPoint p.1 p.2)) ⁻¹' U) ≤
          ENNReal.ofReal (β / ((A_R ^ q) ^ Mexp) ^ 3) * volume U) ∧
      (∀ x ∈ Gz, ‖normalizedBase (zoomForwardShift c₁ cz ((A_R ^ q) ^ Mexp))
        (((A_R ^ q) ^ Mexp) • M₁) Bv (graphPoint x.1 x.2)‖ < 1 / 2) ∧
      -- the branch of the zoomed native equation
      ContDiffOn ℂ ⊤ F (ball 0 4) ∧ ContDiffOn ℝ 6 f (ball 0 3) ∧
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) ∧
      (∀ z ∈ ball (0 : Base) 4,
        nativeA (transportPolynomial (zoomShift c₁' M₁' cz) (zoomMatrix M₁' ((A_R ^ q) ^ Mexp))
          B' R0) * (f z) ^ 2 +
        eval (fun i => z i) (nativeB (transportPolynomial (zoomShift c₁' M₁' cz)
          (zoomMatrix M₁' ((A_R ^ q) ^ Mexp)) B' R0)) * f z +
        eval (fun i => z i) (nativeC (transportPolynomial (zoomShift c₁' M₁' cz)
          (zoomMatrix M₁' ((A_R ^ q) ^ Mexp)) B' R0)
          (basePullback (zoomShift c₁' M₁' cz) (zoomMatrix M₁' ((A_R ^ q) ^ Mexp)) Pot)) = 0 ∧
        0 < (2 * nativeA (transportPolynomial (zoomShift c₁' M₁' cz)
          (zoomMatrix M₁' ((A_R ^ q) ^ Mexp)) B' R0) * f z +
          eval (fun i => z i) (nativeB (transportPolynomial (zoomShift c₁' M₁' cz)
            (zoomMatrix M₁' ((A_R ^ q) ^ Mexp)) B' R0))) * σ) ∧
      Wp ≠ 0 ∧ Δ ≠ 0 ∧ DifferentiableOn ℂ sq (ball 0 4) ∧ Δ.totalDegree ≤ 2 * (d + 1) ∧ U.totalDegree ≤ 2 * (d + 1) ∧
      V.totalDegree ≤ 2 * (d + 1) ∧ Wp.totalDegree ≤ 2 * (d + 1) ∧
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) ∧
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) Wp * F z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) ∧
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, eval (fun i => z i) Wp ≠ 0) ∧
      HasRealExtension (864 * (2 * (d + 1)) + 2) f ∧
      -- the group points along trajectories, in the zoomed normalization
      ∀ x ∈ Gz, ∀ t, |t - x.2| ≤ τw →
        PhysicalGroupPoint B' R0 Rc Pot εfit A₁ σ Vc (graphPoint x.1 t) := by
  obtain ⟨Mexp, hMexp, hbranch⟩ := uniform_branch_with_regular_presentation d
  obtain ⟨q, hq, hzoom⟩ := zoom_discriminant_conditions d
  refine ⟨Mexp, q, hMexp, hq, ?_⟩
  intro A_R hAR ν Bv hBv c₁ c₁' M₁ M₁' B' hM hc hB R0 Rc Pot hR0 hRc hPot σ εfit A₁ Vc hσ hA₁
    hA₁R hsmall hcoeff Gev β mG τw hGm hmG hτw hfin hGev hdom hmass
  set A := A_R ^ q with hAdef
  set lam := A ^ Mexp with hlamdef
  have hA2 : 2 ≤ A := hAR.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ A_R) hq)
  have hApos : 0 < A := by linarith
  have hlam : 0 < lam := pow_pos hApos Mexp
  -- localization
  set μ0 : Measure Event := ν.prod volume with hμ0
  set Zc : Event → Base := fun p => normalizedBase c₁ M₁ Bv (graphPoint p.1 p.2) with hZcdef
  have hZc : Measurable Zc := measurable_eventBase _ _ _
  have hbound : ∀ p ∈ Gev, Zc p ∈ ball (0 : Base) (A ^ 1) := by
    intro p hp
    have h1 := (hGev p hp).1
    rw [mem_closedBall, dist_zero_right] at h1
    rw [mem_ball, dist_zero_right, pow_one]
    linarith
  obtain ⟨ω₀, hω₀, hGzm, hGzmass, hGzdom, hGznorm⟩ := zoom_group_localization μ0 Zc hZc Gev hGm
    hfin hA2 1 (Mexp + 1) hlam hbound hmG hmass hdom
  set Gz := {ω | ω ∈ Gev ∧ Zc ω ∈ ball (Zc ω₀) (A ^ (Mexp + 1))⁻¹} with hGzdef
  set cz : Fin 3 → ℝ := fun i => Zc ω₀ i with hczdef
  obtain ⟨hω₀ball, hω₀line⟩ := hGev ω₀ hω₀
  have hczi : ∀ i, |cz i| ≤ 1 := by
    intro i
    have h1 := hω₀ball
    rw [mem_closedBall, dist_zero_right] at h1
    exact (PiLp.norm_apply_le (Zc ω₀) i).trans h1
  -- the physical group point at the centre and the zoomed discriminant conditions
  have hx₀ := hω₀line ω₀.2 (by simp; exact hτw)
  have hcube₀ := certifiedGroupPoint_of_physical hM hc hB hx₀
    (by
      have h1 := hω₀ball
      rw [mem_closedBall, dist_zero_right] at h1
      rw [mem_ball, dist_zero_right]
      exact lt_of_le_of_lt h1 (by norm_num))
  set Sx := transportPolynomial c₁' M₁' B' R0 with hSx
  set Px := basePullback c₁' M₁' Pot with hPx
  have hSxdeg : Sx.totalDegree ≤ 2 := (totalDegree_transportPolynomial_le _ _ _ _).trans hR0
  set w₀ := (pointOfCoordinates (coordinateMap c₁ M₁ Bv (graphPoint ω₀.1 ω₀.2))).2
  have hz₀ : (pointOfCoordinates (coordinateMap c₁ M₁ Bv (graphPoint ω₀.1 ω₀.2))).1 =
      WithLp.toLp 2 cz := rfl
  obtain ⟨⟨-, hfit₀, hsign₀, hlo₀, hhi₀⟩, -⟩ := hcube₀
  rw [hz₀] at hfit₀ hsign₀ hlo₀ hhi₀
  rw [native_equation Sx hSxdeg Px] at hfit₀
  rw [native_derivative Sx hSxdeg] at hsign₀ hlo₀ hhi₀
  obtain ⟨-, hσ0, hdisc, hcenter⟩ := hzoom Mexp A_R hAR c₁' M₁' B' cz R0 Pot hR0 hPot hd hczi σ
    A₁ εfit w₀ hA₁ hA₁R hsmall hcoeff hfit₀ hlo₀ hhi₀ hsign₀
  -- the branch of the zoomed equation
  set S0 := transportPolynomial (zoomShift c₁' M₁' cz) (zoomMatrix M₁' lam) B' R0 with hS0
  set P0 := basePullback (zoomShift c₁' M₁' cz) (zoomMatrix M₁' lam) Pot with hP0
  have hS0deg : S0.totalDegree ≤ 2 := (totalDegree_transportPolynomial_le _ _ _ _).trans hR0
  have hBdeg : (baseDilation (A ^ Mexp) (nativeB S0)).totalDegree ≤ d :=
    (baseDilation_totalDegree _ _).trans ((totalDegree_nativeB S0 hS0deg).trans (by omega))
  have hCdeg : (baseDilation (A ^ Mexp) (nativeC S0 P0)).totalDegree ≤ d :=
    (baseDilation_totalDegree _ _).trans
      (totalDegree_nativeC S0 P0 hS0deg hd ((totalDegree_basePullback _ _ _).trans hPot))
  obtain ⟨F, f, Δ, U, V, Wp, sq, hF, hf6, hmatch, hroot0, hW0, hΔ0, hsqd, hΔ, hU, hV, hW, hsq, hpres,
    hWne, hext⟩ := hbranch A hA2 _ _ (nativeA S0) σ hBdeg hCdeg hσ hσ0 hdisc hcenter
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
  obtain ⟨hfext, -, -, -⟩ := hext R0 1 hR0 one_ne_zero
  -- the localized group in zoomed coordinates
  have hZzeq : ∀ (l : Line) (t : ℝ), normalizedBase (zoomForwardShift c₁ cz lam) (lam • M₁) Bv
      (graphPoint l t) = zoomMap (Zc ω₀) lam (normalizedBase c₁ M₁ Bv (graphPoint l t)) := by
    intro l t
    rw [normalizedBase_zoom]
  have hcalc : lam * (A ^ (Mexp + 1))⁻¹ = A⁻¹ := by
    rw [pow_succ, mul_inv, ← mul_assoc, hlamdef, mul_inv_cancel₀ (pow_ne_zero _ hApos.ne'),
      one_mul]
  have hAinv : A⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hA2
  refine ⟨cz, Gz, F, f, Δ, U, V, Wp, sq, hczi, hGzm, fun x hx => hx.1, hGzmass, ?_, ?_, hF, hf6,
    hmatch, hroot, hW0, hΔ0, hsqd, hΔ, hU, hV, hW, hsq, hpres, hWne, hfext, ?_⟩
  · intro U hU
    have h := hGzdom U hU
    calc μ0 (Gz ∩ (fun p : Event => normalizedBase (zoomForwardShift c₁ cz lam) (lam • M₁) Bv
          (graphPoint p.1 p.2)) ⁻¹' U)
        = μ0 ((fun ω => zoomMap (Zc ω₀) lam (Zc ω)) ⁻¹' U ∩ Gz) := by
          rw [Set.inter_comm]
          congr 1
          ext p
          simp only [mem_preimage, mem_inter_iff]
          rw [hZzeq]
      _ ≤ _ := h
  · intro x hx
    have h1 := hGznorm x hx
    rw [hcalc] at h1
    rw [hZzeq]
    exact lt_of_lt_of_le h1 hAinv
  · intro x hx t ht
    exact ((hGev x hx.1).2 t ht)

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
