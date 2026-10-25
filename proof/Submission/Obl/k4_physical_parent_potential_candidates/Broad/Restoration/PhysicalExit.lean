-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/PhysicalExit.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/PhysicalExit.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.SampledExitCertified
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.PhysicalGroupPoints

/-!
# The sampled exit of a physical heavy group

This is the exit in the form a group producer supplies it. The data are physical:

* a packet `b` with gain `ag`, a cube normalization `x ↦ c₁ + M₁ x` (hidden scale `B (γ b)`) with
  explicit inverse, the group's quadratic `R0`, potential `Pot` (degree `≤ d`) and the
  certificate's quadratic `Rc`;
* the cube native discriminant with coefficients at most `A_R` (for instance from
  `discriminant_coeff_bound_of_group`);
* a measurable set `Gev` of group events of `b` in `H` (physical group points, cube base point in
  the unit ball, hidden value at most `Wmax`), with base density at most `β` and mass at least
  `mG`; near each of its events the line stays a group point for time `τw` and moves at cube
  speed at most `Vmax`;
* for every possible zoom centre in the unit ball, seven directions and a common base set `E`
  with certified tube witnesses (for instance from `seven_directions_of_cells`).

Inside: the zoom centre is chosen by localization (`zoom_group_localization`), the discriminant
hypotheses come from `zoom_discriminant_conditions`, the dominated group measure, the frozen
lines `A'`, their witness time sets and the counted incidences are built, and the certified exit
`sampled_exit_of_certified_group` gives the frozen sampled alternative.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial

/-- The base point of a physical point in the coordinates `c + M x`. -/
def normalizedBase (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (x : Fin 4 → ℝ) :
    Base :=
  (pointOfCoordinates (coordinateMap c M B x)).1

lemma continuous_normalizedBase (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) :
    Continuous (normalizedBase c M B) := by
  unfold normalizedBase pointOfCoordinates coordinateMap
  apply (PiLp.continuous_toLp 2 _).comp
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

lemma continuous_graphPoint_event : Continuous (fun p : Event => graphPoint p.1 p.2) := by
  unfold graphPoint
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

lemma measurable_eventBase (c : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) :
    Measurable (fun p : Event => normalizedBase c M B (graphPoint p.1 p.2)) :=
  ((continuous_normalizedBase c M B).comp continuous_graphPoint_event).measurable

lemma normalizedBase_zoom (c₁ c : Fin 3 → ℝ) (M₁ : Matrix (Fin 3) (Fin 3) ℝ) (B lam : ℝ)
    (x : Fin 4 → ℝ) :
    normalizedBase (zoomForwardShift c₁ c lam) (lam • M₁) B x =
      zoomMap (WithLp.toLp 2 c) lam (normalizedBase c₁ M₁ B x) :=
  (coordinateMap_zoomForward c₁ c M₁ B lam x).1

/-- An interval about a point of `[0,1]` meets `[0,1]` in measure at least `min δ (1/2)`. -/
lemma volume_near_inter_unit {x δ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (min δ (1 / 2)) ≤ volume ({t | |t - x| ≤ δ} ∩ Icc (0 : ℝ) 1) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hm0 : 0 ≤ min δ (1 / 2) := le_min hδ (by norm_num)
  have hmδ : min δ (1 / 2) ≤ δ := min_le_left _ _
  have hmh : min δ (1 / 2) ≤ 1 / 2 := min_le_right _ _
  by_cases hxh : x ≤ 1 / 2
  · have hsub : Icc x (x + min δ (1 / 2)) ⊆ {t | |t - x| ≤ δ} ∩ Icc (0 : ℝ) 1 := by
      intro t ht
      refine ⟨?_, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
      show |t - x| ≤ δ
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    calc ENNReal.ofReal (min δ (1 / 2)) = volume (Icc x (x + min δ (1 / 2))) := by
          rw [Real.volume_Icc]; congr 1; ring
      _ ≤ _ := measure_mono hsub
  · have hsub : Icc (x - min δ (1 / 2)) x ⊆ {t | |t - x| ≤ δ} ∩ Icc (0 : ℝ) 1 := by
      intro t ht
      refine ⟨?_, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
      show |t - x| ≤ δ
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    calc ENNReal.ofReal (min δ (1 / 2)) = volume (Icc (x - min δ (1 / 2)) x) := by
          rw [Real.volume_Icc]; congr 1; ring
      _ ≤ _ := measure_mono hsub

/-- The null part of a set of incidences whose trajectory slices are null. -/
lemma prod_measure_inter_posSlices {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    {G : Set (α × ℝ)} (hG : MeasurableSet G) :
    (ν.prod volume) (G ∩ ({l | 0 < volume (Prod.mk l ⁻¹' G)} ×ˢ univ)) = (ν.prod volume) G := by
  apply le_antisymm (measure_mono inter_subset_left)
  have hA : MeasurableSet {l : α | 0 < volume (Prod.mk l ⁻¹' G)} :=
    measurableSet_lt measurable_const (measurable_measure_prodMk_left hG)
  have hnull : (ν.prod volume) (G ∩ ({l | 0 < volume (Prod.mk l ⁻¹' G)}ᶜ ×ˢ univ)) = 0 := by
    rw [Measure.prod_apply (hG.inter (hA.compl.prod MeasurableSet.univ))]
    have hslice : ∀ l, volume (Prod.mk l ⁻¹'
        (G ∩ ({l | 0 < volume (Prod.mk l ⁻¹' G)}ᶜ ×ˢ univ))) = 0 := by
      intro l
      by_cases hl : l ∈ {l : α | 0 < volume (Prod.mk l ⁻¹' G)}
      · have : Prod.mk l ⁻¹' (G ∩ ({l | 0 < volume (Prod.mk l ⁻¹' G)}ᶜ ×ˢ univ)) = ∅ := by
          ext t
          simp only [mem_preimage, mem_inter_iff, mem_prod, mem_compl_iff, mem_univ,
            and_true, mem_empty_iff_false, iff_false, not_and, not_not]
          exact fun _ => hl
        simp [this]
      · have hzero : volume (Prod.mk l ⁻¹' G) = 0 := by
          simpa only [mem_ofPred_eq, not_lt, nonpos_iff_eq_zero] using hl
        exact measure_mono_null (fun t ht => ht.1) hzero
    rw [lintegral_congr (fun l => hslice l), lintegral_zero]
  calc (ν.prod volume) G ≤ (ν.prod volume) (G ∩ ({l | 0 < volume (Prod.mk l ⁻¹' G)} ×ˢ univ)) +
        (ν.prod volume) (G ∩ ({l | 0 < volume (Prod.mk l ⁻¹' G)}ᶜ ×ˢ univ)) := by
        apply (measure_mono _).trans (measure_union_le _ _)
        intro x hx
        by_cases h : x.1 ∈ {l : α | 0 < volume (Prod.mk l ⁻¹' G)}
        · exact Or.inl ⟨hx, h, mem_univ _⟩
        · exact Or.inr ⟨hx, h, mem_univ _⟩
    _ = _ := by rw [hnull, add_zero]

/-- **The sampled exit of a physical heavy group.** -/
theorem sampled_exit_of_physical_group (d : ℕ) (hd : 2 ≤ d) :
    ∃ Mexp q : ℕ, 1 ≤ Mexp ∧ 1 ≤ q ∧ ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Cloc J : ℕ), DenseJetBound (864 * (2 * (d + 1)) + 2) J →
    ∀ (A_R : ℝ), 2 ≤ A_R →
    ∀ {Nk L : ℝ} {W : ℕ} {ν : Fin W → Measure Line} {B : Fin W → ℝ} {Mc : ℕ}
      {d₁ ρ gain ε : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {Cn : ℕ} {lev : Fin Cn → ℕ}
      {γ : Fin Cn → Fin W} {j : Fin Cn → ℕ} {Aset : Fin Cn → Set Line} {H : Fin W → Set Event}
      (b : Fin Cn) (ag : ℝ), gain ≤ ag → ag ≤ 1 / 8 → r (lev b) + 2 * ag * L ≤ L →
      0 < B (γ b) → IsFiniteMeasure (ν (γ b)) →
    ∀ (c₁ c₁' : Fin 3 → ℝ) (M₁ M₁' : Matrix (Fin 3) (Fin 3) ℝ) (B' : ℝ),
      M₁' * M₁ = 1 → (∀ k, c₁' k = -∑ i : Fin 3, M₁' k i * c₁ i) → B' * B (γ b) = 1 →
    ∀ (R0 Rc : Poly) (Pot : MvPolynomial (Fin 3) ℝ), R0.totalDegree ≤ 2 → Rc.totalDegree ≤ 2 →
      Pot.totalDegree ≤ d →
    ∀ (σ εfit A₁ Vc : ℝ), σ ≠ 0 → 2 ≤ A₁ → 2 * A₁ ^ 2 ≤ A_R ^ 2 →
      4 * |nativeA (transportPolynomial c₁' M₁' B' R0)| * εfit ≤ (2 * A₁ ^ 2)⁻¹ →
      (∀ m, |(nativeBaseDiscriminant (nativeA (transportPolynomial c₁' M₁' B' R0))
        (nativeB (transportPolynomial c₁' M₁' B' R0))
        (nativeC (transportPolynomial c₁' M₁' B' R0) (basePullback c₁' M₁' Pot))).coeff m| ≤
          A_R) →
    ∀ (Gev : Set Event) (Wmax β mG τw Vmax : ℝ), MeasurableSet Gev → 0 < mG →
      (∀ p ∈ Gev, p ∈ H (γ b) ∧ p.1 ∈ Aset b ∧
        p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
        normalizedBase c₁ M₁ (B (γ b)) (graphPoint p.1 p.2) ∈ closedBall (0 : Base) 1 ∧
        |B (γ b) * graphPoint p.1 p.2 3| ≤ Wmax ∧
        ∀ t, |t - p.2| ≤ τw →
          PhysicalGroupPoint B' R0 Rc Pot εfit A₁ σ Vc (graphPoint p.1 t) ∧
          ‖normalizedBase c₁ M₁ (B (γ b)) (graphPoint p.1 t) -
            normalizedBase c₁ M₁ (B (γ b)) (graphPoint p.1 p.2)‖ ≤ Vmax * |t - p.2|) →
      (∀ U : Set Base, MeasurableSet U →
        ((ν (γ b)).prod volume) (Gev ∩
          (fun p : Event => normalizedBase c₁ M₁ (B (γ b)) (graphPoint p.1 p.2)) ⁻¹' U) ≤
          ENNReal.ofReal β * volume U) →
      ENNReal.ofReal mG ≤ ((ν (γ b)).prod volume) Gev →
    ∀ (Mz MH : ℕ) (A0 Z a0 b0 At θ h Vr η Av τs ZR HR : ℝ),
    (∀ cz : Fin 3 → ℝ, WithLp.toLp 2 cz ∈ closedBall (0 : Base) 1 →
      ENNReal.ofReal (mG / (A_R ^ q) ^ (3 * (1 + (Mexp + 1)) + 14)) ≤
        ((ν (γ b)).prod volume) {x | x ∈ Gev ∧
          normalizedBase c₁ M₁ (B (γ b)) (graphPoint x.1 x.2) ∈
            ball (WithLp.toLp 2 cz) ((A_R ^ q) ^ (Mexp + 1))⁻¹} →
      ∃ (p : Fin 7 → Base) (E : Set Base),
        (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ At) ∧
        (∀ i k l : Fin 7, i ≠ k → i ≠ l → k ≠ l →
          A0⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p k, p l] r) t)|) ∧
        MeasurableSet E ∧ E ⊆ closedBall (0 : Base) 1 ∧ ENNReal.ofReal A0⁻¹ ≤ volume E ∧
        ∀ u ∈ E, ∀ i, CertifiedTubeWitness
          (transportPolynomial (zoomShift c₁' M₁' cz) (zoomMatrix M₁' ((A_R ^ q) ^ Mexp)) B' R0)
          (basePullback (zoomShift c₁' M₁' cz) (zoomMatrix M₁' ((A_R ^ q) ^ Mexp)) Pot)
          (transportPolynomial (zoomShift c₁' M₁' cz) (zoomMatrix M₁' ((A_R ^ q) ^ Mexp)) B' Rc)
          εfit A₁ σ Vc At θ h u (p i)) →
    A₁ ≤ At → At ≤ A0 → 0 < εfit → 0 < b0 → b0 ≤ a0 → a0 ≤ 1 → 0 < θ → θ ≤ 1 →
    0 ≤ h → 0 ≤ Vr → Vr ≤ A0 → 0 ≤ Wmax → 0 ≤ Vc → 0 < β → 0 ≤ Vmax →
    0 ≤ τs → τs ≤ τw → (A_R ^ q) ^ Mexp * Vmax * τs ≤ 1 / 2 →
    εfit * A₁ ^ 19 ≤ At * b0 →
    (∀ x : Fin 4 → ℝ, |B' ^ 2 * eval x (pderiv 3 (pderiv 3 Rc))| ≤ At / a0) →
    1 ≤ HR → (∀ i, |c₁' i| ≤ HR) → (∀ i k, |M₁' i k| ≤ HR) → |B'| ≤ HR →
    (∀ e, |Rc.coeff e| ≤ ZR) → 0 ≤ ZR → 1296 * ZR * (4 * HR) ^ 2 ≤ Z →
    A0 ^ (J + 1) ≤ Z → b0⁻¹ ≤ Z → 2 ≤ Av → Av ^ J * (Wmax + At * b0) ≤ Z →
    K * θ ^ (-C) * At ^ 28 ≤ A0 / 2 →
    At ^ (J + 9) * h * ((A0 ^ (J + 1)) ^ Cloc * a0) ≤ A0 * b0 →
    A0 ^ J * Vr * At ^ 9 * h ≤ A0 / 2 * (b0 / a0) →
    Av⁻¹ ≤ (mG / (A_R ^ q) ^ (3 * (1 + (Mexp + 1)) + 14)) / (β / ((A_R ^ q) ^ Mexp) ^ 3) →
    Av ^ J * (Vc / a0 + At ^ 4 * b0 / a0) ≤ Vr →
    Mz * Cloc + 2 * MH + 11 ≤ Mc → Z ≤ Nk ^ Mz →
    (∀ i, (A_R ^ q) ^ Mexp * (|c₁ i| + 1) ≤ Nk ^ MH) →
    (∀ i k, (A_R ^ q) ^ Mexp * |M₁ i k| ≤ Nk ^ MH) → |B (γ b)| ≤ Nk ^ MH →
    b0 = dyadicThickness Nk (r (lev b) + ag * L) →
    0 < η → η ≤ min ((2 : ℝ) ^ T (lev b) * τs) (1 / 2) →
    restorationRemezFactor η * (A0 ^ (J + 1)) ^ Cloc ≤ Nk ^ (ρ * gain * L + ε) →
    ENNReal.ofReal (Nk ^ (-((d₁ * ag + ρ * gain) * L) - ε) / (2 : ℝ) ^ T (lev b)) *
        ν (γ b) (Aset b) ≤
      ENNReal.ofReal (mG / (A_R ^ q) ^ (3 * (1 + (Mexp + 1)) + 14)) →
    RawSampledCandidate Cloc J (864 * (2 * (d + 1)) + 2) Nk L W ν B Mc d₁ ρ gain ε r T Cn lev
      γ j Aset H := by
  obtain ⟨Mexp, hMexp, K, C, hK, hC, hexit⟩ := sampled_exit_of_certified_group d hd
  obtain ⟨q, hq, hzoom⟩ := zoom_discriminant_conditions d
  refine ⟨Mexp, q, hMexp, hq, K, C, hK, hC, ?_⟩
  intro Cloc J hjet A_R hAR Nk L W ν B Mc d₁ ρ gain ε r T Cn lev γ j Aset H b ag hg hg8 hroom
    hBpos hνfin c₁ c₁' M₁ M₁' B' hM hc hB R0 Rc Pot hR0 hRc hPot σ εfit A₁ Vc hσ hA₁ hA₁R hsmall
    hcoeff Gev Wmax β mG τw Vmax hGm hmG hGev hdom hmass Mz MH A0 Z a0 b0 At θ h Vr η Av τs ZR HR
    hseven hA₁t hAtA0 hε hb0 hba ha1 hθ hθ1 hh hVr hVrA hWmax hVc hβ hV hτs hτsw hspeed hband
    hcurv hHR hc'H hM'H hB'H hZR hZR0 hSZ hAZ hbZ hAv hfZ hconst hsmall2 hsmall3 hvolμ hVcr
    hformat hZN hcN hMN hBN hb0eq hη hηmin hbudget hfloor
  set A := A_R ^ q with hAdef
  set lam := A ^ Mexp with hlamdef
  have hA2 : 2 ≤ A := hAR.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ A_R) hq)
  have hApos : 0 < A := by linarith
  have hlam : 0 < lam := pow_pos hApos Mexp
  have hlam1 : 1 ≤ lam := one_le_pow₀ (by linarith)
  -- the group measure and its localization
  set μ0 : Measure Event := (ν (γ b)).prod volume with hμ0
  set Zc : Event → Base := fun p => normalizedBase c₁ M₁ (B (γ b)) (graphPoint p.1 p.2) with hZcdef
  have hZc : Measurable Zc := measurable_eventBase _ _ _
  have hfin : μ0 Gev ≠ ⊤ := by
    have hsub : Gev ⊆ univ ×ˢ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) := fun p hp => ⟨mem_univ _, (hGev p hp).2.2.1⟩
    refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (by simp)
  have hbound : ∀ p ∈ Gev, Zc p ∈ ball (0 : Base) (A ^ 1) := by
    intro p hp
    have h1 := (hGev p hp).2.2.2.1
    rw [mem_closedBall, dist_zero_right] at h1
    rw [mem_ball, dist_zero_right, pow_one]
    linarith
  obtain ⟨ω₀, hω₀, hGzm, hGzmass, hGzdom, hGznorm⟩ := zoom_group_localization μ0 Zc hZc Gev hGm
    hfin hA2 1 (Mexp + 1) hlam hbound hmG hmass hdom
  set Gz := {ω | ω ∈ Gev ∧ Zc ω ∈ ball (Zc ω₀) (A ^ (Mexp + 1))⁻¹} with hGzdef
  -- the zoom centre
  set cz : Fin 3 → ℝ := fun i => Zc ω₀ i with hczdef
  have hczL : WithLp.toLp 2 cz = Zc ω₀ := rfl
  obtain ⟨hω₀H, hω₀A, hω₀t, hω₀ball, hω₀W, hω₀line⟩ := hGev ω₀ hω₀
  have hcz1 : WithLp.toLp 2 cz ∈ closedBall (0 : Base) 1 := hω₀ball
  have hczi : ∀ i, |cz i| ≤ 1 := by
    intro i
    have h1 := hω₀ball
    rw [mem_closedBall, dist_zero_right] at h1
    exact (PiLp.norm_apply_le (Zc ω₀) i).trans h1
  -- the zoomed normalization
  set cZ : Fin 3 → ℝ := zoomForwardShift c₁ cz lam with hcZ
  set MZ : Matrix (Fin 3) (Fin 3) ℝ := lam • M₁ with hMZ
  set cZ' : Fin 3 → ℝ := zoomShift c₁' M₁' cz with hcZ'
  set MZ' : Matrix (Fin 3) (Fin 3) ℝ := zoomMatrix M₁' lam with hMZ'
  obtain ⟨hMinvZ, hcinvZ⟩ := zoomForward_inverse hM hc cz hlam.ne'
  -- the cube group point at the centre
  have hx₀ := (hω₀line ω₀.2 (by simp; linarith)).1
  have hcube₀ := certifiedGroupPoint_of_physical hM hc hB hx₀
    (by
      have h1 := hω₀ball
      rw [mem_closedBall, dist_zero_right] at h1
      rw [mem_ball, dist_zero_right]
      exact lt_of_le_of_lt h1 (by norm_num))
  set Sx := transportPolynomial c₁' M₁' B' R0 with hSx
  set Px := basePullback c₁' M₁' Pot with hPx
  have hSxdeg : Sx.totalDegree ≤ 2 := (totalDegree_transportPolynomial_le _ _ _ _).trans hR0
  set w₀ := (pointOfCoordinates (coordinateMap c₁ M₁ (B (γ b)) (graphPoint ω₀.1 ω₀.2))).2
  have hz₀ : (pointOfCoordinates (coordinateMap c₁ M₁ (B (γ b)) (graphPoint ω₀.1 ω₀.2))).1 =
      WithLp.toLp 2 cz := rfl
  obtain ⟨⟨-, hfit₀, hsign₀, hlo₀, hhi₀⟩, -⟩ := hcube₀
  rw [hz₀] at hfit₀ hsign₀ hlo₀ hhi₀
  rw [native_equation Sx hSxdeg Px] at hfit₀
  rw [native_derivative Sx hSxdeg] at hsign₀ hlo₀ hhi₀
  obtain ⟨-, hσ0, hdisc, hcenter⟩ := hzoom Mexp A_R hAR c₁' M₁' B' cz R0 Pot hR0 hPot hd hczi σ
    A₁ εfit w₀ hA₁ hA₁R hsmall hcoeff hfit₀ hlo₀ hhi₀ hsign₀
  -- the seven directions at the centre
  obtain ⟨pd, E, hp, hdet, hEm, hEsub, hEvol, hwit⟩ := hseven cz hcz1 hGzmass
  -- zoomed base map and hidden value
  set Zz : Event → Base := fun x => zoomMap (Zc ω₀) lam (Zc x) with hZzdef
  set Wz : Event → ℝ := fun x => B (γ b) * graphPoint x.1 x.2 3 with hWzdef
  have hZzeq : ∀ (l : Line) (t : ℝ), normalizedBase cZ MZ (B (γ b)) (graphPoint l t) =
      zoomMap (Zc ω₀) lam (normalizedBase c₁ M₁ (B (γ b)) (graphPoint l t)) := by
    intro l t
    rw [hcZ, hMZ, normalizedBase_zoom]
  have hcalc : lam * (A ^ (Mexp + 1))⁻¹ = A⁻¹ := by
    rw [pow_succ, mul_inv, ← mul_assoc, hlamdef, mul_inv_cancel₀ (pow_ne_zero _ hApos.ne'),
      one_mul]
  have hAinv : A⁻¹ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hA2
  have hGzhalf : ∀ x ∈ Gz, ‖Zz x‖ < 1 / 2 := by
    intro x hx
    have h1 := hGznorm x hx
    rw [hcalc] at h1
    exact lt_of_lt_of_le h1 hAinv
  -- physical group points of `Gz` and nearby points of their lines are zoomed group points
  have hphysZ : ∀ (x : Fin 4 → ℝ), PhysicalGroupPoint B' R0 Rc Pot εfit A₁ σ Vc x →
      normalizedBase cZ MZ (B (γ b)) x ∈ closedBall (0 : Base) 1 →
      CertifiedNativeGroupPoint cZ MZ (B (γ b)) (transportPolynomial cZ' MZ' B' R0)
        (basePullback cZ' MZ' Pot) (transportPolynomial cZ' MZ' B' Rc) εfit A₁ σ x :=
    fun x hx hball => certifiedNativeGroupPoint_of_physical hMinvZ hcinvZ hB hx hball
  -- the numerics in zoomed coordinates
  have hlamne : lam ≠ 0 := hlam.ne'
  have hsmallZ : 4 * |nativeA (transportPolynomial cZ' MZ' B' R0)| * εfit ≤ (2 * A₁ ^ 2)⁻¹ := by
    rw [hcZ', hMZ', (zoom_native_coefficients c₁' M₁' B' cz hlamne R0 hR0 Pot).1]
    exact hsmall
  have hcurvZ : ∀ (z : Base) (w : ℝ), |eval ![z 0, z 1, z 2, w]
      (pderiv 3 (pderiv 3 (transportPolynomial cZ' MZ' B' Rc)))| ≤ At / a0 := by
    intro z w
    rw [(eval_transport_hidden_derivatives cZ' MZ' B' Rc _).2]
    exact hcurv _
  have hcZ'b : ∀ i, |cZ' i| ≤ 4 * HR := by
    intro i
    have hterm : ∀ k, |M₁' i k * cz k| ≤ HR := by
      intro k
      rw [abs_mul]
      calc |M₁' i k| * |cz k| ≤ HR * 1 :=
            mul_le_mul (hM'H i k) (hczi k) (abs_nonneg _) (by linarith)
        _ = HR := mul_one _
    simp only [hcZ', zoomShift, Fin.sum_univ_three]
    calc |c₁' i + (M₁' i 0 * cz 0 + M₁' i 1 * cz 1 + M₁' i 2 * cz 2)|
        ≤ |c₁' i| + (|M₁' i 0 * cz 0| + |M₁' i 1 * cz 1| + |M₁' i 2 * cz 2|) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ HR + (HR + HR + HR) := by gcongr <;> first | exact hc'H i | exact hterm _
      _ = 4 * HR := by ring
  have hMZ'b : ∀ i k, |MZ' i k| ≤ 4 * HR := by
    intro i k
    simp only [hMZ', zoomMatrix, Matrix.smul_apply, smul_eq_mul, abs_mul]
    have hli : |lam⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.mpr hlam)]; exact inv_le_one_of_one_le₀ hlam1
    calc |lam⁻¹| * |M₁' i k| ≤ 1 * HR :=
          mul_le_mul hli (hM'H i k) (abs_nonneg _) zero_le_one
      _ ≤ 4 * HR := by linarith
  have hSZZ : ∀ e, |(transportPolynomial cZ' MZ' B' Rc).coeff e| ≤ Z := by
    intro e
    exact (transportPolynomial_coeff_bound cZ' MZ' B' Rc (by linarith) hZR0 hcZ'b hMZ'b
      (by linarith) hRc hZR e).trans hSZ
  have hcNZ : ∀ i, |cZ i| ≤ Nk ^ MH := by
    intro i
    simp only [hcZ, zoomForwardShift, abs_mul, abs_of_pos hlam]
    refine le_trans ?_ (hcN i)
    apply mul_le_mul_of_nonneg_left _ hlam.le
    calc |c₁ i - cz i| ≤ |c₁ i| + |cz i| := abs_sub _ _
      _ ≤ |c₁ i| + 1 := by linarith [hczi i]
  have hMNZ : ∀ i k, |MZ i k| ≤ Nk ^ MH := by
    intro i k
    simp only [hMZ, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hlam]
    exact hMN i k
  -- the dominated group measure in zoomed coordinates
  have hanchor : ∀ᵐ x ∂(μ0.restrict Gz), Zz x ∈ closedBall (0 : Base) 1 ∧
      CertifiedGroupPoint (transportPolynomial cZ' MZ' B' R0) (basePullback cZ' MZ' Pot)
        (transportPolynomial cZ' MZ' B' Rc) εfit A₁ σ Vc (Zz x) (Wz x) ∧ |Wz x| ≤ Wmax := by
    refine (ae_restrict_iff' hGzm).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    obtain ⟨-, -, -, -, hxW, hxline⟩ := hGev x hx.1
    have hxphys := (hxline x.2 (by simp; linarith)).1
    have hnorm := hGzhalf x hx
    have hZzx : (pointOfCoordinates (coordinateMap cZ MZ (B (γ b)) (graphPoint x.1 x.2))).1 =
        Zz x := hZzeq x.1 x.2
    have hWzx : (pointOfCoordinates (coordinateMap cZ MZ (B (γ b)) (graphPoint x.1 x.2))).2 =
        Wz x := rfl
    have hcg := certifiedGroupPoint_of_physical hMinvZ hcinvZ hB hxphys
      (by rw [hZzx, mem_ball, dist_zero_right]; linarith)
    rw [hZzx, hWzx] at hcg
    refine ⟨?_, hcg, hxW⟩
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hdomμ : ∀ U : Set Base, MeasurableSet U →
      (μ0.restrict Gz) (Zz ⁻¹' U) ≤ ENNReal.ofReal (β / lam ^ 3) * volume U := by
    intro U hU
    rw [Measure.restrict_apply' hGzm]
    exact hGzdom U hU
  have hmμ : ENNReal.ofReal (mG / A ^ (3 * (1 + (Mexp + 1)) + 14)) ≤ (μ0.restrict Gz) univ := by
    rw [Measure.restrict_apply_univ]
    exact hGzmass
  -- the frozen lines, their witness times and the counted incidences
  set A' : Set Line := {l | 0 < volume (Prod.mk l ⁻¹' Gz)} with hA'def
  have hA'm : MeasurableSet A' :=
    measurableSet_lt measurable_const (measurable_measure_prodMk_left hGzm)
  have hA'nonempty : ∀ l ∈ A', ∃ t, (l, t) ∈ Gz := by
    intro l hl
    exact nonempty_of_measure_ne_zero (ne_of_gt hl)
  have hA'b : A' ⊆ Aset b := by
    intro l hl
    obtain ⟨t, ht⟩ := hA'nonempty l hl
    exact (hGev (l, t) ht.1).2.1
  set S : Line → Set ℝ := fun l => {tn | tn ∈ Icc (0 : ℝ) 1 ∧
    CertifiedNativeGroupPoint cZ MZ (B (γ b)) (transportPolynomial cZ' MZ' B' R0)
      (basePullback cZ' MZ' Pot) (transportPolynomial cZ' MZ' B' Rc) εfit A₁ σ
      (graphPoint l ((j b : ℝ) / (2 : ℝ) ^ T (lev b) + ((2 : ℝ) ^ T (lev b))⁻¹ * tn))}
    with hSdef
  have hT : (0 : ℝ) < (2 : ℝ) ^ T (lev b) := by positivity
  have hS : ∀ l ∈ A', S l ⊆ Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (S l) := by
    intro l hl
    refine ⟨fun t ht => ht.1, ?_⟩
    obtain ⟨t₀, ht₀⟩ := hA'nonempty l hl
    obtain ⟨-, -, ht₀w, -, -, hline⟩ := hGev (l, t₀) ht₀.1
    have hnorm₀ := hGzhalf (l, t₀) ht₀
    set tn₀ := (2 : ℝ) ^ T (lev b) * t₀ - j b with htn₀
    have htn₀I : tn₀ ∈ Icc (0 : ℝ) 1 := by
      obtain ⟨h1, h2⟩ := ht₀w
      constructor
      · have := (div_le_iff₀ hT).mp h1
        rw [htn₀]; linarith
      · have := (le_div_iff₀ hT).mp h2
        rw [htn₀]; linarith
    have hsub : {tn | |tn - tn₀| ≤ (2 : ℝ) ^ T (lev b) * τs} ∩ Icc (0 : ℝ) 1 ⊆ S l := by
      intro tn htn
      refine ⟨htn.2, ?_⟩
      set t := (j b : ℝ) / (2 : ℝ) ^ T (lev b) + ((2 : ℝ) ^ T (lev b))⁻¹ * tn with htdef
      have hdiff : t - t₀ = ((2 : ℝ) ^ T (lev b))⁻¹ * (tn - tn₀) := by
        rw [htdef, htn₀]; field_simp; ring
      have htt : |t - t₀| ≤ τs := by
        rw [hdiff, abs_mul, abs_of_pos (inv_pos.mpr hT)]
        calc ((2 : ℝ) ^ T (lev b))⁻¹ * |tn - tn₀|
            ≤ ((2 : ℝ) ^ T (lev b))⁻¹ * ((2 : ℝ) ^ T (lev b) * τs) :=
              mul_le_mul_of_nonneg_left htn.1 (inv_nonneg.mpr hT.le)
          _ = τs := by field_simp
      obtain ⟨hphys, hmove⟩ := hline t (htt.trans hτsw)
      apply hphysZ _ hphys
      rw [hZzeq, mem_closedBall, dist_zero_right]
      have hsplit : zoomMap (Zc ω₀) lam (normalizedBase c₁ M₁ (B (γ b)) (graphPoint l t)) =
          Zz (l, t₀) + lam • (normalizedBase c₁ M₁ (B (γ b)) (graphPoint l t) -
            normalizedBase c₁ M₁ (B (γ b)) (graphPoint l t₀)) := by
        simp only [hZzdef, hZcdef, zoomMap]
        rw [← smul_add]
        congr 1
        abel
      rw [hsplit]
      calc ‖Zz (l, t₀) + lam • (normalizedBase c₁ M₁ (B (γ b)) (graphPoint l t) -
            normalizedBase c₁ M₁ (B (γ b)) (graphPoint l t₀))‖
          ≤ ‖Zz (l, t₀)‖ + lam * (Vmax * |t - t₀|) := by
            refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
            exact mul_le_mul_of_nonneg_left hmove hlam.le
        _ ≤ 1 / 2 + lam * Vmax * τs := by
            have : lam * (Vmax * |t - t₀|) ≤ lam * Vmax * τs := by
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_left htt (mul_nonneg hlam.le hV)
            linarith
        _ ≤ 1 := by linarith
    calc ENNReal.ofReal η ≤ ENNReal.ofReal (min ((2 : ℝ) ^ T (lev b) * τs) (1 / 2)) :=
          ENNReal.ofReal_le_ofReal hηmin
      _ ≤ volume ({tn | |tn - tn₀| ≤ (2 : ℝ) ^ T (lev b) * τs} ∩ Icc (0 : ℝ) 1) :=
          volume_near_inter_unit htn₀I (mul_nonneg hT.le hτs)
      _ ≤ volume (S l) := measure_mono hsub
  have hgp : ∀ l ∈ A', ∀ t ∈ S l, CertifiedNativeGroupPoint cZ MZ (B (γ b))
      (transportPolynomial cZ' MZ' B' R0) (basePullback cZ' MZ' Pot)
      (transportPolynomial cZ' MZ' B' Rc) εfit A₁ σ
      (graphPoint l ((j b : ℝ) / (2 : ℝ) ^ T (lev b) + ((2 : ℝ) ^ T (lev b))⁻¹ * t)) :=
    fun l _ t ht => ht.2
  set counted : Set Event := Gz ∩ (A' ×ˢ univ) with hcounteddef
  have hcounted : counted ⊆ {x | x ∈ H (γ b) ∧ x.1 ∈ A' ∧
      x.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b)) ∧
      CertifiedNativeGroupPoint cZ MZ (B (γ b)) (transportPolynomial cZ' MZ' B' R0)
        (basePullback cZ' MZ' Pot) (transportPolynomial cZ' MZ' B' Rc) εfit A₁ σ
        (graphPoint x.1 x.2)} := by
    intro x hx
    obtain ⟨hxH, -, hxw, -, -, hxline⟩ := hGev x hx.1.1
    refine ⟨hxH, hx.2.1, hxw, hphysZ _ (hxline x.2 (by simp; linarith)).1 ?_⟩
    rw [hZzeq, mem_closedBall, dist_zero_right]
    exact (hGzhalf x hx.1).le.trans (by norm_num)
  have hmass' : ENNReal.ofReal (Nk ^ (-((d₁ * ag + ρ * gain) * L) - ε) /
      (2 : ℝ) ^ T (lev b)) * ν (γ b) (Aset b) ≤ ((ν (γ b)).prod volume) counted := by
    rw [hcounteddef, prod_measure_inter_posSlices (ν (γ b)) hGzm]
    exact hfloor.trans hGzmass
  exact hexit Cloc J hjet A hA2 b ag hg hg8 hroom hBpos cZ cZ' MZ MZ' B' hMinvZ hcinvZ hB R0 Rc
    Pot hR0 hRc hPot σ hσ hσ0 hdisc hcenter Mz MH A0 Z a0 b0 At θ h Vr εfit A₁ Wmax η Vc pd E
    hA₁ hA₁t hAtA0 hε hb0 hba ha1 hθ hθ1 hh hVr hVrA hWmax hsmallZ hband hcurvZ hSZZ hAZ hbZ
    Av hAv hfZ hconst hsmall2 hsmall3 hp hdet hEm hEsub hEvol (μ0.restrict Gz) Zz Wz
    (mG / A ^ (3 * (1 + (Mexp + 1)) + 14)) (β / lam ^ 3) (by positivity) hmμ hdomμ hvolμ
    hanchor hVc hVcr hwit hformat hZN hcNZ hMNZ hBN hb0eq hη (hηmin.trans (min_le_right _ _)
      |>.trans (by norm_num)) hbudget A' hA'm hA'b S hS hgp counted hcounted hmass'

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
