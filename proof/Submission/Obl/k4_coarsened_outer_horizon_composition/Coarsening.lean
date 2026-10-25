import Submission.Obl.k4_coarsened_outer_horizon_composition.Observations
import Submission.Obl.k4_coarsened_outer_horizon_composition.AngularTail
import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_native_grid_profile_extension.Profiles

set_option linter.unusedVariables false

/-- Restrict the depth interval, change its endpoint cap, and construct all the
angular densities at the new endpoint. The pure densities are unchanged. -/
theorem coarsened_problem
    {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure Line}
    {E : (k : ℕ) → Fin (W k) → Set Inc}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → Obs → ℝ≥0∞}
    {G : (k : ℕ) → Fin (W k) → ℝ → Joint → ℝ≥0∞}
    (hp : prob N K L d S η W ω ν E P B f g G)
    {r q : ℝ} (hr : 0 < r) (hrL : r ≤ L) (hq : 0 < q) (hq1 : q < 1)
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ r → f r - f s ≤ q * (r - s)) :
    ∃ G₂, prob N K r q S η W ω ν E P B f g G₂ := by
  classical
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hrest⟩
  rcases hrest with ⟨hformat, hpure, hangular, hreg, htyp, hcapOld, hang⟩
  let μ : (k : ℕ) → Fin (W k) → Measure Inc := fun k γ => selected (ν k γ) (E k γ)
  have hfinite (k : ℕ) (γ : Fin (W k)) : IsFiniteMeasure (μ k γ) := by
    obtain ⟨M, D, hfmt⟩ := hformat
    letI : IsProbabilityMeasure (ν k γ) := ((hfmt k).2.2.2.1 γ).1
    exact Submission.Obl.k4_dyadic_crop_affine_laws.Framework.finite_selected_incidence
      (ν k γ) (E k γ) ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.1
  have hex : ∀ (k : ℕ) (γ : Fin (W k)) (u : ℝ),
      ∃ G₂ : Joint → ℝ≥0∞, Measurable G₂ ∧
        (μ k γ).map (joint (B k γ) (N k) r u) =
          ((volume.prod Measure.count).prod Measure.count).withDensity G₂ := by
    intro k γ u
    letI := hfinite k γ
    exact exists_joint_density (μ k γ) (B k γ) (N k) r u
      (g k γ r) (hpure k γ r hr.le hrL).1 (hpure k γ r hr.le hrL).2
  choose G₂ hG₂ hG₂law using hex
  refine ⟨G₂, hN, hNt, hK, hr, hq, hq1, hS, hη, ?_⟩
  refine ⟨hformat, ?_, ?_, ?_, ?_, hcap, ?_⟩
  · intro k γ s hs hsr
    exact hpure k γ s hs (hsr.trans hrL)
  · intro k γ u hu hur
    exact ⟨hG₂ k γ u, hG₂law k γ u⟩
  · intro s t hs hst htr
    exact hreg s t hs hst (htr.trans hrL)
  · intro s τ hs hsr hτ
    exact htyp s τ hs (hsr.trans hrL) hτ
  · intro u τ hu hur hτ
    have huL : u ≤ η * L := hur.trans (mul_le_mul_of_nonneg_left hrL hη.le)
    have hτ8 : 0 < τ / 8 := by positivity
    have hτ4 : 0 < τ / 4 := by positivity
    let A : ℕ → ℝ≥0∞ := fun k => ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ)
      {p | g k γ r (obs (B k γ) (δ (N k) r) p) < ENNReal.ofReal (N k ^ (-f r - τ / 4)) ∨
        ENNReal.ofReal (N k ^ (-f r + τ / 4)) < g k γ r (obs (B k γ) (δ (N k) r) p)}
    let C : ℕ → ℝ≥0∞ := fun k => ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ)
      {p | g k γ L (obs (B k γ) (δ (N k) L) p) < ENNReal.ofReal (N k ^ (-f L - τ / 8)) ∨
        ENNReal.ofReal (N k ^ (-f L + τ / 8)) < g k γ L (obs (B k γ) (δ (N k) L) p)}
    let D : ℕ → ℝ≥0∞ := fun k => ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ)
      {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ / 8)) < G k γ u (joint (B k γ) (N k) L u p)}
    have hA : IsPowerSmall N A := htyp r (τ / 4) hr.le hrL hτ4
    have hC : IsPowerSmall N C := htyp L (τ / 8) hL.le le_rfl hτ8
    have hD : IsPowerSmall N D := hang u (τ / 8) hu huL hτ8
    have hsmall := hA.add hNt ((hC.add hNt hD).add hNt (hC.add hNt hD))
    apply hsmall.mono
    have hnum := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
      hNt (a := -f r - S * u + τ / 2) (b := -f r - S * u + τ) (by linarith) 2
    filter_upwards [hnum] with k hnumk
    have hNk : 0 < N k := by linarith [hN k]
    have hNk1 : 1 ≤ N k := by linarith [hN k]
    let lo := ENNReal.ofReal (N k ^ (-f L - τ / 8))
    let hi := ENNReal.ofReal (N k ^ (-f L - S * u + τ / 8))
    let c := ENNReal.ofReal (N k ^ (-S * u + τ / 4))
    have hscale : hi ≤ c * lo := by
      dsimp [hi, c, lo]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hNk.le _), ← Real.rpow_add hNk]
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_exponent_le hNk1 (by linarith)
    have hthreshold : 2 * c * ENNReal.ofReal (N k ^ (-f r + τ / 4)) ≤
        ENNReal.ofReal (N k ^ (-f r - S * u + τ)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
      dsimp [c]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * N k ^ (-S * u + τ / 4))]
      apply ENNReal.ofReal_le_ofReal
      calc
        2 * N k ^ (-S * u + τ / 4) * N k ^ (-f r + τ / 4) =
            2 * N k ^ (-f r - S * u + τ / 2) := by
          rw [mul_assoc, ← Real.rpow_add hNk]
          congr 2
          ring
        _ ≤ _ := hnumk.le
    have hworld (γ : Fin (W k)) :
        (μ k γ) {p | ENNReal.ofReal (N k ^ (-f r - S * u + τ)) <
          G₂ k γ u (joint (B k γ) (N k) r u p)} ≤
        (μ k γ) {p | g k γ r (obs (B k γ) (δ (N k) r) p) < ENNReal.ofReal (N k ^ (-f r - τ / 4)) ∨
          ENNReal.ofReal (N k ^ (-f r + τ / 4)) < g k γ r (obs (B k γ) (δ (N k) r) p)} +
        2 * ((μ k γ) {p | g k γ L (obs (B k γ) (δ (N k) L) p) < ENNReal.ofReal (N k ^ (-f L - τ / 8)) ∨
          ENNReal.ofReal (N k ^ (-f L + τ / 8)) < g k γ L (obs (B k γ) (δ (N k) L) p)} +
        (μ k γ) {p | hi < G k γ u (joint (B k γ) (N k) L u p)}) := by
      letI := hfinite k γ
      let qmap := Submission.Lib.K4Homogenization.coarsenObservation (X := E3) (N k) r L
      have hqmap : Measurable qmap := Submission.Lib.K4Homogenization.measurable_coarsenObservation _ _ _
      have heq : qmap ∘ obs (B k γ) (δ (N k) L) = obs (B k γ) (δ (N k) r) :=
        (obs_factorization hNk1 hrL (B k γ)).symm
      have hcoarseLaw : (μ k γ).map (qmap ∘ obs (B k γ) (δ (N k) L)) =
          (volume.prod Measure.count).withDensity (g k γ r) := by
        rw [heq]
        exact (hpure k γ r hr.le hrL).2
      have hjointLaw : (μ k γ).map
          (fun p => (qmap (obs (B k γ) (δ (N k) L) p), ang (N k) u p)) =
          ((volume.prod Measure.count).prod Measure.count).withDensity (G₂ k γ u) := by
        have hfun : (fun p => (qmap (obs (B k γ) (δ (N k) L) p), ang (N k) u p)) =
            joint (B k γ) (N k) r u := by
          funext p
          exact congrArg (fun z => (z, ang (N k) u p)) (congrFun heq p)
        rw [hfun]
        exact hG₂law k γ u
      have htail := coarsened_angular_tail (μ k γ)
        (volume.prod Measure.count) (volume.prod Measure.count)
        (obs (B k γ) (δ (N k) L)) (measurable_obs _ _) (ang (N k) u) (measurable_ang _ _)
        qmap hqmap (g k γ L) (hpure k γ L hL.le le_rfl).1
        (g k γ r) (hpure k γ r hr.le hrL).1 (G k γ u) (hangular k γ u hu huL).1
        (G₂ k γ u) (hG₂ k γ u) (hpure k γ L hL.le le_rfl).2 hcoarseLaw
        (hangular k γ u hu huL).2 hjointLaw lo hi c hscale
      have hqobs (p : Inc) : qmap (obs (B k γ) (δ (N k) L) p) =
          obs (B k γ) (δ (N k) r) p := congrFun heq p
      simp only [hqobs] at htail
      let badPure : Set Inc := {p | g k γ L (obs (B k γ) (δ (N k) L) p) < ENNReal.ofReal (N k ^ (-f L - τ / 8)) ∨
        ENNReal.ofReal (N k ^ (-f L + τ / 8)) < g k γ L (obs (B k γ) (δ (N k) L) p)}
      let badJoint : Set Inc := {p | hi < G k γ u (joint (B k γ) (N k) L u p)}
      have hbad : (μ k γ) {p | g k γ L (obs (B k γ) (δ (N k) L) p) < lo ∨
          hi < G k γ u (joint (B k γ) (N k) L u p)} ≤ (μ k γ) badPure + (μ k γ) badJoint := by
        calc
          _ ≤ (μ k γ) (badPure ∪ badJoint) := by
            apply measure_mono
            intro p hp
            rcases hp with hp | hp
            · exact Or.inl (Or.inl hp)
            · exact Or.inr hp
          _ ≤ _ := measure_union_le _ _
      calc
        _ ≤ (μ k γ) ({p | g k γ r (obs (B k γ) (δ (N k) r) p) < ENNReal.ofReal (N k ^ (-f r - τ / 4)) ∨
              ENNReal.ofReal (N k ^ (-f r + τ / 4)) < g k γ r (obs (B k γ) (δ (N k) r) p)} ∪
            {p | 2 * c * g k γ r (obs (B k γ) (δ (N k) r) p) < G₂ k γ u (joint (B k γ) (N k) r u p)}) := by
          apply measure_mono
          intro p hp
          by_cases hhigh : ENNReal.ofReal (N k ^ (-f r + τ / 4)) < g k γ r (obs (B k γ) (δ (N k) r) p)
          · exact Or.inl (Or.inr hhigh)
          · exact Or.inr ((lt_of_le_of_lt ((mul_le_mul (le_refl (2 * c))
              (le_of_not_gt hhigh) zero_le zero_le).trans hthreshold) hp))
        _ ≤ (μ k γ) {p | g k γ r (obs (B k γ) (δ (N k) r) p) < ENNReal.ofReal (N k ^ (-f r - τ / 4)) ∨
              ENNReal.ofReal (N k ^ (-f r + τ / 4)) < g k γ r (obs (B k γ) (δ (N k) r) p)} +
            (μ k γ) {p | 2 * c * g k γ r (obs (B k γ) (δ (N k) r) p) < G₂ k γ u (joint (B k γ) (N k) r u p)} :=
          measure_union_le _ _
        _ ≤ (μ k γ) {p | g k γ r (obs (B k γ) (δ (N k) r) p) < ENNReal.ofReal (N k ^ (-f r - τ / 4)) ∨
              ENNReal.ofReal (N k ^ (-f r + τ / 4)) < g k γ r (obs (B k γ) (δ (N k) r) p)} +
            2 * (μ k γ) {p | g k γ L (obs (B k γ) (δ (N k) L) p) < lo ∨
              hi < G k γ u (joint (B k γ) (N k) L u p)} := add_le_add (le_refl _) htail
        _ ≤ _ := add_le_add (le_refl _) (mul_le_mul (le_refl 2) hbad zero_le zero_le)
    calc
      _ ≤ ∑ γ, ENNReal.ofReal (ω k γ) *
          ((μ k γ) {p | g k γ r (obs (B k γ) (δ (N k) r) p) < ENNReal.ofReal (N k ^ (-f r - τ / 4)) ∨
            ENNReal.ofReal (N k ^ (-f r + τ / 4)) < g k γ r (obs (B k γ) (δ (N k) r) p)} +
          2 * ((μ k γ) {p | g k γ L (obs (B k γ) (δ (N k) L) p) < ENNReal.ofReal (N k ^ (-f L - τ / 8)) ∨
            ENNReal.ofReal (N k ^ (-f L + τ / 8)) < g k γ L (obs (B k γ) (δ (N k) L) p)} +
          (μ k γ) {p | hi < G k γ u (joint (B k γ) (N k) L u p)})) :=
        Finset.sum_le_sum fun γ _ => mul_le_mul (le_refl _) (hworld γ) zero_le zero_le
      _ = A k + (C k + D k + (C k + D k)) := by
        have hmul (w a b c : ℝ≥0∞) : w * (a + 2 * (b + c)) =
            w * a + 2 * (w * b + w * c) := by ring
        simp_rw [hmul]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
        change A k + 2 * (C k + D k) = _
        ring

end Submission.Obl.k4_coarsened_outer_horizon_composition
