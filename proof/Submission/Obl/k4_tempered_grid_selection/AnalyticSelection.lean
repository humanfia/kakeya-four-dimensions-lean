import Submission.Obl.k4_tempered_grid_selection.SelectionSequence
import Submission.Obl.k4_tempered_grid_selection.SelectionMass
import Submission.Obl.k4_tempered_grid_selection.BandTransfer
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_tempered_grid_selection

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Select whole common-label types with subpower mass loss and bounded,
typical density exponents on the clamped rational grid. -/
theorem analytic_selection (N K : ℕ → ℝ)
    (ν : ℕ → Measure (ℕ × (Fin 6 → ℝ))) (E : ℕ → Set Incidence)
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop) (hK : Subpower N K)
    (hE : ∀ k, MeasurableSet (E k))
    (hmass : ∀ k, incidenceMeasure (ν k) (E k) univ ≤ 1)
    (hlower : ∀ k, ENNReal.ofReal (K k)⁻¹ ≤ incidenceMeasure (ν k) (E k) univ)
    (R U : ℝ) (hR : 0 < R) (hU : 0 < U)
    (hac : AbsoluteContinuity N ν E R U)
    (C H : ℕ) (g : ℕ → ℝ → ℝ → Label → ℝ)
    (happrox : Approximation N (fun k => incidenceMeasure (ν k) (E k)) R U C H g) :
    ∃ (K₀ : ℕ → ℝ) (T : ℕ → Set Label) (a : ℕ → ℚ → ℚ → ℝ),
      Subpower N K₀ ∧ (∀ k, K k ≤ K₀ k) ∧
      (∀ k, ENNReal.ofReal (K₀ k)⁻¹ ≤
        incidenceMeasure (ν k) (E k ∩ commonLabel (N k) H R U ⁻¹' T k) univ) ∧
      (∀ k q s, |a k q s| ≤ (C : ℝ)) ∧
      GridTypical N (fun k =>
        incidenceMeasure (ν k) (E k ∩ commonLabel (N k) H R U ⁻¹' T k)) R U a := by
  classical
  letI : SigmaFinite refMeasure := by unfold refMeasure; infer_instance
  obtain ⟨e, he⟩ := exists_surjective_nat (ℚ × ℚ)
  choose index hindex using he
  let f (k j : ℕ) (z : Label) : ℝ :=
    boundedExponent (C : ℝ) (N k) (g k (clamp R (e j).1) (clamp U (e j).2) z)
  obtain ⟨B, T, a', δ, hB, hBsub, ha', hδpos, hδ, hfit, hretain⟩ :=
    countable_type_selection N hN hNt (fun k => incidenceMeasure (ν k) (E k))
      (fun k => commonLabel (N k) H R U) f (C : ℝ) (Nat.cast_nonneg C)
      (fun k j z => abs_boundedExponent _ _ _ (Nat.cast_nonneg C))
  let K₀ (k : ℕ) : ℝ := K k * (B k : ℝ)
  let a (k : ℕ) (q s : ℚ) : ℝ := a' k (index (q, s))
  refine ⟨K₀, T, a, subpower_mul (fun k => by linarith [hN k]) hK hBsub,
    ?_, ?_, (fun k q s => ha' k (index (q, s))), ?_⟩
  · intro k
    have hb : (1 : ℝ) ≤ B k := by exact_mod_cast Nat.succ_le_iff.mpr (hB k)
    dsimp [K₀]
    nlinarith [hK.1 k]
  · intro k
    apply inverse_mass_after_finite_loss (by linarith [hK.1 k]) (hB k) (hlower k)
    rw [← incidence_selection_mass]
    exact hretain k
  · intro q s τ hτ
    let d : ℝ := min 1 (τ / 4)
    let c : ℝ := d / 2
    have hd : 0 < d := lt_min (by norm_num) (by linarith)
    have hc : 0 < c := by dsimp [c]; positivity
    have hsmall : ∀ᶠ k in atTop, 2 * N k ^ (-d) < N k ^ (-c) :=
      k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt (by dsimp [c]; linarith) 2
    have herr : ∀ᶠ k in atTop,
        N k ^ (-1 : ℝ) + N k ^ (-(τ / 4)) ≤ N k ^ (-c) := by
      filter_upwards [hsmall] with k hk
      have hn1 : 1 ≤ N k := by linarith [hN k]
      have h1 : N k ^ (-1 : ℝ) ≤ N k ^ (-d) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [d]; linarith [min_le_left (1 : ℝ) (τ / 4)])
      have h2 : N k ^ (-(τ / 4)) ≤ N k ^ (-d) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [d]; linarith [min_le_right (1 : ℝ) (τ / 4)])
      linarith
    have hδτ : ∀ᶠ k in atTop, δ k < τ / 4 :=
      hδ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < τ / 4))
    have hfactor : ∀ᶠ k in atTop, 2 ≤ N k ^ (τ / 4) :=
      ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < τ / 4)).comp hNt).eventually
        (eventually_ge_atTop 2)
    refine ⟨c, hc, ?_⟩
    filter_upwards [hfit (index (q, s)), hδτ, hfactor, herr] with k hkfit hkδ hkfactor hkerr
    intro G₀ hG₀ hlaw₀
    have hr := clamp_mem hR.le q
    have hu := clamp_mem hU.le s
    obtain ⟨G, hG, hlaw⟩ := hac k (E k) (hE k) Subset.rfl
      (clamp R q) (clamp U s) hr.1 hr.2 hu.1 hu.2
    let μ := incidenceMeasure (ν k) (E k)
    let μ₀ := incidenceMeasure (ν k) (E k ∩ commonLabel (N k) H R U ⁻¹' T k)
    have hfit₀ : ∀ᵐ p ∂μ₀,
        |boundedExponent (C : ℝ) (N k)
          (g k (clamp R q) (clamp U s) (commonLabel (N k) H R U p)) - a k q s| ≤ δ k := by
      filter_upwards [ae_restrict_mem (measurable_label_selection (N k) H R U (hE k) (T k))]
        with p hp
      simpa only [f, hindex, a] using
        (hkfit (commonLabel (N k) H R U p) hp.2).le
    have hv (p : Incidence) :
        0 ≤ g k (clamp R q) (clamp U s) (commonLabel (N k) H R U p) ∧
        g k (clamp R q) (clamp U s) (commonLabel (N k) H R U p) ≤ N k ^ (C : ℝ) := by
      simpa only [Real.rpow_natCast] using
        happrox.1 k _ _ hr.1 hr.2 hu.1 hu.2 (commonLabel (N k) H R U p)
    have hbound := approximation_band_transfer refMeasure μ μ₀
      (incidence_selection_le (ν k) (E k) (N k) H R U (T k)) (hmass k)
      (observation (N k) (clamp R q) (clamp U s)) (measurable_observation _ _ _)
      G G₀ hG hG₀ hlaw hlaw₀ (N k) (C : ℝ) (a k q s) (δ k) τ
      (by linarith [hN k]) hτ hkδ.le hkfactor
      (fun p => g k (clamp R q) (clamp U s) (commonLabel (N k) H R U p)) hv hfit₀
      (ENNReal.ofReal (N k ^ (-1 : ℝ)))
      (happrox.2 k _ _ hr.1 hr.2 hu.1 hu.2 G hG hlaw)
    apply hbound.trans
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg (by linarith [hN k]) _)
      (Real.rpow_nonneg (by linarith [hN k]) _)]
    exact ENNReal.ofReal_le_ofReal hkerr

end Submission.Obl.k4_tempered_grid_selection
