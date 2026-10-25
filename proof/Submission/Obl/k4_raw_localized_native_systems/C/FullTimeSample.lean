import Submission.Obl.k4_raw_localized_native_systems.C.FullTimeLocalization
import Submission.Obl.k4_raw_localized_native_systems.C.PathCoverage
import Submission.Obl.k4_raw_localized_native_systems.C.ShortLabels

/-
Adapted from this LOT tree, o178, session x0596, `FullTimeSample.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Full-time localization at one sample, from the coverage of the chart system

The weighted good-path mass is at least the coverage `κ⁻¹` of the chart
system minus the exceptional mass (angular-cap and typicality failures and
short-axis charts).  Combined with `full_time_localization`, the retained mass
of the full-time strips is at least `(κ⁻¹ - E)² / 4` minus the bad-pair bound.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

theorem worldMass_eq (a : Atlas p k) (γ : Fin (p.W k)) (u τ κ' lam : ℝ) :
    worldMass a γ u τ κ' lam = (((p.ν k γ).prod volume) (goodPath a γ u τ κ' lam)).toReal := by
  unfold worldMass
  rw [measureReal_def, Measure.restrict_apply_univ]

/-- The weighted good-path mass is at least coverage minus exceptional mass. -/
theorem weighted_goodMass_ge {M D : ℕ} {κ r : ℝ} (hp : Valid p) (a : Atlas p k)
    {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    {u τ κ' lam E : ℝ} (hK : p.K k ≤ κ') (hE : 0 ≤ E) (hκ : 0 < κ)
    (hcov : ENNReal.ofReal κ⁻¹ ≤
      ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b))
    (hexc : ∑ γ, ENNReal.ofReal (p.ω k γ) * (selected p k γ (angFail p k γ u τ) +
      selected p k γ (typFail p k γ p.L τ) + selected p k γ (typFail p k γ 0 τ) +
        selected p k γ (shortPath a γ u τ lam)) ≤ ENNReal.ofReal E) :
    κ⁻¹ - E ≤ ∑ γ, p.ω k γ * worldMass a γ u τ κ' lam := by
  classical
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hω0 : ∀ γ, 0 ≤ p.ω k γ := (hfmt k).2.1
  have hprob : ∀ γ, IsProbabilityMeasure (p.ν k γ) := fun γ => ((hfmt k).2.2.2.1 γ).1
  have hgoodfin : ∀ γ, ((p.ν k γ).prod volume) (goodPath a γ u τ κ' lam) ≠ ⊤ := by
    intro γ
    haveI := hprob γ
    refine ne_top_of_le_ne_top (b := ((p.ν k γ).prod volume) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)) ?_
      (measure_mono (goodPath_subset_unit hp a γ hc))
    rw [Measure.prod_prod, Real.volume_Icc]
    simp
  -- the ENNReal inequality, summed over worlds
  have hsum : ∑ γ, ENNReal.ofReal (p.ω k γ) * ((p.ν k γ).prod volume) (fullPath a γ) ≤
      ∑ γ, ENNReal.ofReal (p.ω k γ) * ((p.ν k γ).prod volume) (goodPath a γ u τ κ' lam) +
        ENNReal.ofReal E := by
    calc ∑ γ, ENNReal.ofReal (p.ω k γ) * ((p.ν k γ).prod volume) (fullPath a γ)
        ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) * (((p.ν k γ).prod volume) (goodPath a γ u τ κ' lam) +
            (selected p k γ (angFail p k γ u τ) + selected p k γ (typFail p k γ p.L τ) +
              selected p k γ (typFail p k γ 0 τ) + selected p k γ (shortPath a γ u τ lam))) := by
          gcongr with γ
          have := fullPath_mass_le hp a γ (u := u) (τ := τ) (κ' := κ') (lam := lam) hK hc
          refine this.trans (le_of_eq ?_)
          ring
      _ = ∑ γ, ENNReal.ofReal (p.ω k γ) * ((p.ν k γ).prod volume) (goodPath a γ u τ κ' lam) +
            ∑ γ, ENNReal.ofReal (p.ω k γ) * (selected p k γ (angFail p k γ u τ) +
              selected p k γ (typFail p k γ p.L τ) + selected p k γ (typFail p k γ 0 τ) +
                selected p k γ (shortPath a γ u τ lam)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro γ _
          ring
      _ ≤ _ := by gcongr
  rw [weighted_fullPath_eq hp a hc hdisj] at hsum
  have hcov' := hcov.trans hsum
  -- to reals
  have hgoodsum_fin : ∑ γ, ENNReal.ofReal (p.ω k γ) *
      ((p.ν k γ).prod volume) (goodPath a γ u τ κ' lam) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro γ _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hgoodfin γ)
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hgoodsum_fin, ENNReal.ofReal_ne_top⟩)
    hcov'
  rw [ENNReal.toReal_add hgoodsum_fin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (inv_nonneg.2 hκ.le), ENNReal.toReal_ofReal hE] at hreal
  have hsumR : (∑ γ, ENNReal.ofReal (p.ω k γ) *
      ((p.ν k γ).prod volume) (goodPath a γ u τ κ' lam)).toReal =
      ∑ γ, p.ω k γ * worldMass a γ u τ κ' lam := by
    rw [ENNReal.toReal_sum (fun γ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hgoodfin γ))]
    apply Finset.sum_congr rfl
    intro γ _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hω0 _), worldMass_eq]
  linarith

/-- The per-world full-time strips (the conclusion of paired full-time binning). -/
def StripsAt (a : Atlas p k) (γ : Fin (p.W k)) (hC : 0 < a.C) (u τ κ' lam Kc KB g H : ℝ)
    (CB : ℕ) : Prop :=
  ∃ (t₀ : ℝ) (m : ℕ) (rep : Fin m → Fin a.C) (A : Fin m → Set Line)
    (L : Observation → Finset (Fin m)),
    t₀ ∈ Set.Icc (0 : ℝ) 1 ∧ (m : ℝ) ≤ ((CB : ℝ) * KB / (g * H ^ 2)) ^ CB ∧
    Function.Injective (fun i => q2bin a Kc (g * H ^ 2) (rep i)) ∧
    (∀ i, A i = {l | (l, t₀) ∈ goodPath a γ u τ κ' lam ∧
      q2bin a Kc (g * H ^ 2) (tagOf a γ hC (l, t₀)) = q2bin a Kc (g * H ^ 2) (rep i)}) ∧
    (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
    (∀ i l, l ∈ A i → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |inner ℝ (q2normal a (rep i)) (y l 0 + t • v l) - q2intercept a Kc (rep i) -
        t * q2speed a Kc (rep i)| ≤ (CB : ℝ) * KB * (g * H ^ 2)) ∧
    (∀ o, ((L o).card : ℝ) ≤ (CB : ℝ) * KB) ∧ (∀ i, MeasurableSet {o | i ∈ L o}) ∧
    ENNReal.ofReal (worldMass a γ u τ κ' lam ^ 2 / 4) ≤
      (((p.ν k γ).prod volume).restrict (goodPath a γ u τ κ' lam))
        {q | ∃ i, q.1 ∈ A i ∧ i ∈ L (obs (p.B k γ) (δ (p.N k) p.L) q)}

/-- **Full-time localization at one sample, from the coverage.** -/
theorem full_time_sample {CB : ℕ} (hCB2 : 2 ≤ CB) (hB : B0At CB) :
    ∀ (hp : Valid p) (a : Atlas p k) {M D : ℕ} {κ r : ℝ}
      {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
      (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
      (hknown : ∀ b, ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
      (κL : ℕ) (hcard : ∀ γ o, (a.lst γ o).card ≤ κL)
      (hmeas : ∀ γ b, MeasurableSet {o | b ∈ a.lst γ o})
      (hfloor : ∀ b, ENNReal.ofReal (p.N k ^ (-p.f r) * |(a.Q b).det| / ((2 : ℝ) ^ a.T * κ)) ≤
        priorMass p k (a.γ b) (a.F b))
      (hκ : 0 < κ)
      (hC : 0 < a.C) {u τ κ' lam ρ Kc KB g H E : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
      (hκ' : 1 ≤ κ') (hκκ' : κ ≤ κ') (hK : p.K k ≤ κ')
      (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ)
      (hKc : κ' + ρ ≤ Kc)
      (hKcB : 2 * Kc ≤ KB) (hκLB : (κL : ℝ) ≤ KB) (hκ'B : κ' ≤ KB) (hρB : ρ ≤ KB * g)
      (hK2 : 2 ≤ KB) (hg : 0 < g) (hgH : g * H ^ 2 ≤ 1) (hHB : (CB : ℝ) * KB ^ 2 ≤ H)
      (hρ0 : 0 ≤ ρ) (hpin : 8 * ρ / (g * H) ≤ δ (p.N k) u)
      (hE : 0 ≤ E) (hEκ : E ≤ κ⁻¹)
      (hcov : ENNReal.ofReal κ⁻¹ ≤
        ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b))
      (hexc : ∑ γ, ENNReal.ofReal (p.ω k γ) * (selected p k γ (angFail p k γ u τ) +
        selected p k γ (typFail p k γ p.L τ) + selected p k γ (typFail p k γ 0 τ) +
          selected p k γ (shortPath a γ u τ lam)) ≤ ENNReal.ofReal E),
      ∃ S : Finset (Fin (p.W k)),
        (∀ γ ∈ S, StripsAt a γ hC u τ κ' lam Kc KB g H CB) ∧
        (κ⁻¹ - E) ^ 2 / 4 -
            (ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
              (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
                ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r)))).toReal ≤
          ∑ γ ∈ S, p.ω k γ * (worldMass a γ u τ κ' lam ^ 2 / 4) := by
  have hloc := full_time_localization (p := p) (k := k) hCB2 hB
  intro hp a M D κ r ex hc hdisj hknown κL hcard hmeas hfloor hκ hC u τ κ' lam ρ Kc KB g H E hu
    huη hκ' hκκ' hK hρ hKc hKcB hκLB hκ'B hρB hK2 hg hgH hHB hρ0 hpin hE hEκ hcov hexc
  obtain ⟨S, hS, hineq⟩ := hloc hp a hc hdisj hknown κL hcard hmeas hfloor hκ hC hu huη hκ' hκκ'
    hρ hKc hKcB hκLB hκ'B hρB hK2 hg hgH hHB hρ0 hpin
  refine ⟨S, fun γ hγ => hS γ hγ, ?_⟩
  have hge := weighted_goodMass_ge hp a hc hdisj hK hE hκ hcov hexc
  have h0 : 0 ≤ κ⁻¹ - E := by linarith
  have hsq : (κ⁻¹ - E) ^ 2 ≤ (∑ γ, p.ω k γ * worldMass a γ u τ κ' lam) ^ 2 :=
    pow_le_pow_left₀ h0 hge 2
  linarith

end

end Submission.Obl.k4_raw_localized_native_systems.C
