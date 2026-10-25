/-
Adapted from: here:o093
Own proofs by session x0318, branch ae1ecd4; scalar chart interfaces by
session x0364 in the same LOT tree. The source module is
Submission/Obl/k4_scalar_critical_path_terminal/CriticalCertificate.lean.
-/

import Submission.Obl.k4_scalar_linear_critical_extremizers.CapBuffer

set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_linear_critical_extremizers.Split

open Set Filter
open scoped Topology

noncomputable section

/-- The full linear critical certificate follows from the three concrete
chart-calculus inputs and a positive-horizon exact scalar problem. -/
theorem critical_of_initial_weakCalculus_extension (hinit : Initial) (hcalc : WeakCalculus)
    (hext : Extension) (hbad : ∃ p : Code, Exact p ∧ 0 < Horizon p) : Critical := by
  obtain ⟨p₀, hp₀, hH₀⟩ := hbad
  let S₀ := S p₀
  let η := U p₀ / L p₀
  have hS : 0 < S₀ := (exact_angular_pos hp₀).1
  have hη : 0 < η := div_pos (exact_angular_pos hp₀).2 (exact_length_pos hp₀)
  have hp₀class : AngularClass S₀ η p₀ := by
    refine ⟨hp₀, rfl, ?_⟩
    dsimp [η]
    field_simp [(exact_length_pos hp₀).ne']
  have hne : (badDimensions (AngularClass S₀ η) d Horizon).Nonempty :=
    ⟨d p₀, (exact_dimension_bounds hp₀).1, (exact_dimension_bounds hp₀).2,
      p₀, hp₀class, le_rfl, hH₀⟩
  let dstar := classDimension S₀ η
  let κ := classCriticalRate S₀ η
  have hstar₀ : 0 ≤ dstar := criticalDimension_nonneg _ _ _ hne
  have hstar₁ : dstar < 1 := criticalDimension_lt_one _ _ _ hne
  have hκ : 0 < κ ∧ κ ≤ 1 := class_critical_rate_bounds hinit hcalc hext S₀ η hS hη hne
  obtain ⟨p, hp, hdimlim, hHlim, hRlim, huniform⟩ :=
    class_maximizing_profiles hinit hcalc hext S₀ η hS hη hne
  let err := fun i => profileError (p i) dstar
  have herr (i : ℕ) : 0 ≤ err i :=
    (profileError_bounds (hp i).1.1 (hp i).2.1 hstar₀ hstar₁.le).1
  have herrlim : Tendsto err atTop (𝓝 0) := profileError_tendsto_zero p dstar
    (fun i => (hp i).1.1) (fun i => (hp i).2.1) hstar₀ hstar₁.le huniform
  have hdim (i : ℕ) : dstar ≤ d (p i) ∧ d (p i) < 1 := by
    exact ⟨criticalDimension_le_bad _ _ _ (hp i).1
      (exact_dimension_bounds (hp i).1.1).1 (exact_dimension_bounds (hp i).1.1).2
      (hp i).2.2, (exact_dimension_bounds (hp i).1.1).2⟩
  obtain ⟨D₀, hD₀, hDlim, hratio⟩ := exists_slow_cap_buffer
    (fun i => d (p i)) err dstar hstar₁ hdim hdimlim herr herrlim
  let b := fun i => classRate S₀ η (D₀ i)
  have hbH (i : ℕ) : Horizon (p i) ≤ b i := by
    have ht := horizon_le_extremalRate_mul _ _ _ _ (class_horizon_bound hinit S₀ η)
      (hp i).1 (hD₀ i).1
    simpa only [b, classRate, (hp i).2.1, mul_one] using ht
  have hb (i : ℕ) : 0 ≤ b i ∧ b i ≤ 1 :=
    ⟨(hp i).2.2.le.trans (hbH i),
      extremalRate_le_one _ _ _ _ (class_horizon_bound hinit S₀ η)
        (class_rate_nonempty S₀ η hne (hD₀ i).2.1)⟩
  obtain ⟨α, hα, hlower⟩ := class_rates_uniformly_positive hinit hcalc hext S₀ η hS hη hne
  have hblim : Tendsto b atTop (𝓝 κ) :=
    extremal_rates_tendsto_criticalRate hstar₁
      (fun D' hD => hα.le.trans (hlower D' hD))
      (fun D' hD D'' hD' hDD => extremalRate_mono _ _ _ _
        (class_horizon_bound hinit S₀ η) hDD (class_rate_nonempty S₀ η hne hD.1))
      D₀ (fun i => (hD₀ i).2) hDlim
  refine ⟨S₀, η, dstar, κ, p, D₀, b, hS, hη, hstar₀, hstar₁, hκ.1, hκ.2,
    ?_, hdimlim, hDlim, hblim, hHlim, ?_, ?_⟩
  · intro i
    exact ⟨(hp i).1.1, (hp i).2.1, (hp i).1.2.1,
      by simpa only [(hp i).2.1, mul_one] using (hp i).1.2.2,
      (hD₀ i).1, (hD₀ i).2.1, (hD₀ i).2.2, (hb i).1, (hb i).2⟩
  · intro i q hq hqd hqS hqU
    exact horizon_le_extremalRate_mul _ _ _ _ (class_horizon_bound hinit S₀ η)
      ⟨hq, hqS, hqU⟩ hqd
  · intro ε hε
    have hevent := hratio.eventually_lt tendsto_const_nhds hε
    filter_upwards [hevent] with i hi r hr₀ hr₁
    apply (profileError_bounds (hp i).1.1 (hp i).2.1 hstar₀ hstar₁.le).2 r ⟨hr₀, hr₁⟩ |>.trans
    exact (div_le_iff₀ (sub_pos.mpr (hD₀ i).2.1)).1 hi.le

theorem critical_of_initial_calculus_extension (hinit : Initial) (hcalc : Calculus)
    (hext : Extension) (hbad : ∃ p : Code, Exact p ∧ 0 < Horizon p) : Critical :=
  critical_of_initial_weakCalculus_extension hinit (weakCalculus_of_calculus hcalc) hext hbad

end

end Submission.Obl.k4_scalar_linear_critical_extremizers.Split
