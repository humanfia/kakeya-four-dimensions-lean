/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/CriticalNode.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RelativeNormalization

/-!
The concrete one-node critical-path reduction. All cost and refinement
objects are actual exact sequences; no horizon is transported through a
limiting tangent object.
-/

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- One interior target on a buffered critical family supplies actual
coarsened and remaining maximizing problems, attainable outer costs,
and the full original-law refinement of the remaining problem. -/
theorem exists_actual_critical_node (hinit : Initial) (hcalc : Calculus)
    (S₀ η dstar κ r : ℝ) (p : ℕ → Code) (D B : ℕ → ℝ)
    (hp : ∀ i, AngularClass S₀ η (p i)) (hL : ∀ i, L (p i) = 1)
    (hstar₀ : 0 ≤ dstar) (hstar₁ : dstar < 1)
    (hD : ∀ i, dstar < D i ∧ D i < 1 ∧ d (p i) ≤ D i)
    (hr₀ : 0 < r) (hr₁ : r < 1)
    (hrate : ∀ i q, AngularClass S₀ η q → d q ≤ D i → Horizon q ≤ B i * L q)
    (hHlim : Tendsto (fun i => Horizon (p i)) atTop (𝓝 κ))
    (hBlim : Tendsto B atTop (𝓝 κ))
    (hscaled : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
      |f (p i) s - f (p i) 0 - dstar * s| ≤ ε * (D i - dstar)) :
    ∃ (depth h : ℕ → ℝ) (outer remaining : ℕ → Code),
      (∀ i, depth i ∈ Icc 0 r) ∧ Tendsto depth atTop (𝓝 r) ∧
      (∀ᶠ i in atTop,
        AngularClass S₀ η (outer i) ∧ L (outer i) = depth i ∧
        d (outer i) = dstar + (D i - dstar) / 2 ∧
        (∀ s ∈ Icc 0 (depth i),
          f (outer i) s - f (outer i) 0 = f (p i) s - f (p i) 0) ∧
        Cost (outer i) (h i) ∧ Known (p i) (depth i) (depth i) (h i) ∧
        AngularClass S₀ η (remaining i) ∧ L (remaining i) = 1 - depth i ∧
        d (remaining i) = D i ∧
        Refinement (p i) (remaining i) (depth i) (depth i) (h i) ∧
        (∀ s ∈ Icc 0 (L (remaining i)),
          f (remaining i) s - f (remaining i) 0 =
            f (p i) (depth i + s) - f (p i) (depth i)) ∧
        Horizon (p i) ≤ h i + Horizon (remaining i)) ∧
      Tendsto h atTop (𝓝 (κ * r)) ∧
      Tendsto (fun i => Horizon (outer i)) atTop (𝓝 (κ * r)) ∧
      Tendsto (fun i => Horizon (outer i) / L (outer i)) atTop (𝓝 κ) ∧
      Tendsto (fun i => Horizon (remaining i)) atTop (𝓝 (κ * (1 - r))) ∧
      Tendsto (fun i => Horizon (remaining i) / L (remaining i)) atTop (𝓝 κ) := by
  let buffer := fun i => D i - dstar
  let δ := fun i => dstar + buffer i / 2
  have hb (i : ℕ) : 0 < buffer i := sub_pos.mpr (hD i).1
  obtain ⟨depth, hdepth, hdepthlim, hpos, hcap, hstrict⟩ :=
    exists_actual_critical_nodes p dstar r buffer (fun i => (hp i).1) hL
      hstar₀ hstar₁.le hr₀ hr₁ hb hscaled
  have hD₀ (i : ℕ) : 0 ≤ D i := hstar₀.trans (hD i).1.le
  have hδ₀ (i : ℕ) : 0 ≤ δ i := add_nonneg hstar₀ (half_pos (hb i)).le
  have hδD (i : ℕ) : δ i ≤ D i := by
    dsimp only [δ, buffer]
    linarith [(hD i).1]
  have hδ₁ (i : ℕ) : δ i < 1 := (hδD i).trans_lt (hD i).2.1
  obtain ⟨outer, houter, houterlim, houterratio⟩ :=
    exists_coarsened_maximizing_sequence hinit (weakCalculus_of_calculus hcalc)
      S₀ η κ r p D B depth δ hp hL hD₀ (fun i => (hD i).2.1)
      (fun i => (hD i).2.2) hδ₀ hδ₁ hδD hr₀ hr₁ hdepth hdepthlim hcap
      hrate hHlim hBlim
  obtain ⟨h, hcost, hhlim⟩ := exists_costs_tendsto hinit outer (κ * r)
    (houter.mono fun i hi => hi.1.1) houterlim
  have hKnown : ∀ᶠ i in atTop, Known (p i) (depth i) (depth i) (h i) := by
    filter_upwards [houter, hcost] with i hi hc
    exact hi.2.2.2.2 (h i) hc
  have hvalid : ∀ᶠ i in atTop, 0 ≤ depth i ∧ depth i < 1 ∧
      Known (p i) (depth i) (depth i) (h i) := by
    filter_upwards [hKnown] with i hi
    exact ⟨(hdepth i).1, (hdepth i).2.trans_lt hr₁, hi⟩
  obtain ⟨remaining, hremaining, hremaininglim, hremainingratio⟩ :=
    exists_remaining_maximizing_sequence hcalc S₀ η κ r p D B depth h hp hL hD₀
      (fun i => (hD i).2.1) (fun i => (hD i).2.2) hrate hvalid hr₁ hdepthlim
      hHlim hhlim hBlim
  refine ⟨depth, h, outer, remaining, hdepth, hdepthlim, ?_, hhlim,
    houterlim, houterratio, hremaininglim, hremainingratio⟩
  filter_upwards [houter, hcost, hKnown, hremaining] with i ho hc hk hrem
  exact ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.1, hc, hk, hrem⟩

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
