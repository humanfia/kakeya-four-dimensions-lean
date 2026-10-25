/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/ScalarContactCount.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeContactBox
import Submission.Obl.k4_subcritical_corrected_scalar_charts.ReferenceSupportCount
import Submission.Obl.k4_subcritical_corrected_scalar_charts.ContactMargins

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original true entries contacting a scalar cell, at one native time
block and under one named original ancestor, have the required (A0/ai)^d
count. Contact points may have arbitrarily small later retained mass. -/
theorem Prepared.eventually_scalar_contact_count (h : cfg.Prepared)
    {s₀ s M ε : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hnear : s - s₀ ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16)
    (hM : 100 * s₀ < M) (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      ∀ (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
        (ip : Fin (cfg.n k s₀)) (S : Finset (Fin (cfg.n k s)))
        (block : Fin (2 ^ cfg.T k s)) (pc qc v R : ℝ),
      |pc| ≤ 3 * cfg.K k → |v| ≤ 3 * cfg.K k →
      (∀ i ∈ S, cfg.j k s i = block) →
      (∀ i ∈ S, cfg.A k s i ⊆ cfg.A k s₀ ip) →
      (∀ i ∈ S, I (cfg.T k s) (cfg.j k s i) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip)) →
      (∀ i ∈ S, ∃ (l : α) (t : ℝ), l ∈ cfg.B k s i ∧ t ∈ I (cfg.T k s) (cfg.j k s i) ∧
        |cfg.b k l 0 - pc| ≤ cfg.N k ^ (-(2 * cfg.κ * s₀)) ∧
        |cfg.b k l 3 - v| ≤ cfg.N k ^ (-M) ∧
        |cfg.b k l 4 + cfg.b k l 0| ≤ cfg.N k ^ (-M) ∧
        |(cfg.b k l 1 - qc) / cfg.N k ^ (-(2 * cfg.κ * s₀)) -
          2 * t * ((cfg.b k l 0 - pc) / cfg.N k ^ (-(2 * cfg.κ * s₀))) - R| ≤
            cfg.N k ^ (-(20 * s₀))) →
      (S.card : ℝ) ≤ cfg.N k ^ ε *
        ((cfg.N k ^ (-s₀)) / (cfg.N k ^ (-s))) ^ cfg.d := by
  filter_upwards [h.eventually_reference_descendant_count hs₀ hs hε,
    h.eventually_scalar_contact_margins hs₀ hs hnear hM] with k hcount hmargin
  intro parent child ip S block pc qc v R hpc hv hblock hA hI hcontacts
  let τ := (((block : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s
  have hτunit : τ ∈ Icc (0 : ℝ) 1 := native_midpoint_mem_unit _ _
  have hτ : |τ| ≤ 1 := by rw [abs_of_nonneg hτunit.1]; exact hτunit.2
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hD : 0 < cfg.N k ^ (-(2 * cfg.κ * s₀)) := Real.rpow_pos_of_pos hN _
  have hm := hmargin child.assignments
  apply hcount parent child ip S τ pc (qc + cfg.N k ^ (-(2 * cfg.κ * s₀)) * R) v hτ hpc hv
    ?_ hA hI
  intro i hi y hy e
  obtain ⟨l, t, hl, ht, hp, hvel, hhor, hR⟩ := hcontacts i hi
  have hmid : cfg.nativeMidpoint k s i = τ := by
    unfold nativeMidpoint
    rw [hblock i hi]
  have hh := child.reference_box_of_scalar_contact h i hD hm.1 hm.2.1 hm.2.2.1 hm.2.2.2 hv
    hl ht hp hvel hhor hR y.1 hy.1 y.2 hy.2 e
  simpa only [hmid] using hh

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
