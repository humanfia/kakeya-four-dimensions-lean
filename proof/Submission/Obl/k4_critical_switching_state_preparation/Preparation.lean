import Submission.Obl.k4_critical_switching_state_preparation.PreparedAt
import Submission.Obl.k4_critical_switching_state_preparation.NormalizedDomination
import Submission.Obl.k4_critical_switching_state_preparation.NativeNumerics
import Submission.Obl.k4_critical_switching_state_preparation.PaletteIntervals

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Filter Inherited

noncomputable section

/-- At each fixed sufficiently small critical depth, choose one primitive
loss before all samples and prepare every dense original affine primitive. -/
theorem switching_preparation : SwitchingPreparation := by
  intro α _ cfg h s hs hUs he hs1 δ hδ
  obtain ⟨η, hη, hηδ, hηs, hsource⟩ :=
    h.exists_critical_pair_source_exponent hs hUs (show 0 < δ / 100 by positivity)
  refine ⟨η, hη, hηδ.trans (by linarith), ?_⟩
  have hv : 0 < s / 16 := by positivity
  have hvs : s / 16 ≤ s := by linarith
  have hsU : s + s / 16 ≤ cfg.U := by linarith
  have hκ : cfg.κ = 1 / 2 := by linarith [h.critical_rate]
  have hgap : 0 < cfg.κ * s - s / 16 - η := by rw [hκ]; linarith
  have hfine := h.eventually_source_pair_upper_mesh hs hv hvs hsU hη (by linarith) hgap
  have hraw := h.eventually_fine_original_palette_bound hs hsU hη hηs
  have herr := h.eventually_centered_error hs he (by linarith)
  have hpalette := h.eventually_shifted_palette_intervals (a := 200 * s) (by positivity) hδ
  have hbudget := h.eventually_preparation_budget hδ hηδ
  have hbound := h.eventually_centered_bound hδ
  have hparent := h.eventually_assignment_level hs (by linarith)
  filter_upwards [hsource, hfine, hraw, herr, hpalette, hbudget, hbound, hparent]
    with k hsource hfine hraw herr hpalette hbudget hbound parent i L hL0 hL hmass
  obtain ⟨src⟩ := hsource i L hL0 hL
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  obtain ⟨Ffine, hFfine, hcard⟩ := hfine (cfg.N k ^ (-200 * s))
    (Real.rpow_pos_of_pos hN _) (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
    i L src.source hL0 hL src.source_subset src.coefficients
    (fun p hp => src.true_descendants p hp (s + s / 16) (by simp))
  have hraw' := hraw i L src.source hL src.source_subset
  simp only [show -(s + s / 16) = -s - s / 16 by ring] at hraw'
  have hdom := parent.normalized_source_domination h i src.source
    (fun p hp => parent.fitted_subset i (src.source_subset hp).1)
  simp only [show -20 * (10 * s) = -200 * s by ring] at herr
  exact parent.prepared_at h src (by linarith) hmass Ffine
    (fun p hp => (hFfine _).mpr ⟨p, hp, rfl⟩) hcard hraw' hdom
    hbound herr hbudget (by simpa only [neg_mul] using hpalette)

end

end Submission.Obl.k4_critical_switching_state_preparation
