import Submission.Obl.k4_critical_switching_state_preparation.CenteredGeometry
import Submission.Obl.k4_critical_switching_state_preparation.StateCoding

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The actual original-source geometry supplies every pointwise part of the
frozen horizontal law. Only the final measure ceilings are separate inputs. -/
theorem AssignmentLevel.horizontalLaw_of_final_bounds (h : cfg.Valid)
    {k : ℕ} {s v η ζ δ : ℝ} {depths : Finset ℝ} {i : Fin (cfg.n k s)} {L : Fin 4 → ℝ}
    (parent : cfg.AssignmentLevel k s) (src : cfg.RegularPairSource k s v η ζ depths i L)
    (σ : Measure (α × ℝ)) (π₀ : Measure ℝ) (G : Set (α × ℝ))
    (hσ : IsProbabilityMeasure σ) (hπ : IsProbabilityMeasure π₀)
    (hG : MeasurableSet G) (hGfull : σ Gᶜ = 0)
    (hsource : ∀ p ∈ G, cfg.physicalTime k s i p ∈ src.source)
    (hbound : 8 * cfg.K k ^ 4 ≤ cfg.N k ^ δ)
    (herror : cfg.N k ^ (-cfg.e₀) / cfg.timeLength k s ≤ cfg.N k ^ (-200 * s))
    (htime : σ ≤ ENNReal.ofReal (cfg.N k ^ δ) • ((σ.map Prod.fst).prod volume))
    (hpalette : ∀ (q : ℕ) (j : ℤ),
      σ {p | cfg.fineState k s i L (cfg.N k ^ (-200 * s)) p = q ∧
        ⌊cfg.centeredVelocity k s i p.1 / cfg.N k ^ (-200 * s)⌋ = j} ≤
        ENNReal.ofReal (cfg.N k ^ δ) *
          σ {p | cfg.fineState k s i L (cfg.N k ^ (-200 * s)) p = q} *
            π₀ {w | ⌊w / cfg.N k ^ (-200 * s)⌋ = j})
    (hinterval : ∀ z r : ℝ, cfg.N k ^ (-200 * s) ≤ r → r ≤ 1 →
      π₀ (Icc (z - r) (z + r)) ≤ ENNReal.ofReal (cfg.N k ^ δ * r ^ cfg.S)) :
    HorizontalLaw (cfg.N k) (10 * s) cfg.S δ σ π₀
      (cfg.centeredLine k s i) (cfg.centeredVelocity k s i)
      (cfg.midpointBin k s (s / 16) i L)
      (cfg.fineState k s i L (cfg.N k ^ (-200 * s))) G := by
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  refine ⟨hσ, hπ, measurable_centeredLine h k s i, measurable_centeredVelocity h k s i,
    measurable_midpointBin h k s (s / 16) i L, measurable_fineState h k s i L _,
    hG, hGfull, htime, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hsrc := hsource p hp
    have hprim := src.source_subset hsrc
    have hl : p.1 ∈ cfg.A k s i := parent.fitted_subset i hprim.1
    have hunit : p.2 ∈ Icc (0 : ℝ) 1 := by
      have hh := cfg.normalizeTime_mem_unit k s i hprim.2.1
      simpa only [normalizeTime_physicalTime] using hh
    have hb : |cfg.b k p.1 3| ≤ 2 * cfg.K k := src.coefficients _ hsrc 3
    have hdef : |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) :=
      src.horizontal_defect (cfg.physicalTime k s i p) hsrc
    refine ⟨hunit, (parent.centeredVelocity_bound h i hb).trans hbound, ?_, ?_⟩
    · intro t ht
      exact ⟨cfg.centeredLine_time k s i p.1 t,
        fun e => (parent.centeredLine_bounds h i hl ht e).trans hbound⟩
    · intro t ht u hu
      refine ⟨cfg.centeredLine_horizontal_first k s i p.1 t u, ?_⟩
      have hh := (cfg.centeredLine_horizontal_error k s i p.1
        (Real.rpow_nonneg hN.le _) hdef ht hu).trans herror
      simpa only [show -20 * (10 * s) = -200 * s by ring] using hh
  · intro p hp q hq heq
    have hh := cfg.fineState_diameter k s i L (Real.rpow_pos_of_pos hN _) heq
    simpa only [show -20 * (10 * s) = -200 * s by ring] using hh
  · simpa only [show -20 * (10 * s) = -200 * s by ring] using hpalette
  · simpa only [show -20 * (10 * s) = -200 * s by ring] using hinterval

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
