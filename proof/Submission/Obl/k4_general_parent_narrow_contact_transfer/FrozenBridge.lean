import Submission.Obl.k4_general_parent_narrow_contact_transfer.FrontEnd
import Submission.Obl.k4_general_parent_narrow_contact_transfer.FrozenStatements

namespace Submission.Obl.k4_general_parent_narrow_contact_transfer

open MeasureTheory Set Filter

/-- Explicit existential form of the row-parent interface. -/
def RawRowParents {α : Type} [MeasurableSpace α] (cfg : Model α) (r : ℝ) : Prop :=
  (fun r:ℝ => ∃ e:ℝ,0 < e ∧ ∃ M:ℕ → ℝ,(∀ k,1 ≤ M k) ∧ (∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,M k ≤ cfg.N k^ε) ∧ ∃ᶠ k in Filter.atTop,∃ (Q:Fin (cfg.n k r)) (Brow:Fin 2 → ℝ) (lam:ℝ) (Gset:Set (α × ℝ)),MeasurableSet Gset ∧ Gset ⊆ cfg.B k r Q ×ˢ Submission.Obl.k4_critical_intercept_concentration.Data.I (cfg.T k r) (cfg.j k r Q) ∧ ENNReal.ofReal (((2:ℝ)^(-(cfg.T k r:ℤ)))/M k)*cfg.ν k (cfg.A k r Q) ≤ cfg.ρ k Gset ∧ |Brow 0|+|Brow 1| ≤ M k ∧ |lam| ≤ M k ∧ ∀ z ∈ Gset,|(2:ℝ)^(-(cfg.T k r:ℤ))*(cfg.b k z.1 4-cfg.c k r Q 3-cfg.c k r Q 4*cfg.b k z.1 3)/((2:ℝ)^(-(cfg.T k r:ℤ))*cfg.N k^(-cfg.ℓ*r))-Brow 0-Brow 1*cfg.b k z.1 3+lam*((cfg.b k z.1 0+(((cfg.j k r Q:ℕ):ℝ)/(2:ℝ)^cfg.T k r)*cfg.b k z.1 3-(cfg.c k r Q 0+(((cfg.j k r Q:ℕ):ℝ)/(2:ℝ)^cfg.T k r)*cfg.c k r Q 1))/((2:ℝ)^(-(cfg.T k r:ℤ))))| ≤ cfg.N k^(-e)) r

/-- Expanding the row-parent record adds no hypothesis. -/
theorem rawRowParents_iff {α : Type} [MeasurableSpace α] (cfg : Model α) (r : ℝ) :
    RawRowParents cfg r ↔ RowParents cfg r := by
  constructor
  · rintro ⟨e, he, M, hM, hsub, hfreq⟩
    refine ⟨e, he, M, hM, hsub, ?_⟩
    apply hfreq.mono
    rintro k ⟨Q, B, lam, G, hmeas, hG, hmass, hB, hlam, hrow⟩
    exact ⟨⟨Q, B, lam, G, hmeas, hG, hmass, hB, hlam, hrow⟩⟩
  · rintro ⟨e, he, M, hM, hsub, hfreq⟩
    refine ⟨e, he, M, hM, hsub, ?_⟩
    apply hfreq.mono
    rintro k ⟨RP⟩
    exact ⟨RP.Q, RP.B, RP.lam, RP.G, RP.measurable_G, RP.G_sub, RP.mass,
      RP.B_le, RP.lam_le, RP.row⟩

/-- The first frozen child gives the structured front interface. -/
theorem narrowFront_of_raw (h : RawNarrowFront) : NarrowFront := by
  intro hRow hMatch α _ cfg hv
  have hf := h hRow hMatch cfg.N cfg.K hv.scale hv.scale_limit hv.subpower
    cfg.d cfg.κ cfg.ℓ cfg.S cfg.U cfg.e₀ hv.dimension_nonneg hv.dimension_lt_one
    hv.rate_pos hv.rate_le_one hv.transverse_pos hv.palette_pos hv.palette_le_one
    hv.depth_pos hv.defect_pos α cfg.ν cfg.μ cfg.ρ cfg.π cfg.b cfg.P cfg.T cfg.n
    cfg.j cfg.A cfg.B cfg.c cfg.F hv.basic hv.caps hv.atlas hv.nested
  obtain ⟨Λ, hΛ, hf⟩ := hf
  refine ⟨Λ, hΛ, ?_⟩
  intro L₀ hL₀ hlay a s ha haU has hs2 τ H ρ' β n' C tag u v G hw
  have hc := hf L₀ hL₀ hlay a s ha haU has hs2 τ H ρ' β n' C tag u v G
    ⟨hw.mono, hw.loss, hw.loss_subpower, hw.retained, hw.slice, hw.narrow⟩
  rcases hc with hc | ⟨r, hr, hrU, hrows⟩
  · exact Or.inl hc
  · exact Or.inr ⟨r, hr, hrU, (rawRowParents_iff cfg r).mp hrows⟩

/-- The second frozen child gives the structured contact transfer. -/
theorem narrowBack_of_raw (h : RawNarrowBack) : NarrowBack := by
  intro h3 α _ cfg hv r hr hrU hrows
  exact h ((principle_iff 3).mpr h3) cfg.N cfg.K hv.scale hv.scale_limit hv.subpower
    cfg.d cfg.κ cfg.ℓ cfg.S cfg.U cfg.e₀ hv.dimension_nonneg hv.dimension_lt_one
    hv.rate_pos hv.rate_le_one hv.transverse_pos hv.palette_pos hv.palette_le_one
    hv.depth_pos hv.defect_pos α cfg.ν cfg.μ cfg.ρ cfg.π cfg.b cfg.P cfg.T cfg.n
    cfg.j cfg.A cfg.B cfg.c cfg.F hv.basic hv.caps hv.atlas hv.nested
    r hr hrU ((rawRowParents_iff cfg r).mpr hrows)

end Submission.Obl.k4_general_parent_narrow_contact_transfer
