import Submission.Obl.k4_scalar_grid_polynomial_qualification.FirstJetClosedStatement
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.FirstJet

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

/-- The Mathlib-only first-jet type exposes the scalar-normal fields and
the deterministic cover, without changing their meaning. -/
theorem firstJetInput_iff : FirstJetInput ↔ Jets.FirstJetStatement := by
  constructor
  · intro h d hd hd1 r γ γ₀ hγ hγ₀ hγ₀pos
    obtain ⟨cζ, hcζ, hε⟩ := h d hd hd1 r γ γ₀ hγ hγ₀ hγ₀pos
    refine ⟨cζ, hcζ, ?_⟩
    intro ε hεpos
    obtain ⟨α, hα, N₀, hN₀⟩ := hε ε hεpos
    refine ⟨α, hα, N₀, ?_⟩
    intro N hN Λ _ ν c E F piece K ζ Tl T₀ hK hζ hlevels hlo hhi hTl₀ hn
    have hdata := hN₀ N hN Λ ν c E F piece K ζ Tl T₀ hK hζ hlevels hlo hhi hTl₀
      hn.prob hn.one_le_K hn.zeta_pos hn.zeta_le_one
      hn.measurable_c hn.measurableSet_E hn.measurable_F hn.measurable_piece
      hn.time_mem hn.coeff_le hn.row_le hn.dense hn.support hn.abs_cap
      hn.row_cmp hn.resid_cmp hn.piece_diam hn.bin_cap
    simpa [Jets.Determined, Jets.zS, Jets.zx, Jets.zy, Jets.dI, Jets.jet,
      Jets.xder, Jets.leafRows] using hdata
  · intro h d hd hd1 r γ γ₀ hγ hγ₀ hγ₀pos
    obtain ⟨cζ, hcζ, hε⟩ := h d hd hd1 r γ γ₀ hγ hγ₀ hγ₀pos
    refine ⟨cζ, hcζ, ?_⟩
    intro ε hεpos
    obtain ⟨α, hα, N₀, hN₀⟩ := hε ε hεpos
    refine ⟨α, hα, N₀, ?_⟩
    intro N hN Λ _ ν c E F piece K ζ Tl T₀ hK hζ hlevels hlo hhi hTl₀
      hprob hK1 hζpos hζ1 hc hE hF hp ht hcoeff hrow hdense
      hsupport habs hcmp hresid hdiam hbin
    have hdata := hN₀ N hN Λ ν c E F piece K ζ Tl T₀ hK hζ hlevels hlo hhi hTl₀
      ⟨hprob, hK1, hζpos, hζ1, hc, hE, hF, hp, ht, hcoeff, hrow, hdense,
        hsupport, habs, hcmp, hresid, hdiam, hbin⟩
    simpa [Jets.Determined, Jets.zS, Jets.zx, Jets.zy, Jets.dI, Jets.jet,
      Jets.xder, Jets.leafRows] using hdata

end Submission.Obl.k4_scalar_grid_polynomial_qualification
