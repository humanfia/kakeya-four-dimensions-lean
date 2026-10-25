import Submission.Obl.k4_scalar_grid_polynomial_qualification.SplitStatements

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

/-- The closed child type is exactly the existing scalar-normal interface
with its record hypothesis written as explicit premises. -/
theorem higherJetInput_iff : HigherJetInput ↔ Jets.HigherJetsStatement := by
  constructor
  · intro h d hd hd1 M hM c_h hc_h
    obtain ⟨c_ζ, hc_ζ, hε⟩ := h d hd hd1 M hM c_h hc_h
    refine ⟨c_ζ, hc_ζ, ?_⟩
    intro ε hεpos
    obtain ⟨α, hα, N₀, hN₀⟩ := hε ε hεpos
    refine ⟨α, hα, N₀, ?_⟩
    intro N hN Λ _ ν c E F piece K ζ T hK hlo hhi hζ hn
    exact hN₀ N hN Λ ν c E F piece K ζ T hK hlo hhi hζ
      hn.prob hn.one_le_K hn.zeta_pos hn.zeta_le_one
      hn.measurable_c hn.measurableSet_E hn.measurable_F hn.measurable_piece
      hn.time_mem hn.coeff_le hn.row_le hn.dense hn.support hn.abs_cap
      hn.row_cmp hn.resid_cmp hn.piece_diam hn.bin_cap
  · intro h d hd hd1 M hM c_h hc_h
    obtain ⟨c_ζ, hc_ζ, hε⟩ := h d hd hd1 M hM c_h hc_h
    refine ⟨c_ζ, hc_ζ, ?_⟩
    intro ε hεpos
    obtain ⟨α, hα, N₀, hN₀⟩ := hε ε hεpos
    refine ⟨α, hα, N₀, ?_⟩
    intro N hN Λ _ ν c E F piece K ζ T hK hlo hhi hζ
      hprob hK1 hζpos hζ1 hc hE hF hp ht hcoeff hrow hdense
      hsupport habs hcmp hresid hdiam hbin
    exact hN₀ N hN Λ ν c E F piece K ζ T hK hlo hhi hζ
      ⟨hprob, hK1, hζpos, hζ1, hc, hE, hF, hp, ht, hcoeff, hrow, hdense,
        hsupport, habs, hcmp, hresid, hdiam, hbin⟩

end Submission.Obl.k4_scalar_grid_polynomial_qualification
