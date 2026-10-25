import Submission.Obl.k4_scalar_grid_parameter_preparation.EntryInterface
import Submission.Obl.k4_scalar_grid_parameter_preparation.SequenceCoefficientLists
import Submission.Obl.k4_scalar_grid_parameter_preparation.TagConversions

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped Classical ENNReal

theorem entry_stage_claim : EntryStageClaim := by
  intro N K Hc W d θ ρ π Ξ B hN hNt hK hHc hd hd₁ hρ hθ hπ hcard hΞ hB hdom hprior hcap
  let C := fun k => max (K k) (Hc k)
  have hC := Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hK hHc
  have hKC (k) : K k ≤ C k := le_max_left _ _
  have hHcC (k) : Hc k ≤ C k := le_max_right _ _
  have hB' : ∀ k g, MeasurableSet (B k g) ∧
      ∀ z ∈ B k g, z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |z.1.2 e| ≤ C k := by
    intro k g
    refine ⟨(hB k g).1,?_⟩
    intro z hz
    exact ⟨((hB k g).2 z hz).1,fun e => (((hB k g).2 z hz).2 e).trans (hHcC k)⟩
  have hprior' : ∀ k g, ∀ r ∈ Ξ k, ∀ z ∈ B k g,
      ENNReal.ofReal (N k ^ (-((1 + d) * r)) / Hc k) *
        π k g (scalarVelocityBin (N k ^ (-r)) ⌊z.1.2 1 / N k ^ (-r)⌋) ≤
        θ k g {l | scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) l.2 =
          scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) z.1.2} := by
    intro k g r hr z hz
    simpa only [coeffTag_eq,velBin_eq] using hprior k g r hr z hz
  have hcap' : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r : ℝ),
      R⁻¹ ≤ r → r ≤ R → ∀ (q : Fin 3 → ℤ) (c : ℤ),
        ρ k g (B k g ∩ {z | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition Prod.snd z) = q ∧
          (⌊z.1.2 1 / N k ^ (-r)⌋ : ℤ) = c}) ≤
          ENNReal.ofReal (C k * N k ^ (-((2 + d) * r))) *
            π k g (scalarVelocityBin (N k ^ (-r)) c) := by
    intro R hR
    filter_upwards [hcap R hR] with k hk
    intro g r hr hr' q c
    have hh := hk g r hr hr' q c
    apply (measure_mono (Set.inter_subset_right :
      B k g ∩ {z | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition Prod.snd z) = q ∧
        (⌊z.1.2 1 / N k ^ (-r)⌋ : ℤ) = c} ⊆ _)).trans
    have hh' : ρ k g {z | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition Prod.snd z) = q ∧
        (⌊z.1.2 1 / N k ^ (-r)⌋ : ℤ) = c} ≤
        ENNReal.ofReal (Hc k * N k ^ (-((2 + d) * r))) * π k g (scalarVelocityBin (N k ^ (-r)) c) := by
      simpa only [physTag_eq,velBin_eq] using hh
    exact hh'.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hHcC k) (Real.rpow_nonneg (by linarith [hN k]) _))) le_rfl)
  have hπfinite (k) (g : Fin (W k)) : IsFiniteMeasure (π k g) := by
    letI : IsProbabilityMeasure (π k g) := hπ k g
    infer_instance
  obtain ⟨Hl,E,hHl,hHlH,hE,hloss,hlists⟩ := exists_sequence_coefficient_lists N C Hc Hc hN hNt
    hC hHc hHc W Prod.snd measurable_snd θ hθ ρ hρ π hπfinite B hB' Ξ hΞ hcard d hprior' hcap'
  refine ⟨Hl,E,hHl,hE,?_,?_⟩
  · filter_upwards [hloss] with k hk
    intro g
    have hKp : 0 < K k := zero_lt_one.trans_le (hK.1 k)
    have hh : 1 / (100 * C k) ≤ 1 / (100 * K k) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left (hKC k) (by norm_num))
    exact (hk g).trans (ENNReal.ofReal_le_ofReal hh)
  · intro R hR
    filter_upwards [hlists R hR] with k hk
    intro g r hrΞ hr hr' q c
    simpa only [physTag_eq,coeffTag_eq] using (hk g r hr hr' hrΞ q c).2

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
