import Submission.Obl.k4_scalar_candidate_original_return.Coverage.Bridge

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter
open scoped Topology

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid)
include ha

lemma Valid.factor_subpower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, a.H k ≤ a.tangent k ^ ε := by
  filter_upwards [ha.scales.eventually_factor_power_le_allowance 1 1,
    ha.allowance_subpower ε hε] with k hk hεk
  have hk' : (1 : ℝ) * a.H k ^ 1 ≤ a.allowance k := hk
  have hfactor : a.H k ≤ a.allowance k := by simpa only [one_mul, pow_one] using hk'
  exact hfactor.trans hεk

lemma Valid.tangentData_valid : a.tangentData.Valid := by
  refine ⟨ha.tangent_input, ?_, ha.factor_subpower⟩
  intro k
  obtain ⟨hsc, hsc1, hH, hbf, hM, hM', hD, hL, hK, hct, hH'⟩ := ha.bounds k
  exact ⟨hH, hct, ha.weighted_mass k⟩

lemma Valid.encoding_core : EncodingCore a := by
  obtain ⟨hN, hNt, hK, hd, hd1, hκ, hκ1, hS, hlaws, hcaps, hblocks⟩ := ha.tangent_input
  refine ⟨ha.exact, ?_, hNt, hK.2, ha.factor_subpower, hκ, ha.range, ha.rho_le, ?_, ?_⟩
  · intro k
    obtain ⟨hsc, hsc1, hH, hbf, hM, hM', hD, hL, hK', hct, hH'⟩ := ha.bounds k
    exact ⟨hsc, hsc1, hH, hM, hM', hD, hL, hK'⟩
  · intro k ℓ
    exact ⟨a.sc k * a.dp k ℓ, a.sc k * a.tm k ℓ, (ha.layer k ℓ).2.2.1⟩
  · intro R hR
    filter_upwards [hblocks R hR] with k hk
    intro s hs hs'
    exact (hk s hs hs').2.1

lemma Valid.terminalStep_small (R : ℝ) (hR : 0 < R) :
    ∀ᶠ k in atTop, a.tangentData.terminalStep k ≤ a.tangent k ^ (-R) := by
  filter_upwards [ha.range (max 2 R) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))]
    with k hk
  change a.original k ^ (-L (a.p k)) ≤ a.tangent k ^ (-R)
  have hpow : a.tangent k ^ (-R) = a.original k ^ (a.sc k * (-R)) :=
    ha.scales.tangent_rpow k (-R)
  rw [hpow]
  have hN : 2 ≤ a.original k := ha.scales.original_ge_two k
  apply Real.rpow_le_rpow_of_exponent_le (by linarith)
  have hsc := (ha.bounds k).1
  have hmax := le_max_right (2 : ℝ) R
  nlinarith

lemma Valid.tangentData_terminalKnown : a.tangentData.TerminalKnown := by
  refine ⟨?_, ha.terminalStep_small, ?_, ?_, ?_⟩
  · intro k
    exact Real.rpow_pos_of_pos (ha.scales.original_pos k) _
  · intro k ℓ g z
    have hcd := (ha.layer k ℓ).2.2.1
    obtain ⟨ht, hn, hm, hd, hC, hi, hc, hl, hr, hmass⟩ := hcd
    have hh := hc g z
    change ((Layer.lists (a.ls k ℓ) g z).card : ℝ) ≤
      a.original k ^ (Real.log (a.H k) / Real.log (a.original k)) at hh
    have hpow : a.original k ^ (Real.log (a.H k) / Real.log (a.original k)) = a.H k :=
      ha.scales.original_rpow_log_factor k
    rw [hpow] at hh
    exact hh
  · intro k ℓ g i
    have hcd := (ha.layer k ℓ).2.2.1
    obtain ⟨ht, hn, hm, hd, hC, hi, hc, hl, hr, hmass⟩ := hcd
    exact hl g i
  · intro k ℓ g
    let q := a.ls k ℓ
    obtain ⟨hr0, hr1, hcd, hw, hsupport⟩ := ha.layer k ℓ
    obtain ⟨ht, hn, hm, hd, hC, hi, hc, hl, hr, hmass⟩ := hcd
    let B : Fin (Layer.n q) → Set Inc := fun i =>
      {z | Layer.world q i = g ∧ z ∈ Layer.selected q i ∧
        i ∉ Layer.lists q g (a.tangentData.observation k z)}
    have hB (i : Fin (Layer.n q)) : a.ρ k g (B i) = 0 := by
      by_cases hworld : Layer.world q i = g
      · have horig := hr i
        have hsub : B i ⊆ {z | z ∈ Layer.selected q i ∧
            i ∉ Layer.lists q (Layer.world q i) (a.tangentData.observation k z)} := by
          intro z hz
          exact ⟨hz.2.1, by simpa only [hworld] using hz.2.2⟩
        apply le_antisymm _ bot_le
        apply (measure_mono hsub).trans
        apply (ha.rho_le k g _).trans
        have heq : g = Layer.world q i := hworld.symm
        rw [heq]
        exact le_of_eq horig
      · have hempty : B i = ∅ := by
          ext z
          simp only [B, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun hz => hworld hz.1
        rw [hempty, measure_empty]
    have hU : a.ρ k g (⋃ i, B i) = 0 := measure_iUnion_null_iff.mpr hB
    have hsub : {z : Inc | ¬∃ i, Layer.world q i = g ∧
        z.1 ∈ Layer.prior q i ∧ z.2 ∈ I (Layer.T q) (Layer.time q i) ∧
        i ∈ Layer.lists q g (a.tangentData.observation k z)} ⊆
        {z | ∃ i, Layer.world q i = g ∧ z ∈ Layer.selected q i}ᶜ ∪ ⋃ i, B i := by
      intro z hz
      by_cases hs : ∃ i, Layer.world q i = g ∧ z ∈ Layer.selected q i
      · obtain ⟨i, hiworld, hiz⟩ := hs
        right
        apply Set.mem_iUnion.mpr
        refine ⟨i, hiworld, hiz, ?_⟩
        intro hiList
        have hinc := (hC i hiz).2
        exact hz ⟨i, hiworld, hinc.1, hinc.2, hiList⟩
      · exact Or.inl hs
    exact measure_mono_null hsub (measure_union_null (hsupport g) hU)

end PreparedData

/-- The two geometric contracts compose with proved globalization and the original guard. -/
theorem prepared_not_STI_of_split
    (hcompare : Comparison) (hencode : Encoding) : Prepared → ¬STI := by
  apply prepared_not_STI_of_conversion
  intro a ha hSTI
  obtain ⟨θ, hθ, hθ1, hconvert⟩ :=
    hcompare a.tangentData ha.tangentData_valid ha.tangentData_terminalKnown
  obtain ⟨R₀, center, c, C, hR₀, hcenter, hc0, hc1, hC, hcovered⟩ :=
    PreparedData.frequent_centered_cover ha hSTI hθ hθ1
  obtain ⟨R, gain, C', p, hR, hgain, hC', hlisted⟩ :=
    hconvert R₀ center c C hR₀ hcenter hc0 hc1 hC hcovered
  exact hencode a ha.encoding_core R gain C' p hR hgain hC' hlisted

end Submission.Obl.k4_scalar_candidate_original_return
