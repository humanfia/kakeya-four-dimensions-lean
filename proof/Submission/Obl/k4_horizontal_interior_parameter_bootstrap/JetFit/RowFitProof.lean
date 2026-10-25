import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.Bridge
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.RowFitNumerics

/-!
# Part I of the first jet: `FirstJet.RowFitComponent`

x0854's statement of "Fitting one row component" (paper Proposition 5.4) follows from
`block_fit` (the sliced planar fit on one block, proved from the Wang-Zahl planar dichotomy)
through the bridge `jetHyp_of_data` (constant `K₁ = 10 K³`, `K = N^η`), with the planar scale
`p = H^(1/4)`, the block mass floor `τ = N^(-η)` and the constant `Ks = 224 K₁⁵ / τ² = Cs N^(17η)`.
The error `H (12 Ks + 2) p + K₁ ζ` is at most `N^ε₁ H^(5/4)`, the slope at most `6 Ks + 1 ≤ N^ε₁`
and the fitting set has length `≥ H p^ε / (5 C0 Ks · 36864 Ks^16) ≥ N^(-ε₁) H`
(`block_numerics`, `fit_outputs`). The second component is the first one of the swapped chart.
The per-time floor of the statement is not needed.
-/

open MeasureTheory Set Filter

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

set_option maxHeartbeats 4000000 in
/-- **Part I of the first jet** (x0854's `FirstJet.RowFitComponent`). -/
theorem rowFitComponent : FirstJet.RowFitComponent := by
  intro d hd hd1 c' c'' hc' hc'c'' ε₁ hε₁
  have hc''pos : 0 < c'' := hc'.trans_le hc'c''
  set ε : ℝ := min (ε₁ / (8 * c'')) ((1 - d) / 2) with hε_def
  have hε : 0 < ε := lt_min (by positivity) (by linarith)
  have hε2 : ε ≤ (1 - d) / 2 := min_le_right _ _
  have hεc : ε ≤ ε₁ / (8 * c'') := min_le_left _ _
  have hεd : ε + d < 1 := by linarith
  obtain ⟨ηb, δ₀, hηb, hδ₀, hbf⟩ := block_fit hε hd hd1 hεd
  have hev := rowFitConds_eventually hηb hδ₀ hd hd1 hc' hc'c'' hε₁ hε hε2 hεc
  set η : ℝ := min (c' * ηb * (1 - d) / 2000) (min (c' / 400) (ε₁ / 400)) with hη_def
  have hη : 0 < η := by
    have : 0 < 1 - d := by linarith
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  refine ⟨η, hη, max N₁ 2, le_max_right _ _, ?_⟩
  intro N hN Ω _ ν hν y β γ E F ζ hζ hD H t₀ hH1 hH2 hζH ht₀ ht₀H hmass htime
  have := hν
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hC := hN₁ N (le_trans (le_max_left _ _) hN)
  have hK1 : 1 ≤ N ^ η := Real.one_le_rpow hN1 hη.le
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hH1
  have hHle1 : H ≤ 1 := hH2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
  have hζ1 : ζ ≤ 1 := hζH.trans (pow_le_one₀ hH0.le hHle1)
  have hJ := jetHyp_of_data hD hK1 hd hζ hζ1
  obtain ⟨hp0, hp1, hKs1, hδ, hc1, hc2, hc3, hc4⟩ :=
    block_numerics hN1 hη hηb hc' hd hεd hH1 hH2 hC
  obtain ⟨hHp, hζHp, hKs, hσ, herr, hvol⟩ :=
    fit_outputs hN1 hη hε hH0 hH1 hHle1 hζ hζH hC.hf hC.hg
  have hτ0 : 0 < N ^ (-η) := Real.rpow_pos_of_pos hN0 _
  have hτ1 : N ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hset : E ∩ Set.univ ×ˢ Set.Icc t₀ (t₀ + H) = E ∩ {q | q.2 ∈ Icc t₀ (t₀ + H)} := by
    ext q; simp
  rw [hset] at hmass
  have hK10 : 1 ≤ 10 * (N ^ η) ^ 3 := by
    have := le_ten_mul_cube hK1; linarith
  -- the fit of component `0` of any chart with the same prior and labels
  have key : ∀ D' : JetData Ω, JetHyp D' ζ (10 * (N ^ η) ^ 3) d → D'.ν = ν → D'.E = E →
      ∃ T : Set ℝ, MeasurableSet T ∧ T ⊆ Icc t₀ (t₀ + H) ∧ (∀ t ∈ T, ∃ l, (l, t) ∈ E) ∧
        ENNReal.ofReal (N ^ (-ε₁) * H) ≤ volume T ∧
        ∃ a A : ℝ, |A| ≤ N ^ ε₁ ∧ ∀ t ∈ T, |D'.F t 0 - (a + (t - t₀) * A)| ≤
          N ^ ε₁ * H ^ (5 / 4 : ℝ) := by
    intro D' hJ' hν' hE'
    have hmass' : ENNReal.ofReal (N ^ (-η) * H) ≤
        (D'.ν.prod volume) (D'.E ∩ {q | q.2 ∈ Icc t₀ (t₀ + H)}) := by
      rw [hν', hE']; exact hmass
    obtain ⟨σ, c, hσb, T, hTm, hTsub, hTlab, hTvol, hfit⟩ :=
      hbf (H ^ (1 / 4 : ℝ)) (Cs * N ^ (17 * η)) hp0 hp1 hKs1 hδ hc1 hc2 hc3 hc4 D' ζ
        (10 * (N ^ η) ^ 3) (N ^ (-η)) H t₀ D'.E hJ' hK10 hτ0 hτ1 hKs (subset_refl _)
        hJ'.measE hH0 hHle1 hHp hζ hζHp hmass'
    refine ⟨T, hTm, hTsub, ?_, ?_, c + σ * t₀, σ, hσb.trans hσ, ?_⟩
    · intro t ht
      have h := hTlab t ht
      by_contra hne
      push Not at hne
      have : {l | (l, t) ∈ D'.E} = ∅ := by
        ext l
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rw [hE']; exact hne l
      rw [this, measure_empty] at h
      exact lt_irrefl _ h
    · exact (ENNReal.ofReal_le_ofReal hvol).trans hTvol
    · intro t ht
      have h := hfit t ht
      calc |D'.F t 0 - (c + σ * t₀ + (t - t₀) * σ)| = |D'.F t 0 - (c + σ * t)| := by ring_nf
        _ ≤ _ := h
        _ ≤ _ := herr
  intro i
  fin_cases i
  · exact key (ofData ν y β γ E F) hJ rfl rfl
  · obtain ⟨T, h1, h2, h3, h4, a, A, h5, h6⟩ := key (ofData ν y β γ E F).swap hJ.swap rfl rfl
    refine ⟨T, h1, h2, h3, h4, a, A, h5, fun t ht => ?_⟩
    have := h6 t ht
    simpa [JetData.swap_F, swap2_zero, ofData] using this

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
