import Submission.Obl.k4_finite_width_critical_contradiction.SplitBridges

/-! Assemble the true path with the independent exclusion at one late sample. -/
namespace Submission.Obl.k4_finite_width_critical_contradiction

open Filter

/-- The three geometric children suffice; finite cutoff optimization is already proved. -/
theorem finite_width_of_path_and_exclusion
    (composition : KnownCompositionExpanded)
    (paths : PathRealizationExpanded) (exclude : OutputExclusionExpanded) :
    InitialHorizonExpanded → ImprovementPrinciple →
      ∀ ds kr S η : ℝ, 0 < S → 0 < η → ExpandedExtremalSetup ds kr S η →
        ¬ ExpandedBoundedWidth ds kr S η := by
  intro hi hx ds kr S η hS hη hes hbw
  have es := expandedExtremalSetup_to_named hes
  obtain ⟨ell, hell, _, hlower, habove⟩ := es.exists_optimal_width
    (initialHorizon_iff.mp hi) (expandedBoundedWidth_to_named hbw)
  have lower : ∀ z : ℝ, 0 < z →
      UniformWidthExpanded ds kr S η (max 0 (ell - z)) :=
    fun z hz => uniformWidth_of_named (hlower z hz)
  obtain ⟨m, s, hm, hs0, hstep, hlast, Δ, δ0, hΔ, hδ0, engine⟩ :=
    hx ds kr ell S η es.dimension_nonneg es.dimension_lt_one es.rate_pos
      es.rate_le_one hell hS hη
  have grid : 0 < m ∧ 0 < s 0 ∧
      (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1 :=
    ⟨hm, hs0, hstep, hlast⟩
  let zeta := min (Δ / 32) (δ0 / 8)
  have hzeta : 0 < zeta := lt_min (by positivity) (by positivity)
  have hzetagain : 16 * zeta < Δ := by
    have := min_le_left (Δ / 32) (δ0 / 8)
    dsimp [zeta]
    linarith
  have hzetawidth : 4 * zeta ≤ δ0 := by
    have := min_le_right (Δ / 32) (δ0 / 8)
    dsimp [zeta]
    linarith
  obtain ⟨a, ha, bad⟩ := badFamily_of_named (habove zeta hzeta)
  obtain ⟨e, t, he, heδ0, ht, no_output⟩ :=
    exclude composition hi ds kr ell S η hS hη hes hell lower zeta a Δ δ0
      hzeta hzetagain ha hδ0 m s grid
  obtain ⟨tprof, htprof, profile⟩ := hes.2.2.2.2.2.2 δ0 hδ0
  let t' := min t tprof
  have ht' : 0 < t' := lt_min ht htprof
  obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp, hd, hH, hnot,
      Mp, Dp, path_samples⟩ :=
    paths composition hi ds kr ell S η hS hη hes hell lower zeta a hzeta ha bad
      m s grid e t' he ht'
  have hd_t : d < ds + t := by
    have := min_le_left t tprof
    dsimp [t'] at hd
    linarith
  have hH_t : kr - t < ExpandedHorizon N K 1 W ω ν E B f :=
    lt_of_le_of_lt (sub_le_sub_left (min_le_left _ _) _) hH
  have hd_prof : d < ds + tprof := by
    have := min_le_right t tprof
    dsimp [t'] at hd
    linarith
  have hH_prof : (kr - tprof) * 1 < ExpandedHorizon N K 1 W ω ν E B f := by
    simpa only [mul_one] using
      lt_of_le_of_lt (sub_le_sub_left (min_le_right t tprof) kr) hH
  have hprofile := profile N K 1 d W ω ν E P B f g G hp hd_prof hH_prof
  obtain ⟨Mi, Di, improve⟩ := engine N K 1 d W ω ν E P B f g G hp hprofile Mp Dp
  obtain ⟨τ, hτ, no_output_late⟩ :=
    no_output N K d W ω ν E P B f g G hp hd_t hH_t hnot Mi Di
  obtain ⟨σ, hσ, k0, improve_late⟩ := improve τ hτ
  obtain ⟨k, hpath, hlate, hguard⟩ :=
    ((path_samples σ hσ).and_eventually
      ((eventually_ge_atTop k0).and no_output_late)).exists
  obtain ⟨r, T, nw, κ, C, lev, par, γ, j, c, u, Q, R, A, F, lst,
      hκ, hκN, hC, hr, hnodes, hlists, hdisjoint, hcharts⟩ := hpath
  have hN : 1 ≤ N k := le_trans (by norm_num) (hp.1 k)
  apply hguard r T nw
  · refine ⟨hr, fun i hi => ?_⟩
    obtain ⟨hri, hri_pos, hTlo, hThi, hnwi, _⟩ := hnodes i hi
    exact ⟨hri, hri_pos, hTlo, hThi, hnwi⟩
  · have output := improve_late k hlate r T nw κ C lev par γ j c u Q R A F lst
      hκ hκN hC hr
    simp only [mul_one] at output
    apply output
    · intro i hi
      obtain ⟨hri, hri_pos, hTlo, hThi, hnwi, hmass⟩ := hnodes i hi
      refine ⟨hri.trans heδ0, hri_pos, ?_, ?_, hnwi.trans hzetawidth, hmass⟩
      · exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans hTlo
      · exact hThi.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
    · exact hlists
    · exact hdisjoint
    · intro b
      obtain ⟨hlev, hj, hchart⟩ := hcharts b
      refine ⟨hlev, hj, ?_⟩
      rcases hchart with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,hex⟩
      refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,?_⟩
      rcases hex with ⟨hfloor, hupper, hdetlo, hdethi, hlist, hpar⟩
      refine ⟨hfloor,hupper,?_,?_,hlist,hpar⟩
      · exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans hdetlo
      · exact hdethi.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))

end Submission.Obl.k4_finite_width_critical_contradiction
