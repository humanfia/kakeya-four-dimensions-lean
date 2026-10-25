import Submission.Obl.k4_finite_width_output_exclusion.Scenarios

set_option maxRecDepth 4096

namespace Submission.Obl.k4_finite_width_output_exclusion

open MeasureTheory Filter

noncomputable section

lemma eventual_sample_exclusion {p : Data} (hp : Valid p) {m : ℕ} (s : ℕ → ℝ)
    {kr ell Δ zeta e : ℝ} (hkr : 0 ≤ kr) (hΔ : 0 < Δ) (he : 0 ≤ e)
    (hno : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
      NoImprovement (p.reindex φ) kr ell Δ zeta e) (M D : ℕ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ k in atTop,
      ¬ ∃ sc : Scenario m, Sample p k M D τ s kr ell Δ zeta e sc := by
  classical
  by_contra hbad
  push Not at hbad
  let τ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hτpos (n : ℕ) : 0 < τ n := by dsimp [τ]; positivity
  have hτlim : Tendsto τ atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hex (n : ℕ) : ∃ k : ℕ, n ≤ k ∧ ∃ sc : Scenario m,
      Sample p k M D (τ n) s kr ell Δ zeta e sc :=
    frequently_atTop.1 (hbad (τ n) (hτpos n)) n
  choose φ hφge hφdata using hex
  have hφ : Tendsto φ atTop atTop := tendsto_atTop_mono hφge tendsto_id
  simp only [Sample] at hφdata
  choose sc r a hr hrΔ hdepth htime hwidth hknown using hφdata
  have hfinite : ∃ sc₀ : Scenario m, ∃ᶠ n in atTop, sc n = sc₀ := by
    apply frequently_exists.1
    exact (Eventually.of_forall (fun n => ⟨sc n, rfl⟩)).frequently
  obtain ⟨sc₀, hsc₀⟩ := hfinite
  obtain ⟨ψ, hψ, hψsc⟩ := subseq_forall_of_frequently (p := fun n => sc n = sc₀) tendsto_id hsc₀
  change Tendsto ψ atTop atTop at hψ
  change ∀ n, sc (ψ n) = sc₀ at hψsc
  have hrbound (n : ℕ) : r (ψ n) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hr (ψ n), by linarith [hrΔ (ψ n)]⟩
  obtain ⟨r₀, hr₀, ξ, hξ, hrlim⟩ := isCompact_Icc.tendsto_subseq hrbound
  let θ : ℕ → ℕ := fun n => φ (ψ (ξ n))
  have hθ : Tendsto θ atTop atTop := hφ.comp (hψ.comp hξ.tendsto_atTop)
  have hq : Valid (p.reindex θ) := valid_reindex hp hθ
  have htlim : Tendsto (fun n => τ (ψ (ξ n))) atTop (nhds 0) :=
    hτlim.comp (hψ.comp hξ.tendsto_atTop)
  have hlimΔ : r₀ + Δ ≤ 1 :=
    le_of_tendsto (hrlim.add_const Δ) (Eventually.of_forall (fun n => hrΔ (ψ (ξ n))))
  have hlimsc : scenarioDepth s Δ e r₀ sc₀ := by
    apply (scenarioDepth_closed s Δ e sc₀).mem_of_tendsto hrlim
    apply Eventually.of_forall
    intro n
    simpa only [Function.comp_apply, Set.mem_setOf_eq, hψsc (ξ n)] using hdepth (ψ (ξ n))
  have hknownlim : Known (p.reindex θ) r₀ (scenarioTime s kr Δ e sc₀)
      (scenarioWidth s ell Δ zeta sc₀) := by
    apply known_of_convergent (M := M) (D := D) hq hrlim htlim
    intro n
    refine ⟨Atlas.reindex (φ := θ) (k := n) (a (ψ (ξ n))), ?_, ?_, ?_⟩
    · simpa only [Data.reindex, Atlas.reindex, θ, Function.comp_apply, hψsc (ξ n)]
        using htime (ψ (ξ n))
    · intro b
      simpa only [Data.reindex, Atlas.reindex, θ, Function.comp_apply, hψsc (ξ n)]
        using hwidth (ψ (ξ n)) b
    · exact hknown (ψ (ξ n))
  exact not_known_scenario hkr he (hno θ hθ) s sc₀ hr₀.1 hlimΔ hlimsc hknownlim

lemma eventual_improved_exclusion {p : Data} (hp : Valid p) (hpL : p.L = 1)
    {m : ℕ} (s : ℕ → ℝ) {kr ell Δ zeta e : ℝ}
    (hkr : 0 ≤ kr) (hΔ : 0 < Δ) (he : 0 ≤ e)
    (hno : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
      NoImprovement (p.reindex φ) kr ell Δ zeta e) (M D : ℕ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ k in atTop,
      ∀ (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ),
        PathBounds p k m s kr ell zeta e r T nw → ¬ Improved p k M D τ Δ kr m r T nw := by
  obtain ⟨τ, hτ, ht⟩ := eventual_sample_exclusion hp s hkr hΔ he hno M D
  refine ⟨τ, hτ, ht.mono ?_⟩
  intro k hk r T nw hp' hout
  exact hk (improved_to_sample hp hpL hτ.le hΔ hp' hout)

end
end Submission.Obl.k4_finite_width_output_exclusion
