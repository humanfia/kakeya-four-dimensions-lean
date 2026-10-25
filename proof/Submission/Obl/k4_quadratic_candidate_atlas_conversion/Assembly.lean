import Submission.Obl.k4_quadratic_candidate_atlas_conversion.Monotonicity
import Submission.Obl.k4_quadratic_finite_greedy_cover
import Submission.Obl.k4_stable_quadratic_hidden_sheets
import Submission.Obl.k4_algebraic_sheet_remez
import Submission.Obl.k4_quadratic_cover_to_analytical_atlas
import Submission.Obl.k4_original_observation_atlas_encoding
import Submission.Obl.k4_local_algebraic_graph_matching
import Submission.Obl.k4_quadratic_candidate_atlas_conversion.JetControl

set_option linter.unusedVariables false

namespace Submission.Obl.k4_quadratic_candidate_atlas_conversion

/-- Extract exactly the original-law bounds needed for list encoding. -/
theorem prob_temperedLaw
    {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    (h : prob N K L d S η W ω ν E P B f g G) :
    ∃ M D : ℕ, ∀ k, temperedLaw (N k) M D (W k) (ω k) (ν k) (B k) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hdata⟩
  rcases hdata.1 with ⟨M, D, hall⟩
  refine ⟨M, D, ?_⟩
  intro k
  rcases hall k with ⟨hW, hω, hsum, hworlds, _⟩
  refine ⟨hW, hω, hsum, ?_⟩
  intro w
  rcases hworlds w with ⟨hν, hB, hBup, hBinv, _, _, hprior, _⟩
  exact ⟨hν, hB, hBup, hBinv, hprior⟩

/-- Composition of the concrete child certificates. All remaining operations
are choice of smaller slacks, later cutoffs, and monotone enlargement. -/
theorem conversion_from_children : Conversion := by
  have hgreedy : GreedyCoverage := Submission.k4_quadratic_finite_greedy_cover
  have hanalytic : AnalyticalConversion := Submission.k4_quadratic_cover_to_analytical_atlas
  have hencoding : OriginalEncoding := Submission.k4_original_observation_atlas_encoding
  have hstable : stableSheets := Submission.k4_stable_quadratic_hidden_sheets
  have hremez : algebraicRemez := Submission.k4_algebraic_sheet_remez
  have hjets : algebraicJets := algebraicJets_available
  intro hmatching d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  have hlocal : localGraph := Submission.k4_local_algebraic_graph_matching hmatching
  obtain ⟨α, ρ, hα, hαup, hρ, hdρ, hconvert⟩ :=
    hanalytic hlocal hjets hstable hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  refine ⟨α, ρ, hα, hαup, hρ, hdρ, ?_⟩
  intro S η hS hη m s gain δ₀ hgrid hgain hgainup hδ₀ hδ₀up hdiscovery
  intro N K L d W ω ν E P B f g G hprob hf Mp Dp
  obtain ⟨Mg, Dg, hcover⟩ := hgreedy d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1
    hS hη hρ hdρ m s gain δ₀ hgrid hgain hgainup hδ₀ hδ₀up hdiscovery
    N K L d W ω ν E P B f g G hprob hf Mp Dp
  obtain ⟨Mi, Di, hpre⟩ := hconvert S η hS hη m s gain δ₀ hgrid hgain
    hgainup hδ₀ hδ₀up N K L d W ω ν E P B f g G hprob hf Mp Dp Mg Dg
  obtain ⟨Mν, Dν, hlaw⟩ := prob_temperedLaw hprob
  have hL : 0 < L := hprob.2.2.2.1
  obtain ⟨Me, De, hMi, hDi, hencode⟩ := hencoding L hL Mν Dν Mi Di
  refine ⟨max Mg Me, max Dg De, ?_⟩
  intro τ hτ
  let ζ : ℝ := min (τ / 4) (1 / 8)
  have hζ : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζτ : ζ ≤ τ / 4 := min_le_left _ _
  have hζsmall : ζ ≤ 1 / 8 := min_le_right _ _
  have hζone : ζ ≤ 1 := hζsmall.trans (by norm_num)
  obtain ⟨ε, σc, hε, hεone, hεζ, hσc, kc, hpreAt⟩ := hpre ζ hζ hζone
  obtain ⟨σg, hσg, kg, hcoverAt⟩ := hcover ε hε hεone
  obtain ⟨N₀, hN₀, hencodeAt⟩ := hencode τ hτ
  obtain ⟨ke, hke⟩ := Filter.eventually_atTop.mp (hprob.2.1.eventually (Filter.eventually_ge_atTop N₀))
  refine ⟨min σg σc, lt_min hσg hσc, max (max kg kc) ke, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hp
  have hNk : 1 ≤ N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hprob.1 k)
  have hkg : kg ≤ k := (le_max_left kg kc).trans ((le_max_left (max kg kc) ke).trans hk)
  have hkc : kc ≤ k := (le_max_right kg kc).trans ((le_max_left (max kg kc) ke).trans hk)
  have hke' : ke ≤ k := (le_max_right (max kg kc) ke).trans hk
  have hpG := path_mono_exponent hNk (min_le_left σg σc) hp
  have hpC := path_mono_exponent hNk (min_le_right σg σc) hp
  change ImprovementAt (N k) L (W k) (ω k) (ν k) (E k) (B k) κ₁ (α * gain)
    m r T nw (max Mg Me) (max Dg De) τ
  rcases hcoverAt k hkg r T nw κ C lev par γ j c u Q R A F lst hpG with hw | hcov
  · have hΔ : α * gain ≤ gain := by nlinarith
    have hi := width_improvementAt (N k) L (W k) (ω k) (ν k) (E k) (B k)
      κ₁ gain (α * gain) m r T nw Mg Dg ε hNk hL.le hgain.le hΔ hw
    exact improvementAt_mono hNk (le_max_left Mg Me) (le_max_left Dg De)
      (hεζ.trans (hζτ.trans (by linarith))) hi
  · have hpout := hpreAt k hkc r T nw κ C lev par γ j c u Q R A F lst hpC hcov
    rcases hpout with ⟨r₂, T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
      hroom, htime, hcount, hdisj, hlist, hlistmeas, hcharts, hmass⟩
    obtain ⟨F', lst', hsub, hlist', hcharts', hmass'⟩ :=
      hencodeAt (N k) (hke k hke') (W k) (ω k) (ν k) (B k) (E k) (hlaw k)
        ζ r₂ T₂ C₂ γ₂ j₂ c₂ u₂ Q₂ R₂ A₂ F₂ lst₂ hζ hζτ hζsmall hcount
        hlist hlistmeas hcharts hmass
    have hi : ImprovementAt (N k) L (W k) (ω k) (ν k) (E k) (B k) κ₁ (α * gain)
        m r T nw Me De τ := by
      refine ⟨r₂, T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F', lst',
        hroom, ?_, hcount.trans (pow_le_pow_right₀ hNk hMi), hdisj,
        hlist', hcharts', hmass'⟩
      rcases htime with hfirst | ⟨i, hi, hr, ht⟩
      · exact Or.inl hfirst
      · exact Or.inr ⟨i, hi, Or.inl ⟨hr, ht⟩⟩
    exact improvementAt_mono hNk (le_max_right Mg Me) (le_max_right Dg De) le_rfl hi

end Submission.Obl.k4_quadratic_candidate_atlas_conversion
