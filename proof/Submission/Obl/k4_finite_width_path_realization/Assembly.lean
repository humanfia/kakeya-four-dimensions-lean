import Submission.Obl.k4_finite_width_path_realization.Children
import Submission.Obl.k4_finite_width_path_realization.PreparationBridge
import Submission.Obl.k4_finite_width_path_realization.WidthBridge
import Submission.Obl.k4_finite_width_path_realization.TerminalLayer
import Submission.Obl.k4_finite_width_path_realization.WidthNumerics

namespace Submission.Obl.k4_finite_width_path_realization

open MeasureTheory Filter

set_option linter.unusedVariables false

/-- The upper width bound is a consequence of badness, after the geometric
construction and finite ancestor-preserving selection. -/
theorem assemble_paths (prep : ForestPreparationExpanded)
    (raw : RawCriticalForestsExpanded) (sel : ForestWidthSelectionExpanded) :
    PathRealizationExpanded := by
  intro comp ih ds kr ell S η hS hη hes hell hU zeta a hζ ha hbad m s hs e t he ht
  obtain ⟨eps, q, lam, heps, heps_e, heps_one, heps_a, heps_mul,
    hq, hlam, hlam_e, hlam_ζ, herr⟩ := path_error_budgets (m := m) hell hζ he ha
  let z := zeta / 4
  let w := max 0 (ell - z)
  have hz : 0 < z := by dsimp [z]; positivity
  have hw0 : 0 ≤ w := le_max_left _ _
  have hwell : w ≤ ell := max_le hell (by dsimp [z]; linarith)
  have hwdiff : ell - w ≤ z := by
    have := le_max_right (0 : ℝ) (ell - z)
    dsimp [w]
    linarith
  obtain ⟨u, hu, hraw⟩ := raw prep comp ih ds kr S η w hS hη hes hw0 (hU z hz)
    m s hs eps q heps heps_one hq
  obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp, hd, hH, hnot⟩ :=
    hbad (min u t) (lt_min hu ht)
  let p : Data := ⟨N, K, 1, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
  have hp' : p.Valid := hp
  have hdu : d < ds + u := hd.trans_le (by linarith [min_le_left u t])
  have hHu : kr - u < ExpandedHorizon N K 1 W ω ν E B f :=
    lt_of_le_of_lt (by linarith [min_le_left u t]) hH
  obtain ⟨r, Mr, Dr, hrlast, hr, hforests⟩ :=
    hraw N K d W ω ν E P B f g G hp hdu hHu
  obtain ⟨Mp, Dp, hprepare⟩ := prepare_forests prep hp' m r hs.1
    (fun i hi => ⟨(hr i hi).2.1, (hr i hi).2.2⟩) Mr Dr
  obtain ⟨Bc, hBc, hselect⟩ := select_forest_widths sel m Mr lam hs.1 hlam
  have hnot' : ¬ NarrowTerminal p (kr + a) (ell + zeta) :=
    fun h => hnot ((expandedNarrowTerminal_iff p _ _).mpr h)
  obtain ⟨τ, hτ, hguard⟩ := terminal_width_bound (M := Mp) (D := Dp) hp' hs.1 hnot'
  refine ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp,
    hd.trans_le (by linarith [min_le_right u t]),
    lt_of_le_of_lt (by linarith [min_le_right u t]) hH, hnot, Mp, Dp, fun σ hσ => ?_⟩
  let δs := min (σ / 2) (τ / 2)
  have hδs : 0 < δs := lt_min (by positivity) (by positivity)
  have hδσ : δs + δs ≤ σ := by have := min_le_left (σ / 2) (τ / 2); dsimp [δs]; linarith
  have hδτ : δs + δs ≤ τ := by have := min_le_right (σ / 2) (τ / 2); dsimp [δs]; linarith
  obtain ⟨ρ, hρ, hprep⟩ := hprepare δs hδs
  have hBpow : ∀ᶠ k in atTop, (Bc : ℝ) ≤ N k ^ δs :=
    ((tendsto_rpow_atTop hδs).comp hp'.2.1).eventually_ge_atTop _
  apply (((hforests ρ hρ).and_eventually hprep).and_eventually (hguard.and hBpow)).mono
  intro k hk
  rcases hk with ⟨⟨hkraw, hkprep⟩, hkguard, hkB⟩
  rcases hkraw with ⟨κ, T, C, lev, par, γ, j, c, u₀, Q, R, A, F, vwidth,
    hκ, hcore, htime, hwidth⟩
  let x : Forest p k := ⟨κ, T, C, lev, par, γ, j, c, u₀, Q, R, A, F, vwidth, fun _ _ _ => ∅⟩
  obtain ⟨y, hyκ, hyT, hycore, hyprep, hybudget, hywidth⟩ := hkprep x w q
    (fun i hi => (htime i hi).2.2) hcore hκ hwidth
  obtain ⟨v, nw, hvκ, hvT, hvcore, hvprep, hveq, hvbin, hvlower⟩ :=
    hselect hp' y r w q hq.le hycore hyprep hybudget hywidth
  have hN : 1 ≤ N k := by linarith [hp'.N_ge k]
  have hNpos : 0 < N k := by linarith
  have hvκσ : v.κ ≤ N k ^ σ := by
    calc
      v.κ = (Bc : ℝ) * N k ^ δs := by rw [hvκ, hyκ]
      _ ≤ N k ^ δs * N k ^ δs := mul_le_mul_of_nonneg_right hkB (by positivity)
      _ = N k ^ (δs + δs) := (Real.rpow_add hNpos _ _).symm
      _ ≤ N k ^ σ := Real.rpow_le_rpow_of_exponent_le hN hδσ
  have hvκτ : v.κ ≤ N k ^ τ := by
    calc
      v.κ = (Bc : ℝ) * N k ^ δs := by rw [hvκ, hyκ]
      _ ≤ N k ^ δs * N k ^ δs := mul_le_mul_of_nonneg_right hkB (by positivity)
      _ = N k ^ (δs + δs) := (Real.rpow_add hNpos _ _).symm
      _ ≤ N k ^ τ := Real.rpow_le_rpow_of_exponent_le hN hδτ
  have hvtime (i : ℕ) (hi : i < m) :
      N k ^ (kr * s i - e) ≤ (2 : ℝ) ^ v.T i ∧
        (2 : ℝ) ^ v.T i ≤ N k ^ (kr * s i + e) := by
    rw [hvT, hyT]
    exact ⟨(Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans (htime i hi).1,
      ((htime i hi).2.1).trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))⟩
  have hvterminal : (2 : ℝ) ^ v.T (m - 1) ≤ N k ^ (kr + a) := by
    rw [hvT, hyT]
    have htlast := (htime (m - 1) (by omega)).2.1
    rw [hs.2.2.2, mul_one] at htlast
    exact htlast.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  have hnwlast : nw (m - 1) < ell + zeta + lam :=
    hkguard v r nw lam hvcore hrlast hvκτ hvterminal hveq hvbin
  have hnw (i : ℕ) (hi : i < m) : |nw i - ell * s i| ≤ 4 * zeta :=
    squeeze_width hell hζ (by dsimp [z]; rfl) ⟨hw0, hwell, hwdiff⟩ heps_mul
      hlam_ζ herr hrlast hnwlast i ⟨(hr i hi).2.1.le, (hr i hi).2.2⟩ (hr i hi).1
      (hvlower i hi).1 (hvlower i hi).2
  have hdet (b : Fin v.C) :
      N k ^ (-(nw (v.lev b) + e)) ≤ |Matrix.det (v.Q b)| * (4 : ℝ) ^ v.T (v.lev b) ∧
      |Matrix.det (v.Q b)| * (4 : ℝ) ^ v.T (v.lev b) ≤ N k ^ (-(nw (v.lev b) - e)) := by
    have hb := abs_le.mp (hvbin b)
    rw [← hveq b]
    exact ⟨Real.rpow_le_rpow_of_exponent_le hN (by linarith),
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)⟩
  refine ⟨r, v.T, nw, v.κ, v.C, v.lev, v.par, v.γ, v.j, v.c, v.u, v.Q, v.R,
    v.A, v.F, v.lst, hvcore.1, hvκσ, hvcore.2.2.1, hrlast, ?_, hvprep.1,
    hvcore.2.2.2.2.1, ?_⟩
  · intro i hi
    exact ⟨(hr i hi).1.trans heps_e, (hr i hi).2.1, (hvtime i hi).1,
      (hvtime i hi).2, hnw i hi, hvcore.2.2.2.1 i hi⟩
  · intro b
    obtain ⟨hlev, hj, hc, hpar⟩ := hvcore.2.2.2.2.2 b
    refine ⟨hlev, hj, ?_⟩
    apply Chart.mono hN le_rfl le_rfl (lt_of_lt_of_le zero_lt_one hvcore.1) le_rfl
      (hp'.B_pos k (v.γ b)).le _ hc
    intro hfloor
    exact ⟨hfloor, (hvprep.2 b).1, (hdet b).1, (hdet b).2, (hvprep.2 b).2, hpar⟩

end Submission.Obl.k4_finite_width_path_realization
