import Submission.Obl.k4_raw_localized_native_systems.C.Q2Binning
import Submission.Obl.k4_raw_localized_native_systems.C.Recombine
import Submission.Obl.k4_raw_localized_native_systems.C.GoodPathMass

/-
Adapted from this LOT tree, o178, session x0596, `FullTimeLocalization.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Full-time localization at one sample (paper, Section 10, Proposition 10.2)

For a later chart system (true at some depth, narrow, known by the terminal
observation with measurable lists), paired full-time binning is applied in every
world whose own bad-pair mass is small; the retained weighted mass of the
resulting full-time strips is at least the square of the weighted good-path
mass over four, minus the total bad-pair bound of `Q2TotalBad`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

/-- The bad-pair mass of one world. -/
def worldBad (a : Atlas p k) (γ : Fin (p.W k)) (hC : 0 < a.C) (u τ κ' lam g H : ℝ) : ENNReal :=
  ((p.ν k γ).prod (volume.prod volume))
    {z | (z.1, z.2.1) ∈ goodPath a γ u τ κ' lam ∧ (z.1, z.2.2) ∈ goodPath a γ u τ κ' lam ∧
      g * H < min ‖q2normal a (tagOf a γ hC (z.1, z.2.1)) - q2normal a (tagOf a γ hC (z.1, z.2.2))‖
        ‖q2normal a (tagOf a γ hC (z.1, z.2.1)) + q2normal a (tagOf a γ hC (z.1, z.2.2))‖}

/-- The good-path mass of one world. -/
def worldMass (a : Atlas p k) (γ : Fin (p.W k)) (u τ κ' lam : ℝ) : ℝ :=
  (((p.ν k γ).prod volume).restrict (goodPath a γ u τ κ' lam)).real Set.univ

theorem goodPath_subset_unit (hp : Valid p) (a : Atlas p k) (γ : Fin (p.W k)) {u τ κ' lam : ℝ}
    {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex) :
    goodPath a γ u τ κ' lam ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  intro q hq
  obtain ⟨⟨b, hb, hF, -⟩, -⟩ := hq
  have hsel := (hc.selected b hF).1
  rw [hb.1] at hsel
  exact ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.1 hsel

theorem worldBad_le_one (hp : Valid p) (a : Atlas p k) (γ : Fin (p.W k)) (hC : 0 < a.C)
    {u τ κ' lam g H : ℝ} {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex) :
    worldBad a γ hC u τ κ' lam g H ≤ 1 := by
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  haveI : IsProbabilityMeasure (p.ν k γ) := ((hfmt k).2.2.2.1 γ).1
  have hsub := goodPath_subset_unit hp a γ (u := u) (τ := τ) (κ' := κ') (lam := lam) hc
  unfold worldBad
  calc _ ≤ ((p.ν k γ).prod (volume.prod volume))
        (Set.univ ×ˢ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
        apply measure_mono
        intro z hz
        exact ⟨trivial, (Set.mem_prod.1 (hsub hz.1)).2, (Set.mem_prod.1 (hsub hz.2.1)).2⟩
    _ = 1 := by
        rw [Measure.prod_prod, Measure.prod_prod, Real.volume_Icc]
        simp

theorem worldMass_nonneg (a : Atlas p k) (γ : Fin (p.W k)) (u τ κ' lam : ℝ) :
    0 ≤ worldMass a γ u τ κ' lam := measureReal_nonneg

/-- **Full-time localization at one sample.** -/
theorem full_time_localization {CB : ℕ} (hCB2 : 2 ≤ CB) (hB : B0At CB) :
    ∀ (hp : Valid p) (a : Atlas p k) {M D : ℕ} {κ r : ℝ}
      {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
      (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
      (hknown : ∀ b, ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
      (κL : ℕ) (hcard : ∀ γ o, (a.lst γ o).card ≤ κL)
      (hmeas : ∀ γ b, MeasurableSet {o | b ∈ a.lst γ o})
      (hfloor : ∀ b, ENNReal.ofReal (p.N k ^ (-p.f r) * |(a.Q b).det| / ((2 : ℝ) ^ a.T * κ)) ≤
        priorMass p k (a.γ b) (a.F b))
      (hκ : 0 < κ)
      (hC : 0 < a.C) {u τ κ' lam ρ Kc KB g H : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
      (hκ' : 1 ≤ κ') (hκκ' : κ ≤ κ')
      (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ) (hKc : κ' + ρ ≤ Kc)
      (hKcB : 2 * Kc ≤ KB) (hκLB : (κL : ℝ) ≤ KB) (hκ'B : κ' ≤ KB) (hρB : ρ ≤ KB * g)
      (hK2 : 2 ≤ KB) (hg : 0 < g) (hgH : g * H ^ 2 ≤ 1) (hHB : (CB : ℝ) * KB ^ 2 ≤ H)
      (hρ0 : 0 ≤ ρ) (hpin : 8 * ρ / (g * H) ≤ δ (p.N k) u),
      ∃ S : Finset (Fin (p.W k)),
        (∀ γ ∈ S, ∃ (t₀ : ℝ) (m : ℕ) (rep : Fin m → Fin a.C) (A : Fin m → Set Line)
          (L : Observation → Finset (Fin m)),
          t₀ ∈ Set.Icc (0 : ℝ) 1 ∧ (m : ℝ) ≤ ((CB : ℝ) * KB / (g * H ^ 2)) ^ CB ∧
          Function.Injective (fun i => q2bin a Kc (g * H ^ 2) (rep i)) ∧
          (∀ i, A i = {l | (l, t₀) ∈ goodPath a γ u τ κ' lam ∧
            q2bin a Kc (g * H ^ 2) (tagOf a γ hC (l, t₀)) = q2bin a Kc (g * H ^ 2) (rep i)}) ∧
          (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
          (∀ i l, l ∈ A i → ∀ t ∈ Set.Icc (0 : ℝ) 1,
            |inner ℝ (q2normal a (rep i)) (y l 0 + t • v l) - q2intercept a Kc (rep i) -
              t * q2speed a Kc (rep i)| ≤ (CB : ℝ) * KB * (g * H ^ 2)) ∧
          (∀ o, ((L o).card : ℝ) ≤ (CB : ℝ) * KB) ∧ (∀ i, MeasurableSet {o | i ∈ L o}) ∧
          ENNReal.ofReal (worldMass a γ u τ κ' lam ^ 2 / 4) ≤
            (((p.ν k γ).prod volume).restrict (goodPath a γ u τ κ' lam))
              {q | ∃ i, q.1 ∈ A i ∧ i ∈ L (obs (p.B k γ) (δ (p.N k) p.L) q)}) ∧
        (∑ γ, p.ω k γ * worldMass a γ u τ κ' lam) ^ 2 / 4 -
            (ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
              (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
                ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r)))).toReal ≤
          ∑ γ ∈ S, p.ω k γ * (worldMass a γ u τ κ' lam ^ 2 / 4) := by
  have hstrips := q2_world_strips (p := p) (k := k) hCB2 hB
  intro hp a M D κ r ex hc hdisj hknown κL hcard hmeas hfloor hκ hC u τ κ' lam ρ Kc KB g H hu huη
    hκ' hκκ' hρ hKc hKcB hκLB hκ'B hρB hK2 hg hgH hHB hρ0 hpin
  classical
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hω0 : ∀ γ, 0 ≤ p.ω k γ := (hfmt k).2.1
  have hω1 : ∑ γ, p.ω k γ = 1 := (hfmt k).2.2.1
  -- the good worlds
  set S : Finset (Fin (p.W k)) := Finset.univ.filter (fun γ =>
    0 < (((p.ν k γ).prod volume).restrict (goodPath a γ u τ κ' lam)) Set.univ ∧
      worldBad a γ hC u τ κ' lam g H ≤ ENNReal.ofReal (worldMass a γ u τ κ' lam ^ 2 / 4)) with hS
  refine ⟨S, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨hpos, hbad⟩ := (Finset.mem_filter.1 hγ).2
    exact hstrips hp a γ hc hdisj hknown κL (hcard γ) (hmeas γ) hC hu huη hρ hKc hKcB hκLB
      hκ'B hρB hK2 hg hgH hHB hρ0 (by linarith) hpos hbad
  · -- recombination
    set X := ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
      (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
        ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r))) with hX
    have htot := q2_total_bad_pair_le hp a hc hdisj hknown κL hcard hmeas hfloor hκ hC (τ := τ) hu huη hκ'
      hκκ' hρ hKc hg (by
        have : 0 < (CB : ℝ) * KB ^ 2 := by
          have : (0 : ℝ) < CB := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hCB2)
          positivity
        linarith) hpin
    have hbadfin : ∀ γ, worldBad a γ hC u τ κ' lam g H ≠ ⊤ := fun γ =>
      ne_top_of_le_ne_top ENNReal.one_ne_top (worldBad_le_one hp a γ hC hc)
    have hXfin : X ≠ ⊤ := by
      simp only [hX]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    -- real form of the total bound
    have htotR : ∑ γ, p.ω k γ * (worldBad a γ hC u τ κ' lam g H).toReal ≤ X.toReal := by
      have h1 : (∑ γ, ENNReal.ofReal (p.ω k γ) * worldBad a γ hC u τ κ' lam g H).toReal ≤ X.toReal :=
        ENNReal.toReal_mono hXfin htot
      rw [ENNReal.toReal_sum (fun γ _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hbadfin γ))]
        at h1
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hω0 _)] using h1
    have hout : ∀ γ, γ ∉ S → worldMass a γ u τ κ' lam ^ 2 ≤ 4 * (worldBad a γ hC u τ κ' lam g H).toReal := by
      intro γ hγ
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_lt,
        not_le] at hγ
      rcases hγ with h0 | hlt
      · have hz : worldMass a γ u τ κ' lam = 0 := by
          unfold worldMass
          rw [measureReal_def, le_antisymm h0 bot_le, ENNReal.toReal_zero]
        rw [hz]
        have := ENNReal.toReal_nonneg (a := worldBad a γ hC u τ κ' lam g H)
        nlinarith
      · have h1 := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (hbadfin γ)).1 hlt
        linarith
    have hrec := recombine_worlds (p.ω k) (fun γ => worldMass a γ u τ κ' lam)
      (fun γ => (worldBad a γ hC u τ κ' lam g H).toReal) hω0 hω1 (fun γ => ENNReal.toReal_nonneg) S hout
    linarith

end

end Submission.Obl.k4_raw_localized_native_systems.C
