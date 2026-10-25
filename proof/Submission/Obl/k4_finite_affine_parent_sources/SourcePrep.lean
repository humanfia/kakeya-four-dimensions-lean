-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceFacts
import Submission.Obl.k4_finite_affine_parent_sources.SourceAssembly
import Submission.Obl.k4_finite_affine_parent_sources.FineGrid

/-!
# `SourceSamples` from the per-sample source inputs

`SourceInputsSpec` is the remaining preparation interface: after admissible bounds on the
tangent unit and the gain, and after the problem, its own candidate exponent, every late
sample has an original mixed candidate or a source stage (rotated parent frame, model loss
`(Nk^(uL))^θ`, source depth map) with a subpower floor and its true inputs.
`sourceSamples_of_spec` chooses the whole schedule and proves `SourceSamples`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Filter

noncomputable section

/-- Mixed candidates survive a larger coefficient exponent. -/
theorem mixedCandidate_mono {Nk L : ℝ} {W : ℕ} {ν : Fin W → Measure Trajectory}
    {B : Fin W → ℝ} {Mc Mc' : ℕ} {d₁ ρ gain ε : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {A : Fin C → Set Trajectory} {H : Fin W → Set Incidence}
    (hNk : 1 ≤ Nk) (hM : Mc ≤ Mc')
    (h : MixedCandidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j u Q A H) :
    MixedCandidate Nk L W ν B Mc' d₁ ρ gain ε r T C lev γ j u Q A H := by
  have hpow : Nk ^ Mc ≤ Nk ^ Mc' := pow_le_pow_right₀ hNk hM
  obtain ⟨b, hh, hg, h8, hroom, hpos, hcase⟩ := h
  refine ⟨b, hh, hg, h8, hroom, hpos, ?_⟩
  rcases hcase with ⟨R, hR, hcoeff, hmass⟩ | ⟨a, z, ha, hz, hmass⟩
  · exact Or.inl ⟨R, hR, fun e => (hcoeff e).trans hpow, hmass⟩
  · exact Or.inr ⟨a, z, ha, hz.trans hpow, hmass⟩

/-- Grid depths are nonnegative. -/
theorem fineGrid_nonneg {m : ℕ} {s : ℕ → ℝ} {gain ρ : ℝ} (h : FineGrid m s gain ρ) :
    ∀ i, i < m → 0 ≤ s i := by
  obtain ⟨⟨hm, hs0, hinc, -⟩, -, -⟩ := h
  intro i hi
  induction i with
  | zero => exact hs0.le
  | succ i ih =>
    have := hinc i (by omega)
    linarith [ih (by omega)]

/-- Grid mesh. -/
theorem fineGrid_mesh {m : ℕ} {s : ℕ → ℝ} {gain ρ : ℝ} (h : FineGrid m s gain ρ) :
    ∀ i, i + 1 < m → s (i + 1) - s i ≤ ρ * gain := h.2.2

/-- The schedule errors for `gain ≤ κ₁ u θ / (8 (1 + ℓ))`, `mesh = ρ gain`, `δ₀ = ρ gain / 2`. -/
theorem schedule_errors {n : ℕ} (hn : 2 ≤ n) {d₁ κ₁ ℓ ρ u gain : ℝ} (hd₁ : 0 ≤ d₁) (hd₁' : d₁ < 1)
    (hκ₁ : 0 < κ₁) (hκ₁' : κ₁ ≤ 1) (hℓ : 0 < ℓ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 4) (hu : 0 < u)
    (hg : 0 < gain)
    (hgain : gain ≤ κ₁ * u * (ρ / (1000000 * ((n : ℝ) + 1))) / (8 * (1 + ℓ))) :
    κ₁ * (ρ * gain) + 2 * (ρ * gain / 2) ≤ u * (ρ / (1000000 * ((n : ℝ) + 1))) ∧
    ρ * gain + 2 * (ρ * gain / 2) ≤ u * (ρ / (1000000 * ((n : ℝ) + 1))) / 2 ∧
    6 * (ρ * gain / 2) + d₁ * (ρ * gain + 2 * (ρ * gain / 2)) + ℓ * (ρ * gain) ≤
      u * (ρ / (1000000 * ((n : ℝ) + 1))) / 2 ∧
    2 * (ρ * gain / 2) ≤ κ₁ * (u / n - ρ * gain) ∧
    gain ≤ ρ * u / (1000000 * ((n : ℝ) + 1)) := by
  set θ := ρ / (1000000 * ((n : ℝ) + 1)) with hθ
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hθ0 : 0 < θ := by positivity
  have hθn : θ ≤ 1 / n := by
    rw [hθ, div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith
  have hℓ1 : (0 : ℝ) < 1 + ℓ := by linarith
  -- gain ≤ κ₁ u θ / 8 and ρ gain ≤ gain / 4
  have hg8 : gain ≤ κ₁ * u * θ / 8 := by
    refine hgain.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ κ₁ * u * θ := by positivity
    nlinarith
  have hρg : ρ * gain ≤ gain / 4 := by nlinarith
  have hκuθ : κ₁ * u * θ ≤ u * θ := by
    have : 0 ≤ u * θ := by positivity
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · -- (3 + 2 d₁ + ℓ) ρ gain ≤ (5 + ℓ) ρ gain ≤ (5 + ℓ) κ₁ u θ / (32 (1 + ℓ)) ≤ u θ / 2
    have hρg0 : 0 ≤ ρ * gain := by positivity
    have hd : d₁ * (ρ * gain) ≤ 1 * (ρ * gain) := mul_le_mul_of_nonneg_right hd₁'.le hρg0
    have h1 : 6 * (ρ * gain / 2) + d₁ * (ρ * gain + 2 * (ρ * gain / 2)) + ℓ * (ρ * gain) ≤
        (5 + ℓ) * (ρ * gain) := by
      have e : 6 * (ρ * gain / 2) + d₁ * (ρ * gain + 2 * (ρ * gain / 2)) + ℓ * (ρ * gain) =
          3 * (ρ * gain) + 2 * (d₁ * (ρ * gain)) + ℓ * (ρ * gain) := by ring
      rw [e]; linarith
    have h2 : (5 + ℓ) * (ρ * gain) ≤ (5 + ℓ) * (gain / 4) := by nlinarith
    have h3 : (5 + ℓ) * (gain / 4) ≤ (5 + ℓ) * (κ₁ * u * θ / (8 * (1 + ℓ))) / 4 := by nlinarith
    have h4 : (5 + ℓ) * (κ₁ * u * θ / (8 * (1 + ℓ))) / 4 ≤ 5 * (κ₁ * u * θ) / 32 := by
      rw [show (5 + ℓ) * (κ₁ * u * θ / (8 * (1 + ℓ))) / 4 =
        (5 + ℓ) / (1 + ℓ) * (κ₁ * u * θ) / 32 by field_simp; ring]
      have : (5 + ℓ) / (1 + ℓ) ≤ 5 := by rw [div_le_iff₀ hℓ1]; nlinarith
      have : 0 ≤ κ₁ * u * θ := by positivity
      nlinarith
    nlinarith
  · -- ρ gain (1 + κ₁) ≤ gain/2 ≤ κ₁ u θ / 16 ≤ κ₁ u / n
    have hun : u * θ ≤ u / n := by
      calc u * θ ≤ u * (1 / n) := mul_le_mul_of_nonneg_left hθn hu.le
        _ = u / n := by ring
    have : κ₁ * (u * θ) ≤ κ₁ * (u / n) := mul_le_mul_of_nonneg_left hun hκ₁.le
    nlinarith
  · calc gain ≤ κ₁ * u * θ / 8 := hg8
      _ ≤ u * θ := by nlinarith
      _ = ρ * u / (1000000 * ((n : ℝ) + 1)) := by rw [hθ]; ring

/-- A diverging scale eventually exceeds any fixed power target. -/
theorem eventually_rpow_ge {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) {c C : ℝ} (hc : 0 < c) :
    ∀ᶠ k in atTop, C ≤ N k ^ c := by
  have h1 : ∀ᶠ k in atTop, max 1 (|C| ^ (1 / c)) ≤ N k := hN.eventually_ge_atTop _
  filter_upwards [h1] with k hk
  have hN1 : 1 ≤ N k := le_trans (le_max_left _ _) hk
  have hN0 : 0 ≤ N k := by linarith
  have h2 : |C| ^ (1 / c) ≤ N k := le_trans (le_max_right _ _) hk
  calc C ≤ |C| := le_abs_self C
    _ = (|C| ^ (1 / c)) ^ c := by
        rw [← Real.rpow_mul (abs_nonneg C), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
    _ ≤ N k ^ c := Real.rpow_le_rpow (by positivity) h2 hc.le

/-- Absorb a factor into a power gap. -/
theorem mul_rpow_le_rpow {Nk C a b : ℝ} (hN : 0 < Nk) (hC : C ≤ Nk ^ (b - a)) :
    C * Nk ^ a ≤ Nk ^ b := by
  calc C * Nk ^ a ≤ Nk ^ (b - a) * Nk ^ a :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hN.le _)
    _ = Nk ^ b := by rw [← Real.rpow_add hN]; ring_nf

/-- **The remaining preparation interface.** -/
def SourceInputsSpec : Prop :=
  ∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 →
    ∀ n : ℕ, 2 ≤ n →
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ →
    ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ gain : ℝ, 0 < gain → gain ≤ g₀ →
    ∀ (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ), FineGrid m s gain ρ → 0 < δ₀ → δ₀ ≤ ρ * gain →
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
      (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
      ∀ Mp Dp : ℕ, ∃ Mprep : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ σp : ℝ, 0 < σp ∧ ∃ kp : ℕ, ∀ σ : ℝ, 0 < σ → σ ≤ σp → ∀ k, kp ≤ k →
      ∀ p : PathData (W k), p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (W k) → Set Incidence,
        (∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc (W k) p.C m p.lev p.world p.counted w) →
        (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
          ((ν k w).prod volume) (TerminalInc (W k) p.C m p.lev p.world p.counted w)) ≤
        ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod volume) (H w) →
        MixedCandidate (N k) L (W k) (ν k) (B k) Mprep d₁ ρ gain ε
          p.r p.T p.C p.lev p.world p.bin p.velocity p.frame p.assigned H ∨
        ∃ (D : SourceData p) (τ : ℝ),
          D.D₀ = MajorFrame.frame (p.frame D.parent) ∧
          D.K = (N k ^ (u * L)) ^ (ρ / (1000000 * ((n : ℝ) + 1))) ∧
          D.depth = sourceDepth m s D.i₀ u ∧
          s D.i₀ + u + δ₀ ≤ 1 / 2 ∧ 0 < τ ∧
          τ⁻¹ ≤ N k ^ (ε / 4000000) ∧
          τ⁻¹ ≤ N k ^ (u * (ρ / (1000000 * ((n : ℝ) + 1))) * L / 4) ∧
          τ⁻¹ ≤ N k ^ (1 / 2 : ℝ) ∧
          D.Inputs n m d₁ ℓ S u (N k) L τ (ν k) (B k) H

/-- **`SourceSamples` from the preparation interface.** -/
theorem sourceSamples_of_spec (h : SourceInputsSpec) : SourceSamples := by
  intro d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  obtain ⟨u₀, hu₀, hU⟩ := h d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set θ := ρ / (1000000 * ((n : ℝ) + 1)) with hθ
  have hθ0 : 0 < θ := by positivity
  set u := min u₀ (1 / (8 * n)) with hudef
  have hu : 0 < u := lt_min hu₀ (by positivity)
  have hun : u * n ≤ 1 / 8 := by
    have : u ≤ 1 / (8 * n) := min_le_right _ _
    calc u * n ≤ 1 / (8 * n) * n := mul_le_mul_of_nonneg_right this (by positivity)
      _ = 1 / 8 := by field_simp
  obtain ⟨g₀, hg₀, hG⟩ := hU u hu (min_le_left _ _)
  set gain := min g₀ (κ₁ * u * θ / (8 * (1 + ℓ))) with hgdef
  have hg : 0 < gain := lt_min hg₀ (by positivity)
  have hgle : gain ≤ κ₁ * u * θ / (8 * (1 + ℓ)) := min_le_right _ _
  obtain ⟨he1, he2, he3, hgap, hgθ⟩ := schedule_errors hn hd hd' hκ hκ' hℓ hρ hρ' hu hg hgle
  obtain ⟨m, s, hgrid⟩ := exists_fineGrid gain ρ hg hρ
  have hg8 : gain ≤ 1 / 8 := by
    have h1 : gain ≤ u * θ := by
      calc gain ≤ ρ * u / (1000000 * ((n : ℝ) + 1)) := hgθ
        _ = u * θ := by rw [hθ]; ring
    have h2 : u ≤ 1 := by
      have : u ≤ 1 / (8 * n) := min_le_right _ _
      have : 1 / (8 * (n : ℝ)) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      linarith
    have h3 : θ ≤ 1 := by
      rw [hθ, div_le_one (by positivity)]; nlinarith
    have : u * θ ≤ 1 / 8 := by
      have : u * θ ≤ u := by nlinarith
      have : u ≤ 1 / (8 * n) := min_le_right _ _
      have : 1 / (8 * (n : ℝ)) ≤ 1 / 8 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
      linarith
    linarith
  set δ₀ := ρ * gain / 2 with hδ₀def
  have hδ₀ : 0 < δ₀ := by positivity
  have hδ₀' : δ₀ ≤ ρ * gain := by rw [hδ₀def]; linarith [mul_pos hρ hg]
  refine ⟨m, s, gain, δ₀, u, hgrid, hg, hg8, hδ₀, hδ₀', ?_⟩
  intro N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨hNge, hNt, hL, hω0, hω1, hνp, hBpos, hEunit⟩ :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.prob_basic N K L d S η W ω ν E P B f g G hprob
  obtain ⟨Mb, hMb⟩ := prob_B_power hprob
  obtain ⟨Mprep, hP⟩ := hG gain hg (min_le_left _ _) m s δ₀ hgrid hδ₀ hδ₀' N K L d W ω ν E P B
    f g G hprob hprof Mp Dp
  refine ⟨max (budgetExp L ℓ Mp Mb) Mprep, fun ε hε => ?_⟩
  obtain ⟨σp, hσp, kp, hPk⟩ := hP ε hε
  set σ := min σp (min (ε / 4000000) (min (u * θ * L / 8) (1 / 4))) with hσdef
  have hσ : 0 < σ := lt_min hσp (lt_min (by positivity) (lt_min (by positivity) (by norm_num)))
  have hσp' : σ ≤ σp := min_le_left _ _
  have hσε : σ ≤ ε / 4000000 := (min_le_right _ _).trans (min_le_left _ _)
  have hσK : σ ≤ u * θ * L / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσq : σ ≤ 1 / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hE : ∀ᶠ k in atTop, (100 : ℝ) ≤ N k ^ (ε / 1000000) ∧ (n : ℝ) + 2 ≤ N k ^ (u * L) ∧
      (18 : ℝ) ≤ N k ^ (3 * ε / 4000000) ∧ (18 : ℝ) ≤ N k ^ (3 / 4 : ℝ) ∧
      (18 : ℝ) ≤ N k ^ (7 * (u * θ * L) / 8) ∧ (2 : ℝ) ≤ N k ^ (3 * (u * θ * L) / 8) :=
    (eventually_rpow_ge hNt (by positivity)).and ((eventually_rpow_ge hNt (by positivity)).and
      ((eventually_rpow_ge hNt (by positivity)).and ((eventually_rpow_ge hNt (by positivity)).and
        ((eventually_rpow_ge hNt (by positivity)).and (eventually_rpow_ge hNt (by positivity))))))
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp hE
  refine ⟨σ, hσ, max kp k₁, fun k hk p hp H hH hmass => ?_⟩
  obtain ⟨E1, E2, E3, E4, E5, E6⟩ := hk₁ k (le_trans (le_max_right _ _) hk)
  have hNk : (2 : ℝ) ≤ N k := hNge k
  have hN1 : (1 : ℝ) ≤ N k := by linarith
  have hN0 : (0 : ℝ) < N k := by linarith
  rcases hPk σ hσ hσp' k (le_trans (le_max_left _ _) hk) p hp H hH hmass with hc |
    ⟨D, τ, hD₀, hK, hdep, hroom, hτ, hτε, hτK, hτ2, hin⟩
  · exact Or.inl (mixedCandidate_mono hN1 (le_max_right _ _) hc)
  · right
    have hκ1 := hp.one_le_slack
    have hκσ := hp.slack_le
    have hκ_le : ∀ a, σ ≤ a → p.κ ≤ N k ^ a := fun a ha =>
      hκσ.trans (Real.rpow_le_rpow_of_exponent_le hN1 ha)
    have hKe : D.K = N k ^ (u * θ * L) := by
      rw [hK, ← Real.rpow_mul hN0.le]; congr 1; ring
    have hi₀ : D.i₀ < m := hp.label_level D.parent
    set J := max (18 * p.κ) τ⁻¹ with hJdef
    refine ⟨D, J, τ, SourceData.facts_of_inputs hp D hprof (hνp k _) (hBpos k _) (hMb k _).1 (hMb k _).2
      hdep hD₀ hK hn (le_max_left _ _) hd hκ hκ' hℓ hρ hρ' hε hu hun hg hgθ
      (by positivity) (fineGrid_mesh hgrid) hgrid.1.1 hgrid.1.2.2.2 hδ₀.le hL he1 he2 he3 hgap
      hroom (fineGrid_nonneg hgrid _ hi₀) hNk E1 E2 ?_ ?_ (le_max_left _ _) (le_max_right _ _)
      ?_ hτ ?_ ?_ ?_ ?_ hin⟩
    · -- J ≥ 1
      exact le_trans (by linarith) (le_max_left _ _)
    · -- J ≤ Nk^(ε/1e6)
      apply max_le
      · have h1 : 18 * p.κ ≤ 18 * N k ^ (ε / 4000000) := by
          have := hκ_le _ hσε; linarith
        refine h1.trans (mul_rpow_le_rpow hN0 ?_)
        convert E3 using 2; ring
      · exact hτε.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by
          have : 0 < ε := hε; linarith [this]))
    · -- J ≤ Nk
      apply max_le
      · have h1 : 18 * p.κ ≤ 18 * N k ^ (1 / 4 : ℝ) := by
          have := hκ_le _ hσq; linarith
        have h2 : 18 * N k ^ (1 / 4 : ℝ) ≤ N k ^ (1 : ℝ) :=
          mul_rpow_le_rpow hN0 (by convert E4 using 2; norm_num)
        rw [Real.rpow_one] at h2
        linarith
      · calc τ⁻¹ ≤ N k ^ (1 / 2 : ℝ) := hτ2
          _ ≤ N k ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
          _ = N k := Real.rpow_one _
    · -- τ⁻¹ ≤ K
      rw [hKe]
      refine hτK.trans (Real.rpow_le_rpow_of_exponent_le hN1 ?_)
      have : 0 ≤ u * θ * L := by positivity
      linarith
    · -- 18 κ ≤ K
      rw [hKe]
      have h1 : 18 * p.κ ≤ 18 * N k ^ (u * θ * L / 8) := by
        have := hκ_le _ hσK; linarith
      refine h1.trans (mul_rpow_le_rpow hN0 ?_)
      convert E5 using 2; ring
    · -- thickness slack
      rw [hKe]
      have h1 : 2 * p.κ ≤ 2 * N k ^ (u * θ * L / 8) := by
        have := hκ_le _ hσK; linarith
      have h2 : 2 * p.κ * N k ^ (u * θ * L / 2) ≤
          2 * N k ^ (u * θ * L / 8) * N k ^ (u * θ * L / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hN0.le _)
      refine h2.trans ?_
      rw [mul_assoc, ← Real.rpow_add hN0]
      refine mul_rpow_le_rpow hN0 ?_
      convert E6 using 2; ring
    · -- prior slack
      rw [hKe]
      have h1 : p.κ ^ 2 ≤ N k ^ (u * θ * L / 4) := by
        have h := hκ_le _ hσK
        calc p.κ ^ 2 ≤ (N k ^ (u * θ * L / 8)) ^ 2 := pow_le_pow_left₀ (by linarith) h 2
          _ = N k ^ (u * θ * L / 4) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
      calc p.κ ^ 2 * N k ^ (u * θ * L / 2) ≤ N k ^ (u * θ * L / 4) * N k ^ (u * θ * L / 2) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hN0.le _)
        _ = N k ^ (3 * (u * θ * L) / 4) := by rw [← Real.rpow_add hN0]; congr 1; ring
        _ ≤ N k ^ (u * θ * L) := Real.rpow_le_rpow_of_exponent_le hN1 (by
            have : 0 ≤ u * θ * L := by positivity
            linarith)

end

end Submission.Obl.k4_finite_affine_parent_sources

namespace Submission.Obl.k4_finite_affine_parent_sources

/-- **The source preparation from its remaining interface.** -/
theorem sourcePreparation_of_spec (h : SourceInputsSpec) : SourcePreparation :=
  sourcePreparation_of_samples (sourceSamples_of_spec h)

end Submission.Obl.k4_finite_affine_parent_sources
