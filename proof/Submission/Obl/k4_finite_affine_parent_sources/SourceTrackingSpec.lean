-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceTracking

/-!
The tracking component with the positive parent band and the original-axis
mask supplied by source selection. The quantifier interface is adapted from
this team, x0891, SourceComponents.lean (23408e68); the added geometric
premises were agreed by x0812 and x0807 on 2026-10-21.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Filter

noncomputable section

def SourceTrackingFullAxesSpec : Prop :=
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
        ∀ (a : Fin p.C) (τ : ℝ) (D : SourceData p), D.parent = a →
          (1 / 8 : ℝ) ≤ s (p.lev a) → s (p.lev a) ≤ 1 / 4 →
          s (p.lev a) + u + δ₀ ≤ 1 / 2 → 0 < τ →
          τ⁻¹ ≤ N k ^ (ε / 4000000) →
          τ⁻¹ ≤ N k ^ (u * (ρ / (1000000 * ((n : ℝ) + 1))) * L / 4) →
          τ⁻¹ ≤ N k ^ (1 / 2 : ℝ) →
          D.S ⊆ H (p.world a) → MeasurableSet D.S → D.S.Nonempty →
          D.D₀ = MajorFrame.frame (p.frame a) →
          D.K = (N k ^ (u * L)) ^ (ρ / (1000000 * ((n : ℝ) + 1))) →
          D.depth = sourceDepth m s (p.lev a) u →
          D.FullAxes n (N k ^ (-(u * L * trackingSlackExponent n ℓ ρ / 2))) →
          D.S ⊆ p.assigned a ×ˢ Ioo ((p.bin a : ℝ) / (2 : ℝ) ^ p.T (p.lev a))
            (((p.bin a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a)) →
          (∀ z ∈ D.S, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
            z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) →
          ENNReal.ofReal τ * ((ν k D.w₀).prod volume) (p.packet D.parent) ≤
            ((ν k D.w₀).prod volume) (D.S ∩ p.counted D.parent) →
          (∀ x : ℝ, (n : ℝ)⁻¹ ≤ x → x ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth x)),
            ENNReal.ofReal τ * ((ν k D.w₀).prod volume) (p.packet (D.old x i)) ≤
              ((ν k D.w₀).prod volume) (D.S ∩ p.counted (D.old x i))) →
          ∃ c, D.Tracks n ℓ u (N k) L (ν k) (B k) c

/-- Uniform tracking on the unchanged original priors, after the selected
parent band and original-axis deletion have been supplied. -/
theorem sourceTrackingFullAxesSpec : SourceTrackingFullAxesSpec := by
  intro d₁ κ₁ ℓ S η ρ hd₁ hd₁' hκ₁ hκ₁' hℓ hS hS' hη hρ hρ' n hn
  let β := trackingSlackExponent n ℓ ρ
  have hβ : 0 < β := trackingSlackExponent_pos n hℓ hρ
  have hβmodel : 5 * β ≤ ρ / (1000000 * ((n : ℝ) + 1)) :=
    trackingSlackExponent_model n hρ.le
  have hβℓ : 1000 * β ≤ ℓ := trackingSlackExponent_narrowness n ℓ ρ
  refine ⟨min (1 / 8) β⁻¹, lt_min (by norm_num) (inv_pos.mpr hβ), ?_⟩
  intro unit hu hu'
  have hu8 : unit ≤ 1 / 8 := hu'.trans (min_le_left _ _)
  have huβ : unit * β ≤ 1 := by
    have hh := hu'.trans (min_le_right _ _)
    exact (le_div_iff₀ hβ).mp (by simpa only [one_div] using hh)
  refine ⟨min (unit * β / 16) (unit * β / (4 + ℓ)),
    lt_min (by positivity) (by positivity), ?_⟩
  intro gain hg hg' m sg δ₀ hgrid hδ hδgain N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨hNge, hNt, hL, -, -, -, -, -⟩ :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.prob_basic N K L d S η W ω ν E P B f g G hprob
  let X := unit * L * β
  have hX : 0 < X := by dsimp [X]; positivity
  have hE : ∀ᶠ k in atTop, (36 : ℝ) ≤ N k ^ (X / 8) :=
    eventually_rpow_ge hNt (by positivity)
  obtain ⟨kp, hkp⟩ := eventually_atTop.mp hE
  refine ⟨2, fun ε hε => ⟨min 1 (X / 8), lt_min zero_lt_one (by positivity), kp, ?_⟩⟩
  intro σ hσ hσ' k hk p hp Hres hHm hmass
  have hNk : (2 : ℝ) ≤ N k := hNge k
  have hN1 : (1 : ℝ) ≤ N k := by linarith
  have hσ1 : σ ≤ 1 := hσ'.trans (min_le_left _ _)
  have hσX : σ ≤ X / 8 := hσ'.trans (min_le_right _ _)
  have hκ0 : 0 ≤ p.κ := zero_le_one.trans hp.one_le_slack
  have hκN : p.κ ≤ N k := by
    have hh := hp.slack_le.trans (Real.rpow_le_rpow_of_exponent_le hN1 hσ1)
    simpa only [Real.rpow_one] using hh
  have hbias : 2 * p.κ ≤ N k ^ (2 : ℕ) := by
    calc
      _ ≤ N k * N k := mul_le_mul hNk hκN hκ0 (by linarith)
      _ = _ := (pow_two _).symm
  by_cases hc : MixedCandidate (N k) L (W k) (ν k) (B k) 2 d₁ ρ gain ε
      p.r p.T p.C p.lev p.world p.bin p.velocity p.frame p.assigned Hres
  · exact Or.inl hc
  right
  intro a τ D hDa hbandlo hbandhi hroom hτ hτε hτu hτhalf hDS hDm hDne hD₀ hDK hDd haxes
    hDopen hDend hpf hlf
  have hframe : D.D₀ = MajorFrame.frame (p.frame D.parent) := by
    simpa only [hDa] using hD₀
  have hdepth : D.depth = sourceDepth m sg D.i₀ unit := by
    simpa only [SourceData.i₀, hDa] using hDd
  have hparent : unit ≤ sg D.i₀ := by
    change unit ≤ sg (p.lev D.parent)
    rw [hDa]
    exact hu8.trans hbandlo
  have hroom' : sg D.i₀ + unit + δ₀ ≤ 1 / 2 := by
    simpa only [SourceData.i₀, hDa] using hroom
  have hres : D.S ⊆ Hres D.w₀ := by
    simpa only [SourceData.w₀, hDa] using hDS
  have hopen : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀) := by
    intro z hz
    have hh := hDopen hz
    refine ⟨?_, ?_⟩
    · simpa only [hDa] using hh.1
    · rw [D.t₀_add_q₀]
      simpa only [SourceData.t₀, SourceData.i₀, hDa] using hh.2
  exact D.tracks_of_full_axes hp hNk hℓ hL n 2 d₁ ρ gain ε unit β τ hρ hρ' hε hu huβ hβ
    hβmodel hβℓ hg (hg'.trans (min_le_left _ _)) (hg'.trans (min_le_right _ _))
    hgrid hδ hδgain hσX (hkp k hk) Hres hc hbias hframe hDK hdepth hparent hroom' haxes
    hres hopen hτ hτε hlf

end

end Submission.Obl.k4_finite_affine_parent_sources
