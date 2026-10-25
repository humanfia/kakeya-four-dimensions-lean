import Submission.Obl.k4_horizontal_strict_parameter_step.ComparedEngine
import Submission.Obl.k4_horizontal_strict_parameter_step.PreparedRestriction
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Eventually

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set Filter

noncomputable section

/-- A fixed structural buffer works for the comparison step at every admissible
rate and gain. Enlarging the original subpower slack supplies the reference
velocity bounds used by the native support count. -/
theorem comparedStep : ComparedStep := by
  intro _ _ hMatching d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he₀
  refine ⟨min (U / 4) (e₀ / 100), lt_min (by positivity) (by positivity), ?_⟩
  intro sMax hsMax hsMax₁ u θ hu hu1 hθ hθmax hold
  intro N K hN hNt hsub α inst ν μ ρ π b P T n j A B c F h1 h2 h3 h4
  let H : ℕ → ℝ := fun k => 3 * K k
  have hK : ∀ k, 0 < K k := fun k => zero_lt_one.trans_le (hsub.1 k)
  have hKH : ∀ k, K k ≤ H k := fun k => by dsimp [H]; linarith [hK k]
  have hH3 : ∀ k, 3 ≤ H k := fun k => by dsimp [H]; linarith [hsub.1 k]
  have hHsub : (∀ k, 1 ≤ H k) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε := by
    simpa only [pow_one] using
      Submission.Obl.k4_scalar_capped_heavy_potential.Cons.subpower_const_mul_pow
        hN hNt hsub 3 (by norm_num) 1
  have h1' : Hyp1 H ν μ ρ π b P := h1.restrictCurrent hK hKH
    (fun _ => le_rfl) (fun k => by
      have hinv : (H k)⁻¹ ≤ (K k)⁻¹ := inv_anti₀ (hK k) (hKH k)
      obtain ⟨_, _, _, _, _, _, hmass, _⟩ := h1 k
      exact (ENNReal.ofReal_le_ofReal hinv).trans hmass)
  have h2' : Hyp2 N H d S μ π b P := h2.monoK
    (fun k => by linarith [hN k]) hKH
  have h3' : Hyp3 N H d κ ℓ U e₀ ν μ π b P T n j A B c F :=
    h3.monoK (fun k => by linarith [hN k]) hK hKH
  let cfg : NativeModel α := {
    N := N, K := H, d := d, κ := κ, ℓ := ℓ, S := S, U := U, e₀ := e₀
    ν := ν, μ := μ, ρ := ρ, π := π, b := b, P := P
    T := T, n := n, j := j, A := A, B := B, c := c, F := F }
  have hbufferU : 4 * sMax ≤ U := by
    have := hsMax₁.trans (min_le_left _ _)
    linarith
  have hbufferE : 100 * sMax ≤ e₀ := by
    have := hsMax₁.trans (min_le_right _ _)
    linarith
  exact cfg.compared_layers_at hMatching hN hNt hH3 hHsub.2 hd hd1 hκ hκ1 hℓ
    h1' h2' h3' h4 hsMax hbufferU hbufferE hu hu1 hθ hθmax
    (hold N H hN hNt hHsub α ν μ ρ π b P T n j A B c F h1' h2' h3' h4)

end

end Submission.Obl.k4_horizontal_strict_parameter_step
