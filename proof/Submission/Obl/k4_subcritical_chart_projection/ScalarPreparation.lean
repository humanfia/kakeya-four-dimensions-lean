import Submission.Obl.k4_subcritical_chart_projection.Ensemble

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory Filter
open scoped ENNReal BigOperators
open Submission.Obl.k4_horizontal_supercritical_three_projections

/-- Corrected charts supply the entire scalar ensemble at a prescribed
relative depth, uniformly for every sufficiently small positive chart loss. -/
theorem corrected_scalar_preparation (hscalar : Scalar)
    {α : Type} [MeasurableSpace α] (m : Model α)
    (hN : ∀ k, 2 ≤ m.N k) (hNt : Tendsto m.N atTop atTop)
    (hK : ∀ k, 1 ≤ m.K k)
    (hKsub : ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, m.K k ≤ m.N k ^ ξ)
    (hd : 0 ≤ m.d) (hd₁ : m.d < 1) (hκ : 0 < m.κ) (hκ₁ : m.κ ≤ 1)
    (hbasic : m.Basic) (hcaps : m.Caps)
    {s₀ M : ℝ} (hs₀ : 0 < s₀) (hM : 100 * s₀ < M)
    (depth : Fin 3 → ℝ) (h : Fin 3) (hdepth : s₀ < depth h)
    (hnear : depth h < 3 * s₀ / 2) :
    ∀ τ : ℝ, 0 < τ → ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ᶠ k in atTop,
        ∀ C : Charts (m.b k) (m.ρ k) (m.π k)
          (m.N k ^ (-M)) (m.N k ^ (-(2 * m.κ * s₀))) (m.N k ^ (-s₀))
          (m.N k ^ (-(20 * s₀))) m.d (m.N k ^ ξ) (m.N k ^ (-ξ))
          (fun h => m.N k ^ (-(depth h - s₀))),
        ∀ ζ : Measure (α × ℝ), ζ ≤ C.law →
          ENNReal.ofReal (m.N k ^ (-η₀)) ≤ ζ univ →
          ∃ L : CorrectedLayer α,
            L.Certified (m.b k) (m.N k ^ (-M)) (m.N k ^ (-(2 * m.κ * s₀)))
              (m.N k ^ (-s₀)) (m.N k ^ ξ) (240 * (m.N k ^ τ) ^ 5)
              (m.N k ^ τ * m.N k ^ (-(depth h - s₀))) ∧
            (∀ i, 0 < m.π k (Ico ((L.q i 0 : ℝ) * m.N k ^ (-M))
              (((L.q i 0 : ℝ) + 1) * m.N k ^ (-M)))) ∧
            (∀ i, ENNReal.ofReal
              (chartReference (m.π k) (m.N k ^ (-M)) (m.N k ^ (-(2 * m.κ * s₀)))
                (m.N k ^ (-depth h)) m.d (L.q i) / m.N k ^ (2 * τ)) ≤
              ζ (L.A i ×ˢ Icc (0 : ℝ) 1)) ∧
            ENNReal.ofReal (m.N k ^ (-2 * τ)) ≤ ζ {p | ∃ i, p.1 ∈ L.A i} := by
  intro τ hτ
  obtain ⟨η, hη, N₀, hN₀, Hscalar⟩ := scalar_packets_of_mesh hscalar hd hd₁
    (show 0 < depth h - s₀ by linarith) (show depth h - s₀ < 20 * s₀ by linarith)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
    hs₀ (by linarith : s₀ < 20 * s₀) hτ
  obtain ⟨cut, η₀, ξ₀, hcut, hη₀, hξ₀, hnum⟩ := exists_input_exponents m.N m.K
    hN hNt hK hKsub hκ hκ₁ hs₀ hnear hM hη hτ
  have hM₀ : 0 < M := by linarith
  let R := 2 + M + M⁻¹ + 3 * s₀ / 2
  have hMinv : 0 < M⁻¹ := inv_pos.mpr hM₀
  have hR : 1 < R := by dsimp [R]; linarith
  have hMhi : M ≤ R := by dsimp [R]; linarith
  have hBhi : 3 * s₀ / 2 ≤ R := by dsimp [R]; linarith
  have hMlo : R⁻¹ ≤ M := by
    have hh : M⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [inv_inv] using inv_anti₀ hMinv hh
  have hnative := original_joint_caps_eventually m hN hcaps hR hMlo hMhi hBhi
  refine ⟨η₀, hη₀, ξ₀, hξ₀, ?_⟩
  intro ξ hξ hξmax
  filter_upwards [hnum ξ hξ hξmax, hnative, (tendsto_atTop.1 hNt N₀)] with k hnum hnative hNk
  intro C ζ hζ hmass
  obtain ⟨hb, hν, hπ, hμdom, hρμ, hsupp, -⟩ := hbasic k
  have : IsProbabilityMeasure (m.ν k) := hν
  have : IsProbabilityMeasure (m.π k) := hπ
  have hN₁ : 1 ≤ m.N k := by linarith [hN k]
  have hρsupp : m.ρ k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
    le_antisymm ((hρμ _).trans_eq hsupp) bot_le
  have hρmass : m.ρ k univ ≤ ENNReal.ofReal (m.K k) := by
    simpa only [Set.mem_univ, Set.ofPred_true, measure_univ, mul_one] using
      incidence_assignment_bound (m.ν k) (m.ρ k) univ (ENNReal.ofReal (m.K k))
        (hρμ.trans hμdom) hρsupp
  obtain ⟨S, F, hνG, hpalette, hsub, hmass'⟩ := corrected_chart_packets hN₁ (hK k)
    hκ hs₀ hξ hd₁ depth h hdepth hnear.le (m.ν k) (m.μ k) (m.ρ k) ζ
    (m.π k) (m.b k) hb hρμ hμdom hsupp hρmass hnative hnum
    (Hscalar (m.N k) hNk α) C hζ hmass
  exact layer_of_corrected_chart_packets hN₁ hτ.le depth h (m.ν k) (m.ρ k) ζ
    (m.π k) (m.b k) C S F hνG hpalette hsub hmass'

end Submission.Obl.k4_subcritical_chart_projection
