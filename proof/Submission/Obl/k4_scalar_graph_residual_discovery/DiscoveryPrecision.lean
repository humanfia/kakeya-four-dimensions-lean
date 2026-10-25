import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryBudget
import Submission.Obl.k4_scalar_graph_residual_discovery.PrecisionAsymptotics

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

/-- The precision fields of the discovery budget, separated from its
mass, support-counting and finite-selection allowances. -/
structure DiscoveryPrecision (N H Hg h a C L B cζ : ℝ) (M J₁ : ℕ) : Prop where
  point_precision : (1 + 3 * (H + 1)) * N ^ (-B) ≤ N ^ (-a) * N ^ (-C)
  variation :
    (Hg * N ^ (-L) + discoveryRowConstant N Hg J₁ *
      (N ^ (-a) + 2 * N ^ (-B) + N ^ (-a)) * (1 + H)) *
      (N ^ (-a) + 2 * N ^ (-B)) + 2 * (1 + 2 * Hg) * N ^ (-B) ≤
        N ^ (-a) * N ^ (-C)
  residual_precision :
    4 * discoveryTimeConstant N H Hg J₁ ^ 2 * N ^ (-a) + Hg * N ^ (-L) / N ^ (-a) +
      2 * (H + 1) * N ^ (-B) / N ^ (-a) ≤ N ^ (-C)
  support_precision :
    2 * (discoveryRowConstant N Hg J₁ * (N ^ (-a) + 2 * N ^ (-B) + N ^ (-a)) +
      4 * discoveryTimeConstant N H Hg J₁ ^ 2 * N ^ (-a)) +
      (1 + 2 * Hg) * N ^ (-B) / N ^ (-a) ≤ N ^ (-C)
  graph_margin : Hg * N ^ (-L) ≤ h ^ M * h ^ ((1 : ℝ) / 8)
  row_margin : 4 * discoveryTimeConstant N H Hg J₁ ^ 2 * N ^ (-a) ≤
    h ^ M * h ^ ((1 : ℝ) / 8)
  floor_margin : N ^ (-C) ≤ h ^ cζ

/-- Fixed integer coarse exponents give all geometric precision bounds
at once. Their surplus is fixed before the first-grid loss parameter. -/
theorem eventually_discovery_precision {N H Hg K h : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : Subpower N H) (hHg : Subpower N Hg) (hK : Subpower N K)
    (hh : ∀ k, 0 < h k) {κ a C L B cζ : ℝ} {M J₁ : ℕ}
    (hM : 2 ≤ M) (hcζ : 0 < cζ) (hC : κ * cζ < C) (hC0 : 0 ≤ C)
    (haC : C + 2 ≤ a) (haM : κ * ((M : ℝ) + 1 / 8) + 2 ≤ a)
    (hLa : a + C + 2 ≤ L) (hBL : L + 10 ≤ B)
    (hJ : 2 / (J₁ : ℝ) < 1)
    (hscale : ∀ᶠ k in atTop, N k ^ (-κ) / K k ≤ h k) :
    ∀ᶠ k in atTop, DiscoveryPrecision (N k) (H k) (Hg k) (h k) a C L B cζ M J₁ := by
  let U : ℕ → ℝ := fun k => max (H k) (Hg k)
  let R : ℕ → ℝ := fun k => discoveryRowConstant (N k) (Hg k) J₁
  let Q : ℕ → ℝ := fun k => discoveryTimeConstant (N k) (H k) (Hg k) J₁
  have hU : Subpower N U := subpower_max hH hHg
  have hH0 (k : ℕ) : 0 ≤ H k := zero_le_one.trans (hH.1 k)
  have hHg0 (k : ℕ) : 0 ≤ Hg k := zero_le_one.trans (hHg.1 k)
  have hR0 (k : ℕ) : 0 ≤ R k := by
    have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
    dsimp only [R, discoveryRowConstant]
    positivity
  have hQ0 (k : ℕ) : 0 ≤ Q k := by
    dsimp only [Q, discoveryTimeConstant, Zoom.worldRowConstant]
    linarith [hR0 k, hH0 k]
  have hbound (k : ℕ) : precisionEnvelope (H k) (Hg k) (R k) (Q k) ≤
      2000000 * U k ^ 4 * N k ^ (2 / (J₁ : ℝ)) := by
    let X := N k ^ (1 / (J₁ : ℝ))
    have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
    have hX : 1 ≤ X := Real.one_le_rpow (hN k) (by positivity)
    have hR : R k ≤ 102 * U k ^ 2 * X :=
      discovery_first_row_constant_le (hU.1 k) (hHg0 k) (le_max_right _ _) hX
    have hHc : H k + 1 ≤ 2 * U k := by
      have hHU : H k ≤ U k := le_max_left _ _
      linarith [hU.1 k]
    have hQ : Q k ≤ 128 * U k ^ 2 * X :=
      discovery_world_row_constant_le (hU.1 k) hHc hX hR
    have hpower : X ^ 2 = N k ^ (2 / (J₁ : ℝ)) := by
      dsimp only [X]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      congr 1
      ring
    simpa only [hpower] using precisionEnvelope_le (hU.1 k)
      (hH0 k) (le_max_left _ _) (hHg0 k) (le_max_right _ _) (hR0 k) hR (hQ0 k) hQ hX
  have haL : a ≤ L := by linarith
  have haB : a ≤ B := by linarith
  have hprec := eventually_precision_of_envelope hN hNt hU hH0 hHg0 hR0
    (A := 2000000) (e := 2 / (J₁ : ℝ)) (a := a) (C := C) (L := L) (B := B)
    (by norm_num) 4 (by linarith) (by linarith) (by linarith) haL haB
    (Eventually.of_forall hbound)
  have hβ : 0 < (M : ℝ) + 1 / 8 := by positivity
  have hmarg := eventually_row_graph_margins_of_envelope hN hNt hU hK hH0 hHg0 hR0
    (A := 2000000) (e := 2 / (J₁ : ℝ)) (a := a) (L := L)
    (by norm_num) 4 hβ (by linarith) (by linarith) hscale
    (Eventually.of_forall hbound)
  filter_upwards [hprec, hmarg, eventually_floor_le_block_rpow hN hK hcζ hC hscale]
    with k hp hm hf
  have hpower : h k ^ ((M : ℝ) + 1 / 8) = h k ^ M * h k ^ ((1 : ℝ) / 8) := by
    rw [Real.rpow_add (hh k), Real.rpow_natCast]
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2,
    by simpa only [hpower] using hm.1, by simpa only [hpower] using hm.2, hf⟩

end Submission.Obl.k4_scalar_graph_residual_discovery
