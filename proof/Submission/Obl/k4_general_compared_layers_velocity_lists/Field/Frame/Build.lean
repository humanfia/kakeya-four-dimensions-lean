-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Frame.Build; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Frame.Construct

/-!
# Residual velocity lists from a field-ready sample

`Parent.Valid.listFrame_of_fieldReady`: for compared exponents and every loss `ε > 0`
there are a sample-loss exponent `δ > 0` and a field loss `ε₁ > 0` such that, eventually,
every compared sample with loss `2 ≤ H ≤ N^δ` (and `K ≤ H`) and every common field of it
at precision `E = N^(-(r + (1 - d) u / 2))` with loss `ε₁` give a `ListFrame` at loss `ε`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent.FieldFrame

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- A fixed constant times a fixed power of the subpolynomial `K` is absorbed by any
strictly larger power of `N`, eventually. -/
theorem eventually_const_K_pow (h : p.Valid) (C : ℝ) (a : ℕ) {b c : ℝ} (hbc : b < c) :
    ∀ᶠ k in atTop, C * p.K k ^ a * p.N k ^ b ≤ p.N k ^ c := by
  have hγ0 : 0 < (c - b) / 2 := by linarith
  have hθ0 : 0 < (c - b) / 2 / ((a : ℝ) + 1) := div_pos hγ0 (by positivity)
  have hNγ : Tendsto (fun k => p.N k ^ ((c - b) / 2)) atTop atTop :=
    (tendsto_rpow_atTop hγ0).comp h.scale_limit
  filter_upwards [h.subpower.2 _ hθ0, hNγ.eventually_ge_atTop C] with k hK hC
  have hN : 1 ≤ p.N k := by linarith [h.scale k]
  have hN0 : 0 < p.N k := by linarith
  have hK1 := h.subpower.1 k
  have hKa : p.K k ^ a ≤ p.N k ^ ((a : ℝ) * ((c - b) / 2 / ((a : ℝ) + 1))) := by
    calc p.K k ^ a ≤ (p.N k ^ ((c - b) / 2 / ((a : ℝ) + 1))) ^ a :=
          pow_le_pow_left₀ (by linarith) hK a
      _ = p.N k ^ ((a : ℝ) * ((c - b) / 2 / ((a : ℝ) + 1))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, mul_comm]
  have haθ : (a : ℝ) * ((c - b) / 2 / ((a : ℝ) + 1)) ≤ (c - b) / 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ (c - b) / 2 := hγ0.le
    nlinarith
  calc C * p.K k ^ a * p.N k ^ b
      ≤ p.N k ^ ((c - b) / 2) * p.N k ^ ((a : ℝ) * ((c - b) / 2 / ((a : ℝ) + 1))) *
          p.N k ^ b := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
        exact mul_le_mul hC hKa (pow_nonneg (by linarith) a) (Real.rpow_nonneg hN0.le _)
    _ = p.N k ^ ((c - b) / 2 + (a : ℝ) * ((c - b) / 2 / ((a : ℝ) + 1)) + b) := by
        rw [Real.rpow_add hN0, Real.rpow_add hN0]
    _ ≤ p.N k ^ c := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end Parent.FieldFrame

open Parent.FieldFrame in
/-- Residual velocity lists from a field-ready compared sample. -/
theorem Parent.Valid.listFrame_of_fieldReady {α : Type} [MeasurableSpace α] {p : Parent α}
    (h : p.Valid) {r u v m : ℝ} (hexp : p.ComparedExponents r u v m) :
    ∀ ε : ℝ, 0 < ε → ∃ δ ε₁ : ℝ, 0 < δ ∧ 0 < ε₁ ∧ ∀ᶠ k in Filter.atTop,
      ∀ H : ℝ, 2 ≤ H → p.K k ≤ H → H ≤ p.N k ^ δ →
      ∀ (s : p.ComparedSample k r u v m H)
        (F : p.FieldReady k s (p.N k ^ (-(r + (1 - p.d) * u / 2))) ε₁),
        Nonempty (p.ListFrame k r v m ε) := by
  obtain ⟨⟨hr, hv, hvr, hm100, hℓm, hrU⟩, hu, hur, hvu, hm10000, hκ⟩ := hexp
  intro ε hε
  have hd1 : 0 < 1 - p.d := by linarith [h.dimension_lt_one]
  have hm : 0 < m := by linarith
  have hκ0 : 0 < p.κ := h.rate_pos
  have hκ1 : p.κ ≤ 1 := h.rate_le_one
  have hℓ0 : 0 < p.ℓ := h.transverse_pos
  set ε₁ := min (ε / 2) (min ((1 - p.d) * u / 8) (m / 100)) with hε₁_def
  have hε₁0 : 0 < ε₁ := by
    rw [hε₁_def]
    refine lt_min (by linarith) (lt_min (by positivity) (by linarith))
  have hε₁ε : ε₁ ≤ ε / 2 := min_le_left _ _
  have hε₁u : ε₁ ≤ (1 - p.d) * u / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₁m : ε₁ ≤ m / 100 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε / 22, ε₁, by positivity, hε₁0, ?_⟩
  -- the depth `r` is prepared
  have hR : 1 < 2 + r⁻¹ := by linarith [inv_pos.mpr hr]
  have hRr : (2 + r⁻¹)⁻¹ ≤ r := by
    apply (inv_le_comm₀ (by linarith [inv_pos.mpr hr]) hr).mpr
    linarith
  have hrU' : r ≤ p.U := by
    have : 0 < 3 * m / p.κ := by positivity
    linarith
  -- the numerical conditions
  have e1 := h.subpower.2 ε hε
  have e2 := eventually_const_K_pow h 40 2 (show ε₁ < ε by linarith)
  have e3 := eventually_const_K_pow h 40 4
    (show ε₁ + 2 * (p.κ + p.ℓ) * r < m / 10 by nlinarith)
  have e4 := eventually_const_K_pow h 6 2 (show p.κ * r < m / 10 by nlinarith)
  have e5 := eventually_const_K_pow h 2 2
    (show ε₁ + -(r + (1 - p.d) * u / 2) < -r - v by nlinarith)
  have e6 := eventually_const_K_pow h 5832 6 (show m / 1000 + -m < -r - v by linarith)
  have e7 := eventually_const_K_pow h 3 2 (show -m < 0 by linarith)
  have e8 := eventually_const_K_pow h 2000 0 (show ε / 2 < ε by linarith)
  filter_upwards [h.prepared _ hR, e1, e2, e3, e4, e5, e6, e7, e8] with k hprep h1 h2 h3 h4 h5
    h6 h7 h8
  intro H hH2 hKH hHN s F
  have hat := hprep r hRr hrU'
  have hN0 : 0 < p.N k := by linarith [h.scale k]
  have hK1 : 1 ≤ p.K k := h.subpower.1 k
  have h2T : (2 : ℝ) ^ p.T k r ≤ p.K k * p.N k ^ (p.κ * r) := hat.2.1
  have hNpos (x : ℝ) : 0 < p.N k ^ x := Real.rpow_pos_of_pos hN0 x
  -- the background budget
  have hbg : 40 * p.K k ^ 2 * p.N k ^ ε₁ *
      ((2 : ℝ) ^ p.T k r * (p.N k ^ (-p.ℓ * r))⁻¹) ^ 2 ≤ p.N k ^ (m / 10) := by
    have hginv : (p.N k ^ (-p.ℓ * r))⁻¹ = p.N k ^ (p.ℓ * r) := by
      rw [neg_mul, Real.rpow_neg hN0.le, inv_inv]
    rw [hginv]
    have hle : ((2 : ℝ) ^ p.T k r * p.N k ^ (p.ℓ * r)) ^ 2 ≤
        (p.K k * p.N k ^ (p.κ * r) * p.N k ^ (p.ℓ * r)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h2T (hNpos _).le) 2
    have heq : 40 * p.K k ^ 2 * p.N k ^ ε₁ *
        (p.K k * p.N k ^ (p.κ * r) * p.N k ^ (p.ℓ * r)) ^ 2 =
        40 * p.K k ^ 4 * p.N k ^ (ε₁ + 2 * (p.κ + p.ℓ) * r) := by
      have : p.N k ^ (ε₁ + 2 * (p.κ + p.ℓ) * r) =
          p.N k ^ ε₁ * (p.N k ^ (p.κ * r) * p.N k ^ (p.ℓ * r)) ^ 2 := by
        rw [← Real.rpow_add hN0, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
          ← Real.rpow_add hN0]
        congr 1
        push_cast
        ring
      rw [this]
      ring
    calc _ ≤ 40 * p.K k ^ 2 * p.N k ^ ε₁ *
          (p.K k * p.N k ^ (p.κ * r) * p.N k ^ (p.ℓ * r)) ^ 2 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 40 * p.K k ^ 4 * p.N k ^ (ε₁ + 2 * (p.κ + p.ℓ) * r) := heq
      _ ≤ p.N k ^ (m / 10) := h3
  -- the frame budget
  have hframe : 6 * p.K k * (2 : ℝ) ^ p.T k r ≤ p.N k ^ (m / 10) := by
    calc 6 * p.K k * (2 : ℝ) ^ p.T k r ≤ 6 * p.K k * (p.K k * p.N k ^ (p.κ * r)) :=
          mul_le_mul_of_nonneg_left h2T (by positivity)
      _ = 6 * p.K k ^ 2 * p.N k ^ (p.κ * r) := by ring
      _ ≤ p.N k ^ (m / 10) := h4
  -- the field residual
  have hfield : 2 * p.K k ^ 2 * (p.N k ^ ε₁ * p.N k ^ (-(r + (1 - p.d) * u / 2))) ≤
      p.N k ^ (-r - v) := by
    rw [← Real.rpow_add hN0]
    calc _ = 2 * p.K k ^ 2 * p.N k ^ (ε₁ + -(r + (1 - p.d) * u / 2)) := by ring
      _ ≤ _ := h5
  -- the cell variation
  have hvar : 5832 * p.N k ^ (m / 1000) * p.K k ^ 6 * p.N k ^ (-m) ≤ p.N k ^ (-r - v) := by
    calc _ = 5832 * p.K k ^ 6 * p.N k ^ (m / 1000 + -m) := by
          rw [Real.rpow_add hN0]
          ring
      _ ≤ _ := h6
  have hσK : 3 * p.K k ^ 2 * p.N k ^ (-m) ≤ 1 := by
    have := h7
    rwa [Real.rpow_zero] at this
  -- the list count
  have hcard : 2000 * H ^ 11 ≤ p.N k ^ ε := by
    have hH11 : H ^ 11 ≤ p.N k ^ (ε / 2) := by
      calc H ^ 11 ≤ (p.N k ^ (ε / 22)) ^ 11 := pow_le_pow_left₀ (by linarith) hHN 11
        _ = p.N k ^ (ε / 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
            congr 1
            push_cast
            ring
    calc 2000 * H ^ 11 ≤ 2000 * p.N k ^ (ε / 2) := by linarith
      _ = 2000 * p.K k ^ 0 * p.N k ^ (ε / 2) := by ring
      _ ≤ p.N k ^ ε := h8
  exact listFrame_of_atDepth p h hat hr.le s F hKH (by linarith) hε₁0.le h1 h2 hbg hframe
    hfield hvar hσK hcard

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
