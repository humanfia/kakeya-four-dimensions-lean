-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.Numerics; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900, on
   `eventually_subpower_mul_rpow_lt` of this checkout (`k4_profile_density_bounds`). -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Assemble
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-!
# Numerics of coefficient consensus

* `agree_eventually_KH_le`: for a valid parent, `A K^a H^b N^c ≤ 1` eventually, uniformly for
  `0 ≤ H ≤ N^δ`, as soon as `c + b δ < 0`;
* `agree_epsnum_core`: the disagreement bound of `consensus_at_index` is at most `1 / (16 H)` once three
  monomial bounds hold.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- **Uniform eventual monomial bounds** under `H ≤ N^δ`. -/
theorem agree_eventually_KH_le {α : Type} [MeasurableSpace α] {p : Parent α} (h : p.Valid)
    (A : ℝ) (hA : 0 ≤ A) (pK pH : ℕ) {a δ : ℝ} (hδ : 0 ≤ δ) (ha : a + pH * δ < 0) :
    ∀ᶠ k in atTop, ∀ H : ℝ, 0 ≤ H → H ≤ p.N k ^ δ →
      A * p.K k ^ pK * H ^ pH * p.N k ^ a ≤ 1 := by
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [h.scale k]
  have hev := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt hN1
    h.scale_limit h.subpower.1 h.subpower.2 pK ha hA
  filter_upwards [hev] with k hk
  intro H hH0 hHN
  have hNpos : 0 < p.N k := by linarith [hN1 k]
  have hK0 : 0 ≤ p.K k := by linarith [h.subpower.1 k]
  have hpow : H ^ pH ≤ p.N k ^ ((pH : ℝ) * δ) := by
    calc H ^ pH ≤ (p.N k ^ δ) ^ pH := pow_le_pow_left₀ hH0 hHN pH
      _ = p.N k ^ ((pH : ℝ) * δ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
          ring_nf
  rw [Real.rpow_zero] at hk
  have hsplit : p.N k ^ (a + pH * δ) = p.N k ^ ((pH : ℝ) * δ) * p.N k ^ a := by
    rw [← Real.rpow_add hNpos]
    ring_nf
  rw [hsplit] at hk
  have hA' : 0 ≤ A * p.K k ^ pK := by positivity
  have hNa : 0 ≤ p.N k ^ a := (Real.rpow_pos_of_pos hNpos a).le
  calc A * p.K k ^ pK * H ^ pH * p.N k ^ a ≤
        A * p.K k ^ pK * p.N k ^ ((pH : ℝ) * δ) * p.N k ^ a := by gcongr
    _ = A * p.K k ^ pK * (p.N k ^ ((pH : ℝ) * δ) * p.N k ^ a) := by ring
    _ ≤ 1 := hk.le

/-- **The disagreement numeric.** -/
theorem agree_epsnum_core {K H X Y Z E a₁ Nd χ wQ W θ' ϑ : ℝ} (hK1 : 1 ≤ K) (hH1 : 1 ≤ H)
    (hX : 0 < X) (hY0 : 0 ≤ Y) (hZ0 : 0 ≤ Z) (hE : 0 < E) (hθ' : θ' = E / 8 * X)
    (hNd : 1 ≤ Nd) (hid : Nd * a₁ = E * X * Y) (hχ0 : 0 ≤ χ) (hwQ : 0 < wQ)
    (hW : 1 / wQ ≤ K * W) (hidZ : Nd * χ * W = Z) (hϑ : ϑ = 1 / (16 * H))
    (hB1 : 300000000000 * K ^ 4 * H ^ 8 * X ≤ 1)
    (hB2 : 20000000000000 * K ^ 3 * H ^ 13 * Y ≤ 1)
    (hB3 : 600000000000 * K ^ 5 * H ^ 12 * Z ≤ 1) :
    (324 * K / ϑ) * (45 * H ^ 4) * (4200 * K ^ 2 * H * H) *
      (2 * θ' * (4 * K + 2) / (E / 4) + 8 * (H ^ 4 * Nd) * (6 * H * a₁) / θ' +
        (2 * (H ^ 4 * Nd) + 1) * (4 * K * χ / wQ)) ≤ 1 / (16 * H) := by
  have hK0 : 0 < K := by linarith
  have hH0 : 0 < H := by linarith
  have hEX : E * X ≠ 0 := (mul_pos hE hX).ne'
  have t1 : 2 * θ' * (4 * K + 2) / (E / 4) = (4 * K + 2) * X := by
    rw [hθ']
    field_simp
    ring
  have t2 : 8 * (H ^ 4 * Nd) * (6 * H * a₁) / θ' = 384 * H ^ 5 * Y := by
    rw [hθ']
    have : 8 * (H ^ 4 * Nd) * (6 * H * a₁) / (E / 8 * X) = 384 * H ^ 5 * (Nd * a₁) / (E * X) := by
      field_simp
      ring
    rw [this, hid]
    field_simp
  have hH4 : 1 ≤ H ^ 4 := one_le_pow₀ hH1
  have hHNd : 1 ≤ H ^ 4 * Nd := by nlinarith
  have t3 : (2 * (H ^ 4 * Nd) + 1) * (4 * K * χ / wQ) ≤ 12 * K ^ 2 * H ^ 4 * Z := by
    have h1 : 4 * K * χ / wQ ≤ 4 * K * χ * (K * W) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hW (by positivity)
    have h2 : 2 * (H ^ 4 * Nd) + 1 ≤ 3 * (H ^ 4 * Nd) := by linarith
    have h3 : 0 ≤ 4 * K * χ / wQ := by positivity
    calc (2 * (H ^ 4 * Nd) + 1) * (4 * K * χ / wQ) ≤ 3 * (H ^ 4 * Nd) * (4 * K * χ / wQ) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ ≤ 3 * (H ^ 4 * Nd) * (4 * K * χ * (K * W)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 12 * K ^ 2 * H ^ 4 * (Nd * χ * W) := by ring
      _ = 12 * K ^ 2 * H ^ 4 * Z := by rw [hidZ]
  have hP : 324 * K / ϑ = 5184 * K * H := by
    rw [hϑ]
    field_simp
    ring
  rw [hP, t1, t2]
  have hP0 : 0 ≤ 5184 * K * H * (45 * H ^ 4) * (4200 * K ^ 2 * H * H) := by positivity
  have hstep : 5184 * K * H * (45 * H ^ 4) * (4200 * K ^ 2 * H * H) *
      ((4 * K + 2) * X + 384 * H ^ 5 * Y + (2 * (H ^ 4 * Nd) + 1) * (4 * K * χ / wQ)) ≤
      5184 * K * H * (45 * H ^ 4) * (4200 * K ^ 2 * H * H) *
        ((4 * K + 2) * X + 384 * H ^ 5 * Y + 12 * K ^ 2 * H ^ 4 * Z) := by
    gcongr
  refine hstep.trans ?_
  rw [le_div_iff₀ (by positivity)]
  -- monomial comparisons
  have hK3 : K ^ 3 * H ^ 8 * X ≤ K ^ 4 * H ^ 8 * X := by
    have : K ^ 3 ≤ K ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
    gcongr
  have hexp : 5184 * K * H * (45 * H ^ 4) * (4200 * K ^ 2 * H * H) *
      ((4 * K + 2) * X + 384 * H ^ 5 * Y + 12 * K ^ 2 * H ^ 4 * Z) * (16 * H) =
      62705664000 * (K ^ 4 * H ^ 8 * X) + 31352832000 * (K ^ 3 * H ^ 8 * X) +
        6019743744000 * (K ^ 3 * H ^ 13 * Y) + 188116992000 * (K ^ 5 * H ^ 12 * Z) := by
    ring
  rw [hexp]
  nlinarith [hB1, hB2, hB3, hK3]

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
