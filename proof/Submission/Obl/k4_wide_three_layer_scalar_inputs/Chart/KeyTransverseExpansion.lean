/- Adapted from this LOT tree o218, branch x0950, commit 5227dd4c,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/KeyTransverseExpansion.lean. Original attribution, when present, is preserved below. -/

import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.KeyFrameCoordinates

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs
namespace KeyFrame

open MvPolynomial Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- The two recovered key graph evaluations give exactly the discrepancy
identity consumed below; their original normalization is the same `a`. -/
theorem discrepancy_key_identity (F : CellFrame) (G : MvPolynomial (Fin 2) ℝ)
    (sr br : Fin 6 → ℝ) (Zk Vk Yk : ℝ)
    (hs : ∀ τ y : ℝ, quadraticValue sr τ y =
      eval ![F.t₀ + F.q * τ, keyY (F.q * F.g) F.q Yk Zk τ y] G / F.a)
    (hb : ∀ τ y : ℝ, quadraticValue br τ y =
      F.fit (F.t₀ + F.q * τ) (keyZ Zk Vk (F.t₀ + F.q * τ))
        (keyY (F.q * F.g) F.q Yk Zk τ y) / F.a) :
    ∀ τ y : ℝ,
      (eval ![F.t₀ + F.q * τ, keyY (F.q * F.g) F.q Yk Zk τ y] G -
        F.fit (F.t₀ + F.q * τ) (keyZ Zk Vk (F.t₀ + F.q * τ))
          (keyY (F.q * F.g) F.q Yk Zk τ y)) / F.a = quadraticValue (sr - br) τ y := by
  intro τ y
  have hsub : quadraticValue (sr - br) τ y = quadraticValue sr τ y - quadraticValue br τ y := by
    unfold quadraticValue
    simp only [Pi.sub_apply]
    ring
  rw [hsub, hs, hb]
  ring

/-- A recovered short-key discrepancy has these exact transverse coefficients
in the original true frame. The hypothesis is just the defining key coefficient
identity, before any measure or mass normalization is involved. -/
theorem normalized_transverse_expansion (F : CellFrame)
    (hq : F.q ≠ 0) (hg : F.g ≠ 0) (ha : F.a ≠ 0)
    (G : MvPolynomial (Fin 2) ℝ) (r : Fin 6 → ℝ) (Zk Vk Yk : ℝ)
    (hkey : ∀ τ y : ℝ,
      (eval ![F.t₀ + F.q * τ, keyY (F.q * F.g) F.q Yk Zk τ y] G -
        F.fit (F.t₀ + F.q * τ) (keyZ Zk Vk (F.t₀ + F.q * τ))
          (keyY (F.q * F.g) F.q Yk Zk τ y)) / F.a = quadraticValue r τ y)
    (τ Z U : ℝ) :
    let t := F.t₀ + F.q * τ
    let Y := baseY F t Z
    F.resid t Z (Y + F.q * F.g * U) (eval ![t, Y + F.q * F.g * U] G) =
      F.resid t Z Y (eval ![t, Y] G) +
        f1 r τ (beta F Zk Yk t Z) * U + f2 r * U ^ 2 := by
  let t := F.t₀ + F.q * τ
  let Y := baseY F t Z
  let B := beta F Zk Yk t Z
  have heval (y : ℝ) :
      eval ![t, keyY (F.q * F.g) F.q Yk Zk τ y] G =
        F.fit t (keyZ Zk Vk t) (keyY (F.q * F.g) F.q Yk Zk τ y) +
          F.a * quadraticValue r τ y := by
    have h := (div_eq_iff ha).mp (hkey τ y)
    dsimp only [t]
    linarith
  have hdom₀ : keyY (F.q * F.g) F.q Yk Zk τ B = Y := by
    simpa only [B, Y, t, zero_div, add_zero, mul_zero] using keyY_beta F hq hg Zk Yk τ Z 0
  have hdomU : keyY (F.q * F.g) F.q Yk Zk τ (B + U / 2) = Y + F.q * F.g * U :=
    keyY_beta F hq hg Zk Yk τ Z U
  have hG₀ := heval B
  have hGU := heval (B + U / 2)
  rw [hdom₀] at hG₀
  rw [hdomU] at hGU
  change (eval ![t, Y + F.q * F.g * U] G - F.fit t Z (Y + F.q * F.g * U)) / F.a =
    (eval ![t, Y] G - F.fit t Z Y) / F.a + f1 r τ B * U + f2 r * U ^ 2
  rw [hG₀, hGU, quadratic_key_expansion]
  unfold CellFrame.fit
  field_simp
  <;> ring

/-- On normalized true coordinates the linear transverse term is affine in
`(τ,zZ)` and the quadratic term is the one constant `r5/4`. -/
theorem normalized_frame_transverse_expansion (F : CellFrame)
    (hq : F.q ≠ 0) (hg : F.g ≠ 0) (ha : F.a ≠ 0)
    (G : MvPolynomial (Fin 2) ℝ) (r : Fin 6 → ℝ) (Zk Vk Yk : ℝ)
    (hkey : ∀ τ y : ℝ,
      (eval ![F.t₀ + F.q * τ, keyY (F.q * F.g) F.q Yk Zk τ y] G -
        F.fit (F.t₀ + F.q * τ) (keyZ Zk Vk (F.t₀ + F.q * τ))
          (keyY (F.q * F.g) F.q Yk Zk τ y)) / F.a = quadraticValue r τ y)
    (τ z U : ℝ) :
    let t := F.t₀ + F.q * τ
    let Z := F.c 0 + t * F.c 1 + F.q * z
    let Y := baseY F t Z
    F.resid t Z (Y + F.q * F.g * U) (eval ![t, Y + F.q * F.g * U] G) =
      F.resid t Z Y (eval ![t, Y] G) +
        (frameF1 F Zk Yk r 0 + τ * frameF1 F Zk Yk r 1 + z * frameF1 F Zk Yk r 2) * U +
          f2 r * U ^ 2 := by
  have h := normalized_transverse_expansion F hq hg ha G r Zk Vk Yk hkey τ
    (F.c 0 + (F.t₀ + F.q * τ) * F.c 1 + F.q * z) U
  dsimp only at h ⊢
  rw [f1_frame F hq hg] at h
  exact h

end KeyFrame
end Submission.Obl.k4_wide_three_layer_scalar_inputs
