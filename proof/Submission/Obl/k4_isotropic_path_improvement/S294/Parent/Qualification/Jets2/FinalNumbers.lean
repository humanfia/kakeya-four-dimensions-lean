-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.FinalNumbers, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/FinalNumbers.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Jets2/FinalNumbers.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/FinalNumbers.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.CoreAux

set_option autoImplicit false

/-!
# The numbers of the final test, version 2

Adapted from this LOT tree: o229, session x0801, branch `x0801` at `38917d30`,
`Jets/FinalNumbers.lean`, for the version-2 final test (`Jets2/FinalTest.lean`: error term
`2 K BR h^(M+1)`, mass bound `4000 K⁶ (…⌊K ((8K+2)/r)^d⌋₊) (2 r + 2 h K + p)`).

With `h = ℓ^{10 s}`, test radius `r = ℓ^s` and `θ ≥ ℓ^{10 s (D+1) + 2 s}`:

* `Ok.final_err`: the Taylor error of the root jets is at most `θ r`;
* `Ok.final_mass`: the final-test mass bound is at most `Q⁻³` (using `d ≤ 1 - 1/s`).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set

noncomputable section

namespace Sched

variable {S : Sched} {ζ : ℝ}

theorem levelScale_eq (S : Sched) {T : ℕ} (hℓ : S.ell ^ (10 * S.s) = ((2 : ℝ) ^ T)⁻¹) :
    levelScale (fun k => T * (S.ω k + 3)) = S.H := by
  funext k
  simp only [levelScale, H]
  rw [pow_mul, ← inv_pow, ← hℓ, ← pow_mul]

theorem Ok.h_eq (_hS : S.Ok ζ) {T : ℕ} (hℓ : S.ell ^ (10 * S.s) = ((2 : ℝ) ^ T)⁻¹) (e : ℕ) :
    (((2 : ℝ) ^ T)⁻¹) ^ e = S.ell ^ (10 * S.s * e) := by
  rw [← hℓ, ← pow_mul]

theorem Ok.final_err (hS : S.Ok ζ) {T : ℕ} (hℓ : S.ell ^ (10 * S.s) = ((2 : ℝ) ^ T)⁻¹)
    (htop : 10 * S.s * (S.D + 1) + 3 * S.s + 1 ≤ S.top) {θ : ℝ}
    (hθ : S.ell ^ (10 * S.s * (S.D + 1) + 2 * S.s) ≤ θ) :
    (((S.D + 1 : ℕ) : ℝ) + 1) * S.w S.D + 2 * S.Q * S.BR S.D * (((2 : ℝ) ^ T)⁻¹) ^ (S.D + 1 + 1) ≤
      θ * S.ell ^ S.s := by
  have hL := hS.levels S.D le_rfl
  have hCJ := hL.2.2.2.2
  have hBR := hL.2.2.2.1
  have hB1 := hL.2.2.1
  have hCJ1 := Ok.one_le_CJ hL
  have hQ1 := hS.one_le_Q
  have hl0 := hS.hell0
  have hl1 := hS.hell1
  set G := gExp S.D S.D
  set a := 10 * S.s * (S.D + 1) + 3 * S.s
  have hE := hS.exp_le_bigE (le_refl S.D)
  have hθr : S.ell ^ a ≤ θ * S.ell ^ S.s := by
    have e : S.ell ^ a = S.ell ^ (10 * S.s * (S.D + 1) + 2 * S.s) * S.ell ^ S.s := by
      rw [← pow_add]; congr 1; ring
    rw [e]; gcongr
  have hw : S.w S.D ≤ S.CJ S.D * (S.ell * S.ell ^ a) := by
    have : S.W S.D ≤ S.ell * S.ell ^ a := by
      rw [W_top, ← pow_succ']; exact hS.ell_pow_le (by omega)
    simp only [w]; gcongr
  have hh : (((2 : ℝ) ^ T)⁻¹) ^ (S.D + 1 + 1) ≤ S.ell * S.ell ^ a := by
    rw [hS.h_eq hℓ, ← pow_succ']
    apply hS.ell_pow_le
    have := hS.hs
    have e : 10 * S.s * (S.D + 1 + 1) = 10 * S.s * (S.D + 1) + 10 * S.s := by ring
    omega
  have hD2 : ((S.D + 1 : ℕ) : ℝ) + 1 ≤ S.Q := by
    have h := hS.D_le (c := 1) (by norm_num) (by norm_num)
    push_cast; linarith
  have hla : 0 ≤ S.ell ^ a := by positivity
  have hw0 : 0 ≤ S.w S.D := by
    have := hS.W_pos S.D
    simp only [w]; positivity
  calc (((S.D + 1 : ℕ) : ℝ) + 1) * S.w S.D +
        2 * S.Q * S.BR S.D * (((2 : ℝ) ^ T)⁻¹) ^ (S.D + 1 + 1)
      ≤ S.Q * (S.CJ S.D * (S.ell * S.ell ^ a)) + 2 * S.Q * S.BR S.D * (S.ell * S.ell ^ a) := by
        gcongr
    _ ≤ S.Q * (S.Q ^ G * (S.ell * S.ell ^ a)) + 2 * S.Q * S.Q ^ G * (S.ell * S.ell ^ a) := by
        gcongr
    _ = (S.ell * (3 * S.Q ^ (G + 1))) * S.ell ^ a := by ring
    _ ≤ (S.ell * S.Q ^ (G + 2)) * S.ell ^ a := by
        gcongr
        calc 3 * S.Q ^ (G + 1) ≤ S.Q * S.Q ^ (G + 1) := by gcongr; linarith [hS.big]
          _ = S.Q ^ (G + 2) := by ring
    _ ≤ 1 * S.ell ^ a := by gcongr; exact hS.ellQ (by omega)
    _ = S.ell ^ a := one_mul _
    _ ≤ θ * S.ell ^ S.s := hθr

/-- `((8Q+2)/ℓ^s)^d ℓ^{s-1} ≤ 8Q+2` when `d ≤ 1 - 1/s`. -/
theorem Ok.rpow_bound (hS : S.Ok ζ) {d : ℝ} (_hd0 : 0 ≤ d) (hds : d ≤ 1 - 1 / S.s) :
    ((8 * S.Q + 2) / S.ell ^ S.s) ^ d * S.ell ^ (S.s - 1) ≤ 8 * S.Q + 2 := by
  have hl0 := hS.hell0
  have hl1 := hS.hell1
  have hQ1 := hS.one_le_Q
  have hs1 := hS.hs
  have hsr : (1 : ℝ) ≤ S.s := by exact_mod_cast hs1
  set x := (8 * S.Q + 2) / S.ell ^ S.s
  have hls : 0 < S.ell ^ S.s := pow_pos hl0 _
  have hx1 : 1 ≤ x := by
    rw [le_div_iff₀ hls, one_mul]
    calc S.ell ^ S.s ≤ 1 := pow_le_one₀ hl0.le hl1
      _ ≤ 8 * S.Q + 2 := by linarith
  have h1 : x ^ d ≤ x ^ (1 - 1 / (S.s : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1 hds
  have h2 : x ^ (1 - 1 / (S.s : ℝ)) = (8 * S.Q + 2) ^ (1 - 1 / (S.s : ℝ)) /
      (S.ell ^ S.s) ^ (1 - 1 / (S.s : ℝ)) := Real.div_rpow (by linarith) hls.le _
  have h3 : (S.ell ^ S.s) ^ (1 - 1 / (S.s : ℝ)) = S.ell ^ (S.s - 1) := by
    rw [← Real.rpow_natCast S.ell S.s, ← Real.rpow_mul hl0.le, ← Real.rpow_natCast S.ell (S.s - 1)]
    congr 1
    rw [Nat.cast_sub hs1]
    field_simp
    push_cast
    ring
  have h4 : (8 * S.Q + 2) ^ (1 - 1 / (S.s : ℝ)) ≤ 8 * S.Q + 2 := by
    calc (8 * S.Q + 2) ^ (1 - 1 / (S.s : ℝ)) ≤ (8 * S.Q + 2) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          have : 0 ≤ 1 / (S.s : ℝ) := by positivity
          linarith
      _ = 8 * S.Q + 2 := Real.rpow_one _
  have hls1 : 0 < S.ell ^ (S.s - 1) := pow_pos hl0 _
  calc x ^ d * S.ell ^ (S.s - 1) ≤ x ^ (1 - 1 / (S.s : ℝ)) * S.ell ^ (S.s - 1) := by gcongr
    _ = (8 * S.Q + 2) ^ (1 - 1 / (S.s : ℝ)) := by
        rw [h2, h3]; field_simp
    _ ≤ 8 * S.Q + 2 := h4

theorem Ok.final_mass (hS : S.Ok ζ) {d : ℝ} (hd0 : 0 ≤ d) (hds : d ≤ 1 - 1 / S.s) {T : ℕ}
    (hℓ : S.ell ^ (10 * S.s) = ((2 : ℝ) ^ T)⁻¹) (htop : S.s ≤ S.top) :
    4000 * S.Q ^ 6 * ((S.n S.D ^ (S.D + 1) * ⌊S.Q * ((8 * S.Q + 2) / S.ell ^ S.s) ^ d⌋₊ : ℕ) : ℝ) *
      (2 * S.ell ^ S.s + 2 * (((2 : ℝ) ^ T)⁻¹ * S.Q) + S.W S.D) ≤ (S.Q ^ 3)⁻¹ := by
  have hL := hS.levels S.D le_rfl
  have hn := hL.2.1
  have hQ1 := hS.one_le_Q
  have hQ0 := hS.Q_pos
  have hbig := hS.big
  have hl0 := hS.hell0
  have hl1 := hS.hell1
  have hs1 := hS.hs
  set G := gExp S.D S.D
  have hE := hS.exp_le_bigE (le_refl S.D)
  have hEbig : G * (S.D + 1) + 13 ≤ bigE S.D := by
    unfold bigE
    have : G * (S.D + 1) + 13 ≤ (S.D + 3) * G + 20 := by
      have e : (S.D + 3) * G = G * (S.D + 1) + 2 * G := by ring
      omega
    exact this
  set x := (8 * S.Q + 2) / S.ell ^ S.s
  have hx0 : 0 ≤ x := by positivity
  have hrp := hS.rpow_bound hd0 hds
  -- the scale factor
  have hsum : 2 * S.ell ^ S.s + 2 * (((2 : ℝ) ^ T)⁻¹ * S.Q) + S.W S.D ≤
      (3 + 2 * S.Q) * (S.ell ^ (S.s - 1) * S.ell) := by
    have e : S.ell ^ (S.s - 1) * S.ell = S.ell ^ S.s := by
      rw [← pow_succ, Nat.sub_add_cancel hs1]
    rw [e]
    have hh : ((2 : ℝ) ^ T)⁻¹ ≤ S.ell ^ S.s := by
      rw [← hℓ]; exact hS.ell_pow_le (by nlinarith)
    have hW : S.W S.D ≤ S.ell ^ S.s := by rw [W_top]; exact hS.ell_pow_le htop
    nlinarith
  have hfl : ((⌊S.Q * x ^ d⌋₊ : ℕ) : ℝ) ≤ S.Q * x ^ d := Nat.floor_le (by positivity)
  have hnM : ((S.n S.D : ℝ)) ^ (S.D + 1) ≤ S.Q ^ (G * (S.D + 1)) := by
    rw [pow_mul]; gcongr
  have h1 : (8 * S.Q + 2) * (3 + 2 * S.Q) ≤ 20 * S.Q ^ 2 := by nlinarith
  have hpos : 0 ≤ 2 * S.ell ^ S.s + 2 * (((2 : ℝ) ^ T)⁻¹ * S.Q) + S.W S.D := by
    have := hS.W_pos S.D
    positivity
  push_cast
  calc 4000 * S.Q ^ 6 * ((S.n S.D : ℝ) ^ (S.D + 1) * (⌊S.Q * x ^ d⌋₊ : ℝ)) *
        (2 * S.ell ^ S.s + 2 * (((2 : ℝ) ^ T)⁻¹ * S.Q) + S.W S.D)
      ≤ 4000 * S.Q ^ 6 * (S.Q ^ (G * (S.D + 1)) * (S.Q * x ^ d)) *
          ((3 + 2 * S.Q) * (S.ell ^ (S.s - 1) * S.ell)) := by
        gcongr
    _ = 4000 * S.Q ^ 7 * S.Q ^ (G * (S.D + 1)) * (3 + 2 * S.Q) * (x ^ d * S.ell ^ (S.s - 1)) *
          S.ell := by ring
    _ ≤ 4000 * S.Q ^ 7 * S.Q ^ (G * (S.D + 1)) * (3 + 2 * S.Q) * (8 * S.Q + 2) * S.ell := by
        gcongr
    _ = 4000 * S.Q ^ 7 * S.Q ^ (G * (S.D + 1)) * ((8 * S.Q + 2) * (3 + 2 * S.Q)) * S.ell := by
        ring
    _ ≤ 4000 * S.Q ^ 7 * S.Q ^ (G * (S.D + 1)) * (20 * S.Q ^ 2) * S.ell := by gcongr
    _ = 80000 * S.Q ^ (G * (S.D + 1) + 9) * S.ell := by ring
    _ ≤ S.Q * S.Q ^ (G * (S.D + 1) + 9) * S.ell := by gcongr; linarith
    _ = (S.ell * S.Q ^ (G * (S.D + 1) + 13)) * (S.Q ^ 3)⁻¹ := by
        field_simp; ring
    _ ≤ 1 * (S.Q ^ 3)⁻¹ := by gcongr; exact hS.ellQ hEbig
    _ = (S.Q ^ 3)⁻¹ := one_mul _

end Sched

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
