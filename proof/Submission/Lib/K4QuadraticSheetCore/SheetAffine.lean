import Mathlib
import Submission.Lib.K4QuadraticSheetCore.SheetCore

/-! Adapted from: here:o223 (session x0777, branch x0777). -/

/-!
# Affine predictors from a bounded projected second fundamental form

If the six frame components of the projected second fundamental form are bounded by `Mb`
at a base point `p₀` of the unit cube carrying a root `f₀` of the quadratic test with
hidden derivative `s₀`, the tangent plane `L` of the sheet at `p₀` satisfies
`|G(p, L(p))| ≤ 13 Λ² Mb` on the whole cube (`tangent_plane_bound`). A full-time line with
an event then stays within an explicit polynomial bound of `L` or of the far affine branch
`L - G_w(p, L(p)) / α` (`line_near_affine_branches`); the high-curvature case uses the affine
centre `-β / (2α)` (`line_near_affine_centre`).
-/

namespace Submission.Lib.K4QuadraticSheetCore

open MvPolynomial Set

noncomputable section

/-- A displacement written in the horizontal frame at `p₀`. -/
theorem sffB_frame_decomposition (a g b : ℝ) (gr br : Fin 3 → ℝ) (H : Fin 3 → Fin 3 → ℝ)
    (hH : SymH H) (p₀ u : Fin 3 → ℝ) :
    sffB a g b gr br H u u =
      u 0 ^ 2 * sffB a g b gr br H (frX p₀) (frX p₀) +
      2 * u 0 * u 1 * sffB a g b gr br H (frX p₀) (frZ p₀) +
      u 1 ^ 2 * sffB a g b gr br H (frZ p₀) (frZ p₀) +
      2 * u 0 * (u 2 + u 0 * p₀ 1 - u 1 * p₀ 0) * sffB a g b gr br H (frX p₀) frY +
      2 * u 1 * (u 2 + u 0 * p₀ 1 - u 1 * p₀ 0) * sffB a g b gr br H (frZ p₀) frY +
      (u 2 + u 0 * p₀ 1 - u 1 * p₀ 0) ^ 2 * sffB a g b gr br H frY frY := by
  obtain ⟨h10, h20, h21⟩ := hH
  simp only [sffB, dot3, bil3, frX, frZ, frY, Matrix.cons_val, h10, h20, h21]
  ring

section Tangent

variable (α : ℝ) (β γ : BasePoly) (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
include hβ hγ

/-- The test evaluated at a base point and hidden value. -/
def testAt (p : Fin 3 → ℝ) (w : ℝ) : ℝ := eval p γ + eval p β * w + α * w ^ 2

/-- The tangent plane at a sheet point, as a function of the base point. -/
def tangentPlane (p₀ : Fin 3 → ℝ) (f₀ s₀ : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  f₀ - (f₀ * dot3 (gradAt β p₀) (fun i => p i - p₀ i) +
    dot3 (gradAt γ p₀) (fun i => p i - p₀ i)) / s₀

/-- **Tangent plane bound.** -/
theorem tangent_plane_bound (Λ Mb : ℝ) (hΛ : 1 ≤ Λ) (p₀ : Fin 3 → ℝ)
    (hp₀ : p₀ ∈ Icc (0 : Fin 3 → ℝ) 1) (f₀ s₀ : ℝ)
    (hroot : eval p₀ γ + eval p₀ β * f₀ + α * f₀ ^ 2 = 0) (hs : s₀ = eval p₀ β + 2 * α * f₀)
    (hs₀ : Λ⁻¹ ≤ |s₀|)
    (hMb : |eval p₀ (cXX α β γ)| ≤ Mb ∧ |eval p₀ (cXZ α β γ)| ≤ Mb ∧
      |eval p₀ (cZZ α β γ)| ≤ Mb ∧ |eval p₀ (cXY α β γ)| ≤ Mb ∧
      |eval p₀ (cZY α β γ)| ≤ Mb ∧ |eval p₀ (cYY α β γ)| ≤ Mb)
    (p : Fin 3 → ℝ) (hp : p ∈ Icc (0 : Fin 3 → ℝ) 1) :
    |testAt α β γ p (tangentPlane β γ p₀ f₀ s₀ p)| ≤ 13 * Λ ^ 2 * Mb := by
  have hΛ0 : 0 < Λ := by linarith
  have hs0 : s₀ ≠ 0 := by
    intro h; rw [h, abs_zero] at hs₀; exact absurd hs₀ (not_le.mpr (inv_pos.mpr hΛ0))
  set u : Fin 3 → ℝ := fun i => p i - p₀ i with hu
  have hpu : p = fun i => p₀ i + 1 * u i := by funext i; simp [hu]
  have hγp : eval p γ = eval p₀ γ + dot3 (gradAt γ p₀) u + bil3 (hessAt γ p₀) u u / 2 := by
    rw [hpu, eval_line_quadratic γ hγ p₀ u 1]; ring
  have hβp : eval p β = eval p₀ β + dot3 (gradAt β p₀) u := by
    rw [hpu, eval_line_affine β hβ p₀ u 1]; ring
  have hid := tangent_plane_identity α (eval p₀ γ) (eval p₀ β) (gradAt γ p₀) (gradAt β p₀)
    (hessAt γ p₀) f₀ s₀ u (hessAt_symm γ p₀) hroot hs hs0
  simp only at hid
  have heq : testAt α β γ p (tangentPlane β γ p₀ f₀ s₀ p) =
      sffB α (eval p₀ γ) (eval p₀ β) (gradAt γ p₀) (gradAt β p₀) (hessAt γ p₀) u u /
        (2 * s₀ ^ 2) := by
    rw [← hid, testAt, tangentPlane, hγp, hβp]
  rw [heq, sffB_frame_decomposition _ _ _ _ _ _ (hessAt_symm γ p₀) p₀ u]
  rw [← sffAt, ← sffAt, ← sffAt, ← sffAt, ← sffAt, ← sffAt, ← eval_cXX, ← eval_cXZ,
    ← eval_cZZ, ← eval_cXY, ← eval_cZY, ← eval_cYY]
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hMb
  have hu1 : ∀ i, |u i| ≤ 1 := by
    intro i
    have a := abs_le_one_of_mem_cube hp i
    have b := abs_le_one_of_mem_cube hp₀ i
    have h0 : (0 : ℝ) ≤ p i := hp.1 i
    have h1 : p i ≤ 1 := hp.2 i
    have h2 : (0 : ℝ) ≤ p₀ i := hp₀.1 i
    have h3 : p₀ i ≤ 1 := hp₀.2 i
    simp only [hu]; rw [abs_le]; constructor <;> linarith
  have hp1 := abs_le_one_of_mem_cube hp₀
  set w := u 2 + u 0 * p₀ 1 - u 1 * p₀ 0
  have hw : |w| ≤ 3 := by
    calc |w| ≤ |u 2| + |u 0 * p₀ 1| + |u 1 * p₀ 0| := by
          have := abs_add_le (u 2) (u 0 * p₀ 1)
          have := abs_sub (u 2 + u 0 * p₀ 1) (u 1 * p₀ 0)
          linarith
      _ ≤ 1 + 1 * 1 + 1 * 1 := by
          rw [abs_mul, abs_mul]
          gcongr
          · exact hu1 2
          · exact hu1 0
          · exact hp1 1
          · exact hu1 1
          · exact hp1 0
      _ = 3 := by norm_num
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans m1
  have hnum : |u 0 ^ 2 * eval p₀ (cXX α β γ) + 2 * u 0 * u 1 * eval p₀ (cXZ α β γ) +
      u 1 ^ 2 * eval p₀ (cZZ α β γ) + 2 * u 0 * w * eval p₀ (cXY α β γ) +
      2 * u 1 * w * eval p₀ (cZY α β γ) + w ^ 2 * eval p₀ (cYY α β γ)| ≤ 25 * Mb := by
    have h0 := hu1 0; have h1 := hu1 1
    have t1 : |u 0 ^ 2 * eval p₀ (cXX α β γ)| ≤ Mb := by
      rw [abs_mul, abs_pow]
      calc |u 0| ^ 2 * |eval p₀ (cXX α β γ)| ≤ 1 ^ 2 * Mb := by gcongr
        _ = Mb := by ring
    have t2 : |2 * u 0 * u 1 * eval p₀ (cXZ α β γ)| ≤ 2 * Mb := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      calc 2 * |u 0| * |u 1| * |eval p₀ (cXZ α β γ)| ≤ 2 * 1 * 1 * Mb := by gcongr
        _ = 2 * Mb := by ring
    have t3 : |u 1 ^ 2 * eval p₀ (cZZ α β γ)| ≤ Mb := by
      rw [abs_mul, abs_pow]
      calc |u 1| ^ 2 * |eval p₀ (cZZ α β γ)| ≤ 1 ^ 2 * Mb := by gcongr
        _ = Mb := by ring
    have t4 : |2 * u 0 * w * eval p₀ (cXY α β γ)| ≤ 6 * Mb := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      calc 2 * |u 0| * |w| * |eval p₀ (cXY α β γ)| ≤ 2 * 1 * 3 * Mb := by gcongr
        _ = 6 * Mb := by ring
    have t5 : |2 * u 1 * w * eval p₀ (cZY α β γ)| ≤ 6 * Mb := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      calc 2 * |u 1| * |w| * |eval p₀ (cZY α β γ)| ≤ 2 * 1 * 3 * Mb := by gcongr
        _ = 6 * Mb := by ring
    have t6 : |w ^ 2 * eval p₀ (cYY α β γ)| ≤ 9 * Mb := by
      rw [abs_mul, abs_pow]
      calc |w| ^ 2 * |eval p₀ (cYY α β γ)| ≤ 3 ^ 2 * Mb := by gcongr
        _ = 9 * Mb := by ring
    have := abs_add_le (u 0 ^ 2 * eval p₀ (cXX α β γ) + 2 * u 0 * u 1 * eval p₀ (cXZ α β γ) +
      u 1 ^ 2 * eval p₀ (cZZ α β γ) + 2 * u 0 * w * eval p₀ (cXY α β γ) +
      2 * u 1 * w * eval p₀ (cZY α β γ)) (w ^ 2 * eval p₀ (cYY α β γ))
    have := abs_add_le (u 0 ^ 2 * eval p₀ (cXX α β γ) + 2 * u 0 * u 1 * eval p₀ (cXZ α β γ) +
      u 1 ^ 2 * eval p₀ (cZZ α β γ) + 2 * u 0 * w * eval p₀ (cXY α β γ))
      (2 * u 1 * w * eval p₀ (cZY α β γ))
    have := abs_add_le (u 0 ^ 2 * eval p₀ (cXX α β γ) + 2 * u 0 * u 1 * eval p₀ (cXZ α β γ) +
      u 1 ^ 2 * eval p₀ (cZZ α β γ)) (2 * u 0 * w * eval p₀ (cXY α β γ))
    have := abs_add_le (u 0 ^ 2 * eval p₀ (cXX α β γ) + 2 * u 0 * u 1 * eval p₀ (cXZ α β γ))
      (u 1 ^ 2 * eval p₀ (cZZ α β γ))
    have := abs_add_le (u 0 ^ 2 * eval p₀ (cXX α β γ)) (2 * u 0 * u 1 * eval p₀ (cXZ α β γ))
    linarith
  have hs2 : (Λ ^ 2)⁻¹ ≤ s₀ ^ 2 := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr hΛ0.le) hs₀ 2
    rw [inv_pow, sq_abs] at h; exact h
  have hs2pos : 0 < s₀ ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * s₀ ^ 2)]
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ 25 * Mb := hnum
    _ ≤ 13 * Λ ^ 2 * Mb * (2 * s₀ ^ 2) := by
      have : 1 ≤ Λ ^ 2 * s₀ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hs2 (by positivity : (0 : ℝ) ≤ Λ ^ 2)
        rwa [mul_inv_cancel₀ (by positivity)] at this
      nlinarith

end Tangent

section Branches

set_option maxHeartbeats 4000000 in
/-- The product estimate for explicit affine functions centred at `σe`. -/
theorem affine_product_bound_aux (Ae me A1 m1 α Λ Q₀ σe : ℝ) (hΛ : 1 ≤ Λ) (hQ₀ : 0 ≤ Q₀)
    (hσe : σe ∈ Icc (0 : ℝ) 1)
    (hprod : ∀ σ ∈ Icc (0 : ℝ) 1, |(Ae + A1 * (σ - σe)) * (me + m1 * (σ - σe))| ≤ Q₀)
    (hder : ∀ σ ∈ Icc (0 : ℝ) 1, |(me + m1 * (σ - σe)) + α * (Ae + A1 * (σ - σe))| ≤ Λ)
    (hme : 3 / (4 * Λ) ≤ |me|) (hαe : |α * Ae| ≤ 1 / (4 * Λ)) :
    ∀ σ ∈ Icc (0 : ℝ) 1, |Ae + A1 * (σ - σe)| ≤ 30 * Λ ^ 3 * Q₀ := by
  have hΛ0 : 0 < Λ := by linarith
  have hq : ∀ τ ∈ Icc (-σe) (-σe + 1),
      |Ae * me + (Ae * m1 + A1 * me) * τ + (A1 * m1) * τ ^ 2| ≤ Q₀ := by
    intro τ hτ
    have h := hprod (σe + τ) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have e : (Ae + A1 * (σe + τ - σe)) * (me + m1 * (σe + τ - σe)) =
        Ae * me + (Ae * m1 + A1 * me) * τ + (A1 * m1) * τ ^ 2 := by ring
    rwa [e] at h
  obtain ⟨hc0, hc1, -⟩ := quadratic_coeff_bounds _ _ _ Q₀ (-σe)
    (by linarith [hσe.1]) (by linarith [hσe.2]) hq
  have hslope : |m1 + α * A1| ≤ 2 * Λ := by
    have h1 := hder 1 ⟨by norm_num, le_rfl⟩
    have h0 := hder 0 ⟨le_rfl, by norm_num⟩
    have e : m1 + α * A1 = ((me + m1 * (1 - σe)) + α * (Ae + A1 * (1 - σe))) -
        ((me + m1 * (0 - σe)) + α * (Ae + A1 * (0 - σe))) := by ring
    rw [e]; exact (abs_sub _ _).trans (by linarith)
  have hme0 : 0 < |me| := lt_of_lt_of_le (by positivity) hme
  have hAe : |Ae| ≤ 2 * Λ * Q₀ := by
    have h : |Ae| * |me| ≤ Q₀ := by rw [← abs_mul]; exact hc0
    have h2 : |Ae| * (3 / (4 * Λ)) ≤ Q₀ :=
      le_trans (mul_le_mul_of_nonneg_left hme (abs_nonneg _)) h
    have e : |Ae| = (4 * Λ / 3) * (|Ae| * (3 / (4 * Λ))) := by field_simp
    rw [e]
    calc (4 * Λ / 3) * (|Ae| * (3 / (4 * Λ))) ≤ (4 * Λ / 3) * Q₀ :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 2 * Λ * Q₀ := by nlinarith
  have hm1 : |m1| ≤ 2 * Λ + |α| * |A1| := by
    have h := abs_sub (m1 + α * A1) (α * A1)
    rw [add_sub_cancel_right, abs_mul] at h
    linarith
  have hkey : |A1| * |me| ≤ 10 * Q₀ + |Ae| * |m1| := by
    have h := abs_sub (Ae * m1 + A1 * me) (Ae * m1)
    rw [add_sub_cancel_left, abs_mul, abs_mul] at h
    linarith
  have hαAe : |α| * |Ae| ≤ 1 / (4 * Λ) := by rw [← abs_mul]; exact hαe
  have hfac : 1 / (2 * Λ) ≤ |me| - |α| * |Ae| := by
    have e : 3 / (4 * Λ) - 1 / (4 * Λ) = 1 / (2 * Λ) := by field_simp; ring
    linarith
  have hbound : |A1| * (|me| - |α| * |Ae|) ≤ 10 * Q₀ + 2 * Λ * |Ae| := by
    have h1 := mul_le_mul_of_nonneg_left hm1 (abs_nonneg Ae)
    have e : |A1| * (|me| - |α| * |Ae|) = |A1| * |me| - |Ae| * (|α| * |A1|) := by ring
    rw [e]
    nlinarith [abs_nonneg A1, abs_nonneg α, abs_nonneg Ae]
  have h3 : |A1| * (1 / (2 * Λ)) ≤ 10 * Q₀ + 2 * Λ * (2 * Λ * Q₀) := by
    calc |A1| * (1 / (2 * Λ)) ≤ |A1| * (|me| - |α| * |Ae|) :=
          mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
      _ ≤ 10 * Q₀ + 2 * Λ * |Ae| := hbound
      _ ≤ 10 * Q₀ + 2 * Λ * (2 * Λ * Q₀) := by gcongr
  have hA1 : |A1| ≤ 28 * Λ ^ 3 * Q₀ := by
    have e : |A1| = (2 * Λ) * (|A1| * (1 / (2 * Λ))) := by field_simp
    rw [e]
    calc (2 * Λ) * (|A1| * (1 / (2 * Λ))) ≤ (2 * Λ) * (10 * Q₀ + 2 * Λ * (2 * Λ * Q₀)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 20 * Λ * Q₀ + 8 * Λ ^ 3 * Q₀ := by ring
      _ ≤ 28 * Λ ^ 3 * Q₀ := by
          have h1 : Λ ≤ Λ ^ 3 := by
            have h2 : (1 : ℝ) ≤ Λ ^ 2 := by nlinarith
            calc Λ = Λ * 1 := by ring
              _ ≤ Λ * Λ ^ 2 := by gcongr
              _ = Λ ^ 3 := by ring
          nlinarith
  intro σ hσ
  have hd : |σ - σe| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2, hσe.1, hσe.2]
  calc |Ae + A1 * (σ - σe)| ≤ |Ae| + |A1| * |σ - σe| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ 2 * Λ * Q₀ + 28 * Λ ^ 3 * Q₀ * 1 := by gcongr
    _ ≤ 30 * Λ ^ 3 * Q₀ := by
        have h1 : Λ ≤ Λ ^ 3 := by
          have h2 : (1 : ℝ) ≤ Λ ^ 2 := by nlinarith
          calc Λ = Λ * 1 := by ring
            _ ≤ Λ * Λ ^ 2 := by gcongr
            _ = Λ ^ 3 := by ring
        nlinarith

/-- **Product of affine functions.** If `A, m` are affine on `[0,1]` with `|A m| ≤ Q₀` and
`|m + α A| ≤ Λ` there, and at one time `σe` the factor `m` is at least `3/(4Λ)` while
`α A` is at most `1/(4Λ)`, then `A` is bounded by `30 Λ³ Q₀` on `[0,1]`. -/
theorem affine_product_bound (A m : ℝ → ℝ) (α Λ Q₀ σe : ℝ) (hΛ : 1 ≤ Λ) (hQ₀ : 0 ≤ Q₀)
    (hA : ∀ σ, A σ = A 0 + σ * (A 1 - A 0)) (hm : ∀ σ, m σ = m 0 + σ * (m 1 - m 0))
    (hσe : σe ∈ Icc (0 : ℝ) 1)
    (hprod : ∀ σ ∈ Icc (0 : ℝ) 1, |A σ * m σ| ≤ Q₀)
    (hder : ∀ σ ∈ Icc (0 : ℝ) 1, |m σ + α * A σ| ≤ Λ)
    (hme : 3 / (4 * Λ) ≤ |m σe|) (hαe : |α * A σe| ≤ 1 / (4 * Λ)) :
    ∀ σ ∈ Icc (0 : ℝ) 1, |A σ| ≤ 30 * Λ ^ 3 * Q₀ := by
  have hAσ : ∀ σ, A σ = A σe + (A 1 - A 0) * (σ - σe) := by
    intro σ; rw [hA σ, hA σe]; ring
  have hmσ : ∀ σ, m σ = m σe + (m 1 - m 0) * (σ - σe) := by
    intro σ; rw [hm σ, hm σe]; ring
  have h := affine_product_bound_aux (A σe) (m σe) (A 1 - A 0) (m 1 - m 0) α Λ Q₀ σe hΛ hQ₀ hσe
    (fun σ hσ => by rw [← hAσ σ, ← hmσ σ]; exact hprod σ hσ)
    (fun σ hσ => by rw [← hAσ σ, ← hmσ σ]; exact hder σ hσ) hme hαe
  intro σ hσ
  rw [hAσ σ]
  exact h σ hσ

variable (α : ℝ) (β γ : BasePoly) (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
include hβ hγ

/-- An affine function of the base point. -/
def affineFn (c₀ : ℝ) (c : Fin 3 → ℝ) (p : Fin 3 → ℝ) : ℝ := c₀ + dot3 c p

set_option maxHeartbeats 4000000 in
/-- **Lines near the two affine branches.** A full-time line with an event stays within
`30 Λ³ (Λ + B₁)` of an affine function `L` with `|G(p, L p)| ≤ B₁` on the cube, or of the
far affine branch `L - G_w(p, L p) / α`, in the low-curvature regime. -/
theorem line_near_affine_branches (Λ B₁ c₀ : ℝ) (c : Fin 3 → ℝ) (hΛ : 1 ≤ Λ) (hB₁ : 0 ≤ B₁)
    (hL : ∀ p ∈ Icc (0 : Fin 3 → ℝ) 1, |testAt α β γ p (affineFn c₀ c p)| ≤ B₁)
    (hlow : |α| * (16 * Λ ^ 2 * (Λ + B₁)) ≤ 1)
    (b : Fin 6 → ℝ)
    (hfit : ∀ σ ∈ Icc (0 : ℝ) 1, |testVal α β γ b σ| ≤ Λ ∧ |testDer α β b σ| ≤ Λ)
    (hcube : ∀ σ ∈ Icc (0 : ℝ) 1, lineP b σ ∈ Icc (0 : Fin 3 → ℝ) 1)
    (σe : ℝ) (hσe : σe ∈ Icc (0 : ℝ) 1) (hev : Λ⁻¹ ≤ |testDer α β b σe|) :
    (∀ σ ∈ Icc (0 : ℝ) 1, |lineW b σ - affineFn c₀ c (lineP b σ)| ≤ 30 * Λ ^ 3 * (Λ + B₁)) ∨
    (∀ σ ∈ Icc (0 : ℝ) 1,
      |lineW b σ - (affineFn c₀ c (lineP b σ) -
        (eval (lineP b σ) β + 2 * α * affineFn c₀ c (lineP b σ)) / α)| ≤
        30 * Λ ^ 3 * (Λ + B₁)) := by
  have hΛ0 : 0 < Λ := by linarith
  set Q₀ := Λ + B₁ with hQ₀def
  have hQ₀ : 0 ≤ Q₀ := by positivity
  set Lf : ℝ → ℝ := fun σ => affineFn c₀ c (lineP b σ)
  set Bf : ℝ → ℝ := fun σ => eval (lineP b σ) β
  set A : ℝ → ℝ := fun σ => lineW b σ - Lf σ
  set m : ℝ → ℝ := fun σ => Bf σ + 2 * α * Lf σ + α * A σ
  -- affine structure in time
  have hLf : ∀ σ, Lf σ = Lf 0 + σ * (Lf 1 - Lf 0) := by
    intro σ; simp only [Lf, affineFn, dot3, lineP, Matrix.cons_val]; ring
  have hBf : ∀ σ, Bf σ = Bf 0 + σ * (Bf 1 - Bf 0) := by
    have e : ∀ τ, eval (lineP b τ) β =
        eval (lineP b 0) β + τ * dot3 (gradAt β (lineP b 0)) (lineV b) := by
      intro τ
      have h := lineP_add b 0 τ
      rw [zero_add] at h
      rw [h, eval_line_affine β hβ]
    intro σ
    simp only [Bf]
    rw [e σ, e 1]; ring
  have hA : ∀ σ, A σ = A 0 + σ * (A 1 - A 0) := by
    intro σ; simp only [A, lineW]; rw [hLf σ]; ring
  have hm : ∀ σ, m σ = m 0 + σ * (m 1 - m 0) := by
    intro σ; simp only [m]; rw [hBf σ, hLf σ, hA σ]; ring
  -- the two identities
  have hval : ∀ σ, testVal α β γ b σ = testAt α β γ (lineP b σ) (Lf σ) + A σ * m σ := by
    intro σ; simp only [testVal, testAt, A, m, Bf, Lf]; ring
  have hderv : ∀ σ, testDer α β b σ = m σ + α * A σ := by
    intro σ; simp only [testDer, A, m, Bf, Lf]; ring
  have hprod : ∀ σ ∈ Icc (0 : ℝ) 1, |A σ * m σ| ≤ Q₀ := by
    intro σ hσ
    have h1 := (hfit σ hσ).1
    have h2 : |testAt α β γ (lineP b σ) (Lf σ)| ≤ B₁ := hL _ (hcube σ hσ)
    have e : A σ * m σ = testVal α β γ b σ - testAt α β γ (lineP b σ) (Lf σ) := by
      rw [hval σ]; ring
    rw [e]
    calc _ ≤ |testVal α β γ b σ| + |testAt α β γ (lineP b σ) (Lf σ)| := abs_sub _ _
      _ ≤ Λ + B₁ := by linarith
      _ = Q₀ := hQ₀def.symm
  have hder : ∀ σ ∈ Icc (0 : ℝ) 1, |m σ + α * A σ| ≤ Λ := by
    intro σ hσ; rw [← hderv σ]; exact (hfit σ hσ).2
  have hev' : Λ⁻¹ ≤ |m σe + α * A σe| := by rw [← hderv σe]; exact hev
  have h4 : Λ⁻¹ = 4 / (4 * Λ) := by field_simp
  by_cases hcase : |α * A σe| ≤ 1 / (4 * Λ)
  · left
    have hme : 3 / (4 * Λ) ≤ |m σe| := by
      have := abs_add_le (m σe) (α * A σe)
      have e : 4 / (4 * Λ) - 1 / (4 * Λ) = 3 / (4 * Λ) := by ring
      linarith
    intro σ hσ
    exact affine_product_bound A m α Λ Q₀ σe hΛ hQ₀ hA hm hσe hprod hder hme hcase σ hσ
  · right
    have hcase' : 1 / (4 * Λ) < |α * A σe| := lt_of_not_ge hcase
    have hα0 : α ≠ 0 := by
      intro h; rw [h, zero_mul, abs_zero] at hcase'
      exact absurd hcase' (not_lt.mpr (by positivity))
    -- the factor `m` is small at the event
    have hme_small : |m σe| ≤ 1 / (4 * Λ) := by
      have hp := hprod σe hσe
      rw [abs_mul] at hp
      have h1 : |m σe| * (1 / (4 * Λ)) ≤ |m σe| * |α * A σe| :=
        mul_le_mul_of_nonneg_left hcase'.le (abs_nonneg _)
      have h2 : |m σe| * |α * A σe| ≤ |α| * Q₀ := by
        rw [abs_mul]
        calc |m σe| * (|α| * |A σe|) = |α| * (|A σe| * |m σe|) := by ring
          _ ≤ |α| * Q₀ := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      have h3 : |α| * Q₀ ≤ (1 / (4 * Λ)) * (1 / (4 * Λ)) := by
        have e : (1 / (4 * Λ)) * (1 / (4 * Λ)) = 1 / (16 * Λ ^ 2) := by field_simp; ring
        rw [e, le_div_iff₀ (by positivity)]
        nlinarith [abs_nonneg α]
      have h4 : |m σe| * (1 / (4 * Λ)) ≤ (1 / (4 * Λ)) * (1 / (4 * Λ)) := by linarith
      have hc : (0 : ℝ) < 1 / (4 * Λ) := by positivity
      exact le_of_mul_le_mul_right h4 hc
    set G : ℝ → ℝ := fun σ => Bf σ + 2 * α * Lf σ
    set A₂ : ℝ → ℝ := fun σ => A σ + G σ / α
    set m₂ : ℝ → ℝ := fun σ => α * A σ
    have hA₂ : ∀ σ, A₂ σ = A₂ 0 + σ * (A₂ 1 - A₂ 0) := by
      intro σ; simp only [A₂, G]; rw [hA σ, hBf σ, hLf σ]; field_simp; ring
    have hm₂ : ∀ σ, m₂ σ = m₂ 0 + σ * (m₂ 1 - m₂ 0) := by
      intro σ; simp only [m₂]; rw [hA σ]; ring
    have hprod₂ : ∀ σ ∈ Icc (0 : ℝ) 1, |A₂ σ * m₂ σ| ≤ Q₀ := by
      intro σ hσ
      have e : A₂ σ * m₂ σ = A σ * m σ := by
        simp only [A₂, m₂, m, G]; field_simp; ring
      rw [e]; exact hprod σ hσ
    have hder₂ : ∀ σ ∈ Icc (0 : ℝ) 1, |m₂ σ + α * A₂ σ| ≤ Λ := by
      intro σ hσ
      have e : m₂ σ + α * A₂ σ = m σ + α * A σ := by
        simp only [A₂, m₂, m, G]; field_simp; ring
      rw [e]; exact hder σ hσ
    have hme₂ : 3 / (4 * Λ) ≤ |m₂ σe| := by
      have := abs_add_le (m σe) (α * A σe)
      have e : 4 / (4 * Λ) - 1 / (4 * Λ) = 3 / (4 * Λ) := by ring
      simp only [m₂]
      linarith
    have hαe₂ : |α * A₂ σe| ≤ 1 / (4 * Λ) := by
      have e : α * A₂ σe = m σe := by
        simp only [A₂, m, G]; field_simp; ring
      rw [e]; exact hme_small
    intro σ hσ
    have h := affine_product_bound A₂ m₂ α Λ Q₀ σe hΛ hQ₀ hA₂ hm₂ hσe hprod₂ hder₂ hme₂ hαe₂ σ hσ
    have e : lineW b σ - (affineFn c₀ c (lineP b σ) -
        (eval (lineP b σ) β + 2 * α * affineFn c₀ c (lineP b σ)) / α) = A₂ σ := by
      simp only [A₂, A, G, Bf, Lf]; ring
    rw [e]; exact h

/-- **High curvature.** If the quadratic coefficient is at least `α₀` in size, every line with
bounded hidden derivative stays within `Λ / (2 α₀)` of the affine centre `-β / (2α)`. -/
theorem line_near_affine_centre (α : ℝ) (β : BasePoly) (Λ α₀ : ℝ) (hα₀ : 0 < α₀)
    (hα : α₀ ≤ |α|) (b : Fin 6 → ℝ)
    (hder : ∀ σ ∈ Icc (0 : ℝ) 1, |testDer α β b σ| ≤ Λ) :
    ∀ σ ∈ Icc (0 : ℝ) 1, |lineW b σ - (-(eval (lineP b σ) β) / (2 * α))| ≤ Λ / (2 * α₀) := by
  have hαpos : 0 < |α| := lt_of_lt_of_le hα₀ hα
  have hα0 : α ≠ 0 := abs_pos.mp hαpos
  intro σ hσ
  have e : lineW b σ - (-(eval (lineP b σ) β) / (2 * α)) = testDer α β b σ / (2 * α) := by
    simp only [testDer]; field_simp; ring
  rw [e, abs_div, abs_mul, abs_two]
  have hd := hder σ hσ
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := abs_nonneg (testDer α β b σ)
  nlinarith

end Branches

end

end Submission.Lib.K4QuadraticSheetCore
