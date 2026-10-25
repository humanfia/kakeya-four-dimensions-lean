-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.StripTransfer, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.WorldStates
import Submission.Lib.K4ChartLifting

/-!
# Strips of the original velocity are strips of the normalized velocity

The front measures breadth in the velocity normalized to an active packet `a`,
`PathData.normalizedVelocity a = 2^-T Q_a⁻¹ (v - u_a)`, at one strip width `r`. The row packet
asks for breadth in the ORIGINAL velocity `v`, at its own width `w`. Writing `v - u_a = 2^T Q_a x`
for the normalized velocity `x`, the strip `|⟨n, v⟩ - t| ≤ w` is the strip of `x` with normal
`2^T Q_aᵀ n`, whose length is at least `2^T |det Q_a| / Σ|Q_a|` (Cramer). So an original strip of
width `w` lies in a normalized strip of width `r` once `w Σ|Q_a| ≤ r 2^T |det Q_a|`; for a path
packet (`|det Q| 4^T ≥ N^(-2 δ₀ L)`, `Σ|Q| ≤ κ 2^-T`) this is `w κ N^(2 δ₀ L) ≤ r`.

* `det_mul_norm_le`: `|det M| ‖n‖ ≤ Σ|M| ‖Mᵀ n‖` in the plane.
* `normalized_strip_of_strip`: the strip inclusion.
* `world_breadth_original`: the front's per-history breadth (`Forward/WorldStates.lean`) for
  strips of the original velocity.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294

namespace Forward

open MeasureTheory Set
open Submission.Lib.K4ChartLifting
open Submission.Lib.K4VelocityStrips
open scoped ENNReal

noncomputable section

theorem inner_two (n x : EuclideanSpace ℝ (Fin 2)) : inner ℝ n x = n 0 * x 0 + n 1 * x 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- Cramer's rule in the plane: `|det M| ‖n‖ ≤ Σ|M| ‖Mᵀ n‖`. -/
theorem det_mul_norm_le (M : Matrix (Fin 2) (Fin 2) ℝ) (n : EuclideanSpace ℝ (Fin 2)) :
    |M.det| * ‖n‖ ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |M e e'|) *
      ‖Matrix.toEuclideanLin M.transpose n‖ := by
  set y := Matrix.toEuclideanLin M.transpose n with hy
  have hy0 : y 0 = M 0 0 * n 0 + M 1 0 * n 1 := by
    rw [hy, toEuclideanLin_apply_two]; simp [Matrix.transpose_apply]
  have hy1 : y 1 = M 0 1 * n 0 + M 1 1 * n 1 := by
    rw [hy, toEuclideanLin_apply_two]; simp [Matrix.transpose_apply]
  have hdet : M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := Matrix.det_fin_two M
  have hc0 : M.det * n 0 = M 1 1 * y 0 - M 1 0 * y 1 := by rw [hy0, hy1, hdet]; ring
  have hc1 : M.det * n 1 = M 0 0 * y 1 - M 0 1 * y 0 := by rw [hy0, hy1, hdet]; ring
  have hn := plane_norm_le n
  have h0 := plane_abs_le_norm y 0
  have h1 := plane_abs_le_norm y 1
  have e0 : |M.det| * |n 0| ≤ (|M 1 1| + |M 1 0|) * ‖y‖ := by
    rw [← abs_mul, hc0]
    calc |M 1 1 * y 0 - M 1 0 * y 1| ≤ |M 1 1| * |y 0| + |M 1 0| * |y 1| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ |M 1 1| * ‖y‖ + |M 1 0| * ‖y‖ := by gcongr
      _ = _ := by ring
  have e1 : |M.det| * |n 1| ≤ (|M 0 0| + |M 0 1|) * ‖y‖ := by
    rw [← abs_mul, hc1]
    calc |M 0 0 * y 1 - M 0 1 * y 0| ≤ |M 0 0| * |y 1| + |M 0 1| * |y 0| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ |M 0 0| * ‖y‖ + |M 0 1| * ‖y‖ := by gcongr
      _ = _ := by ring
  have hd0 : 0 ≤ |M.det| := abs_nonneg _
  calc |M.det| * ‖n‖ ≤ |M.det| * (|n 0| + |n 1|) := mul_le_mul_of_nonneg_left hn hd0
    _ = |M.det| * |n 0| + |M.det| * |n 1| := by ring
    _ ≤ (|M 1 1| + |M 1 0|) * ‖y‖ + (|M 0 0| + |M 0 1|) * ‖y‖ := add_le_add e0 e1
    _ = (∑ e : Fin 2, ∑ e' : Fin 2, |M e e'|) * ‖y‖ := by
        simp only [Fin.sum_univ_two]; ring

/-- **Original strips are normalized strips.** If `w Σ|Q| ≤ r s |det Q|`, every velocity in the
strip `|⟨n, v⟩ - t| ≤ w` has its normalized velocity `s⁻¹ Q⁻¹ (v - u)` in one strip of width `r`
(with a unit normal and an offset depending only on `Q, s, u, n, t`). -/
theorem normalized_strip_of_strip (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) {s : ℝ}
    (hs : 0 < s) (u n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) (t : ℝ) {w r : ℝ}
    (hwr : w * (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ r * (s * |Q.det|)) :
    ∃ (n' : StripSpace) (β : ℝ), ‖n'‖ = 1 ∧ ∀ vel : EuclideanSpace ℝ (Fin 2),
      |inner ℝ n vel - t| ≤ w → s⁻¹ • Matrix.toEuclideanLin Q⁻¹ (vel - u) ∈ affineStrip n' β r := by
  set m : EuclideanSpace ℝ (Fin 2) := s • Matrix.toEuclideanLin Q.transpose n with hm
  have hdet0 : 0 < |Q.det| := abs_pos.mpr hQ
  have hS0 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| := by positivity
  have hcr := det_mul_norm_le Q n
  rw [hn, mul_one] at hcr
  have hmnorm : ‖m‖ = s * ‖Matrix.toEuclideanLin Q.transpose n‖ := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  -- the normal has length at least `s |det Q| / Σ|Q|`
  have hlow : s * |Q.det| ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) * ‖m‖ := by
    rw [hmnorm]
    calc s * |Q.det| ≤ s * ((∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) *
          ‖Matrix.toEuclideanLin Q.transpose n‖) := mul_le_mul_of_nonneg_left hcr hs.le
      _ = _ := by ring
  have hmpos : 0 < ‖m‖ := by
    by_contra hcon
    have h0 : ‖m‖ = 0 := le_antisymm (not_lt.mp hcon) (norm_nonneg _)
    rw [h0, mul_zero] at hlow
    have : 0 < s * |Q.det| := mul_pos hs hdet0
    linarith
  refine ⟨‖m‖⁻¹ • m, (t - inner ℝ n u) / ‖m‖, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmpos), inv_mul_cancel₀ hmpos.ne']
  intro vel hvel
  set x : EuclideanSpace ℝ (Fin 2) := s⁻¹ • Matrix.toEuclideanLin Q⁻¹ (vel - u) with hx
  -- `vel - u = s Q x`
  have hQinv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  have e00 : Q 0 0 * Q⁻¹ 0 0 + Q 0 1 * Q⁻¹ 1 0 = 1 := by
    have := congrFun (congrFun hQinv 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e01 : Q 0 0 * Q⁻¹ 0 1 + Q 0 1 * Q⁻¹ 1 1 = 0 := by
    have := congrFun (congrFun hQinv 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e10 : Q 1 0 * Q⁻¹ 0 0 + Q 1 1 * Q⁻¹ 1 0 = 0 := by
    have := congrFun (congrFun hQinv 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e11 : Q 1 0 * Q⁻¹ 0 1 + Q 1 1 * Q⁻¹ 1 1 = 1 := by
    have := congrFun (congrFun hQinv 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hx0 : x 0 = s⁻¹ * (Q⁻¹ 0 0 * (vel 0 - u 0) + Q⁻¹ 0 1 * (vel 1 - u 1)) := by
    rw [hx, PiLp.smul_apply, toEuclideanLin_apply_two]; simp
  have hx1 : x 1 = s⁻¹ * (Q⁻¹ 1 0 * (vel 0 - u 0) + Q⁻¹ 1 1 * (vel 1 - u 1)) := by
    rw [hx, PiLp.smul_apply, toEuclideanLin_apply_two]; simp
  have hv0 : vel 0 - u 0 = s * (Q 0 0 * x 0 + Q 0 1 * x 1) := by
    rw [hx0, hx1]; field_simp
    linear_combination (-(vel 0 - u 0)) * e00 - (vel 1 - u 1) * e01
  have hv1 : vel 1 - u 1 = s * (Q 1 0 * x 0 + Q 1 1 * x 1) := by
    rw [hx0, hx1]; field_simp
    linear_combination (-(vel 0 - u 0)) * e10 - (vel 1 - u 1) * e11
  have hm0 : m 0 = s * (Q 0 0 * n 0 + Q 1 0 * n 1) := by
    rw [hm, PiLp.smul_apply, toEuclideanLin_apply_two]; simp [Matrix.transpose_apply]
  have hm1 : m 1 = s * (Q 0 1 * n 0 + Q 1 1 * n 1) := by
    rw [hm, PiLp.smul_apply, toEuclideanLin_apply_two]; simp [Matrix.transpose_apply]
  -- the normalized strip coordinate is the original one divided by `‖m‖`
  have key : inner ℝ x (‖m‖⁻¹ • m) - (t - inner ℝ n u) / ‖m‖ =
      (inner ℝ n vel - t) / ‖m‖ := by
    rw [inner_smul_right, inner_two, inner_two, inner_two, hm0, hm1]
    have hvel0 : vel 0 = u 0 + s * (Q 0 0 * x 0 + Q 0 1 * x 1) := by linarith
    have hvel1 : vel 1 = u 1 + s * (Q 1 0 * x 0 + Q 1 1 * x 1) := by linarith
    rw [hvel0, hvel1]
    field_simp
    ring
  show |inner ℝ x (‖m‖⁻¹ • m) - (t - inner ℝ n u) / ‖m‖| ≤ r
  rw [key, abs_div, abs_of_pos hmpos, div_le_iff₀ hmpos]
  have hw0 : 0 ≤ w := le_trans (abs_nonneg _) hvel
  -- `w ≤ r ‖m‖`
  have hr0 : 0 ≤ r := by
    by_contra hneg
    have hrneg : r < 0 := not_le.mp hneg
    have : r * (s * |Q.det|) < 0 := mul_neg_of_neg_of_pos hrneg (mul_pos hs hdet0)
    nlinarith
  calc |inner ℝ n vel - t| ≤ w := hvel
    _ ≤ r * ‖m‖ := by
        by_cases hS : (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) = 0
        · rw [hS, zero_mul] at hlow
          have : 0 < s * |Q.det| := mul_pos hs hdet0
          linarith
        · have hSpos : 0 < ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| := lt_of_le_of_ne hS0 (Ne.symm hS)
          have h1 : w * (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤
              r * ((∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) * ‖m‖) :=
            hwr.trans (mul_le_mul_of_nonneg_left hlow hr0)
          have h2 : w * (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤
              (r * ‖m‖) * (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) := by
            calc _ ≤ _ := h1
              _ = _ := by ring
          exact le_of_mul_le_mul_right h2 hSpos

section Front

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a₁ A : ℝ} {θ : ENNReal}

/-- **Per-history breadth for strips of the ORIGINAL velocity.** For a good end history `e` of an
active packet `a`, every strip `|⟨n, v⟩ - t| ≤ w` of the original velocity carries at most
`8 fraction` of the world mass of `e` inside the likelihood cut, once
`w Σ|Q_a| ≤ r 2^T |det Q_a|` (`r` the front's normalized strip width). -/
theorem world_breadth_original (F : PaletteFamily Q i stop a₁ A θ) {a : Fin p.C}
    (h : TransferData Q F a) {r fraction : ℝ} (hfr : 0 ≤ fraction) {e : ℕ}
    (he : e ∈ goodEnd F r fraction a) (hQ : (p.Q a).det ≠ 0)
    (n : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) (t : ℝ) {w : ℝ}
    (hwr : w * (∑ e : Fin 2, ∑ e' : Fin 2, |p.Q a e e'|) ≤
      r * ((2 : ℝ) ^ p.T (p.lev a) * |(p.Q a).det|)) :
    ((d.ν k (p.γ a)).prod volume) (worldSection (p.γ a)
        {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a ∧
          |inner ℝ n (v z.2.1) - t| ≤ w}) ≤
      ENNReal.ofReal (8 * fraction) * ((d.ν k (p.γ a)).prod volume) (worldSection (p.γ a)
        {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U a}) := by
  obtain ⟨n', β, hn', hsub⟩ := normalized_strip_of_strip (p.Q a) hQ
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ p.T (p.lev a)) (p.u a) n hn t hwr
  refine le_trans (measure_mono ?_) (world_breadth F h hfr he n' hn' β)
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hx
  exact ⟨h1, h2, hsub _ h3⟩

end Front

end

end Forward

end Submission.Obl.k4_isotropic_path_improvement.S294
