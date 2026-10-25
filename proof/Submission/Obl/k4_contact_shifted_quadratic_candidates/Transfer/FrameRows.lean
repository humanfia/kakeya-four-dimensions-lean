/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameRows.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameScales

/-!
# Rows, fits and centering of the residual labels

A residual label's three rows are its original rows in the parent chart, with
errors divided by `q₀`, `q₀ ^ 2` and `q₀`; its test fits at the residual width
`N ^ (-h * U' / m)` with hidden derivative one; and the horizontal centering of
its rows is the original centering divided by `q₀`.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Frame

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

/-- Parent time of a residual time. -/
theorem FrameGood.mem_resBlock (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) (τ : ℝ) :
    τ ∈ Data.I (f.level h).T ((f.level h).j i) ↔
      f.t₀ + f.q₀ * τ ∈ f.block h (f.node h i).1 := by
  have hq := f.q₀_pos
  rw [← f.mem_resBlock_time (hg.inside hh i).1]
  have : (f.t₀ + f.q₀ * τ - f.t₀) / f.q₀ = τ := by field_simp; ring
  rw [this]

/-- `N ^ (-κ s₀) / q₀ ≤ K`: the parent block is not much shorter than its width. -/
theorem FrameGood.width_over_q₀ (hg : FrameGood f Rk θ K₂ e₀') :
    D.N k ^ (-D.κ * s₀) / f.q₀ ≤ D.K k := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  have h2 := hg.q₀_le_K.2
  rw [div_eq_mul_inv]
  calc
    D.N k ^ (-D.κ * s₀) * f.q₀⁻¹ ≤ D.N k ^ (-D.κ * s₀) * (D.K k * D.N k ^ (D.κ * s₀)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = D.K k * (D.N k ^ (-D.κ * s₀) * D.N k ^ (D.κ * s₀)) := by ring
    _ = D.K k := by rw [← Real.rpow_add hN]; simp

/-- The original transverse width at a grid level, over `q₀`. -/
theorem FrameGood.g_over_q₀ (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    D.N k ^ (-D.ℓ * f.depth h) / f.q₀ ≤
      D.K k * D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  rw [hg.ℓ_eq, hg.depth_eq hh]
  have hsplit : D.N k ^ (-D.κ * (s₀ + (h : ℝ) * (U' / f.m))) =
      D.N k ^ (-D.κ * s₀) * D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) := by
    rw [← Real.rpow_add hN]; ring_nf
  rw [hsplit, mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right hg.width_over_q₀ (by positivity)

/-- The rows of a residual label. -/
theorem FrameGood.res_rows (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) (l : α) (hl : l ∈ (f.level h).A i) (τ : ℝ)
    (hτ : τ ∈ Data.I (f.level h).T ((f.level h).j i)) :
    |point (f.coeff l) τ 1 - (f.level h).c i 0 - τ * (f.level h).c i 1| ≤
        D.K k ^ 2 * (2 : ℝ) ^ (-(f.resT h : ℤ)) ∧
      |point (f.coeff l) τ 2 - (f.level h).c i 2 - τ * (f.level h).c i 3 -
        (f.level h).c i 4 * point (f.coeff l) τ 1| ≤
        D.K k ^ 2 * (2 : ℝ) ^ (-(f.resT h : ℤ)) *
          D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) ∧
      |f.coeff l 4 - (f.level h).c i 3 - (f.level h).c i 4 * f.coeff l 3| ≤
        D.K k ^ 2 * D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m))) := by
  have hq := f.q₀_pos
  have hK : 1 ≤ D.K k := hg.K_ge
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  set oi := (f.node h i).1
  have ht := (hg.mem_resBlock hh i τ).mp hτ
  have hlA : l ∈ D.A k (f.depth h) oi := f.hist_subset_A h oi _ hl
  obtain ⟨r1, r2, r3⟩ := hg.rows h hh oi l hlA _ ht
  have hq' := hg.resq hh
  have hgq := hg.g_over_q₀ hh
  set g := D.N k ^ (-D.ℓ * f.depth h)
  set g' := D.N k ^ (-D.κ * ((h : ℝ) * (U' / f.m)))
  have hg0 : 0 ≤ g := Real.rpow_nonneg hN.le _
  have hg'0 : 0 ≤ g' := Real.rpow_nonneg hN.le _
  have hql := f.ql_pos h
  have h3 : f.coeff l 3 = D.b k l 3 := by
    rw [f.coeff_base l 3 (by decide)]; rfl
  have h4 : f.coeff l 4 = contactChartCoeff f.t₀ f.q₀ f.Z₀ f.Y₀ (D.b k l) 4 :=
    f.coeff_base l 4 (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [f.point_coeff_one, show (f.level h).c i = contactChartLabel f.t₀ f.q₀ f.Z₀ f.Y₀
      (D.c k (f.depth h) oi) from rfl, contactChart_first_row _ _ _ _ hq.ne', abs_div,
      abs_of_pos hq, hq', div_le_iff₀ hq]
    have e : D.K k ^ 2 * (f.ql h / f.q₀) * f.q₀ = D.K k ^ 2 * f.ql h := by field_simp
    have hKK : D.K k ≤ D.K k ^ 2 := by nlinarith
    have : D.K k * f.ql h ≤ D.K k ^ 2 * (f.ql h / f.q₀) * f.q₀ := by
      rw [e]; exact mul_le_mul_of_nonneg_right hKK hql.le
    exact r1.trans this
  · rw [f.point_coeff_one, f.point_coeff_two,
      show (f.level h).c i = contactChartLabel f.t₀ f.q₀ f.Z₀ f.Y₀
      (D.c k (f.depth h) oi) from rfl, contactChart_second_row _ _ _ _ hq.ne', abs_div,
      abs_of_pos (pow_pos hq 2), hq', div_le_iff₀ (pow_pos hq 2)]
    have hgle : g ≤ D.K k * g' * f.q₀ := by
      rwa [div_le_iff₀ hq] at hgq
    have r2' : |point (D.b k l) (f.t₀ + f.q₀ * τ) 2 - D.c k (f.depth h) oi 2 -
        (f.t₀ + f.q₀ * τ) * D.c k (f.depth h) oi 3 -
        D.c k (f.depth h) oi 4 * point (D.b k l) (f.t₀ + f.q₀ * τ) 1| ≤
        D.K k * f.ql h * g := r2
    calc
      _ ≤ D.K k * f.ql h * g := r2'
      _ ≤ D.K k * f.ql h * (D.K k * g' * f.q₀) :=
        mul_le_mul_of_nonneg_left hgle (by positivity)
      _ = D.K k ^ 2 * (f.ql h / f.q₀) * g' * f.q₀ ^ 2 := by field_simp
  · rw [h3, h4, show (f.level h).c i = contactChartLabel f.t₀ f.q₀ f.Z₀ f.Y₀
      (D.c k (f.depth h) oi) from rfl]
    have h3' : D.b k l 3 = contactChartCoeff f.t₀ f.q₀ f.Z₀ f.Y₀ (D.b k l) 3 := rfl
    rw [h3', contactChart_velocity_row _ _ _ _ hq.ne', abs_div, abs_of_pos hq,
      div_le_iff₀ hq]
    have hgle : g ≤ D.K k * g' * f.q₀ := by
      rwa [div_le_iff₀ hq] at hgq
    calc
      _ ≤ D.K k * g := r3
      _ ≤ D.K k * (D.K k * g' * f.q₀) := mul_le_mul_of_nonneg_left hgle (by positivity)
      _ = D.K k ^ 2 * g' * f.q₀ := by ring

/-- The test of a residual label fits at the residual width with hidden derivative one. -/
theorem FrameGood.res_fit (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) (l : α) (hl : l ∈ (f.level h).B i) (τ : ℝ)
    (hτ : τ ∈ Data.I (f.level h).T ((f.level h).j i)) :
    |eval (point (f.coeff l) τ) ((f.level h).F i)| ≤
        f.H * D.N k ^ (-((h : ℝ) * (U' / f.m))) ∧
      eval (point (f.coeff l) τ) (pderiv 3 ((f.level h).F i)) = 1 ∧
      eval (point (f.coeff l) τ) (pderiv 3 (pderiv 3 ((f.level h).F i))) = 0 := by
  have hN : 0 < D.N k := by linarith [hg.N_ge]
  set oi := (f.node h i).1
  set L := f.pal h oi (lastEntry h (f.node h i).2)
  have hF : (f.level h).F i = X 3 - affineBase (f.resL L) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hF, f.eval_resTest hN]
    have ht := (hg.mem_resBlock hh i τ).mp hτ
    have hentry := f.hist_subset_entry h oi _ hl
    have hfitset := (assignedAffineEntry_subset _ _ _ _ _ _ _ hentry).2
    have hw := hfitset (f.t₀ + f.q₀ * τ) ht
    have ha₀ := f.a₀_pos hN
    rw [abs_div, abs_of_pos ha₀, div_le_iff₀ ha₀, abs_sub_comm]
    calc
      _ ≤ f.H * D.N k ^ (-f.depth h) := hw
      _ = f.H * D.N k ^ (-((h : ℝ) * (U' / f.m))) * f.a₀ := by
        rw [a₀, hg.depth_eq hh, hg.depth_zero, mul_assoc, ← Real.rpow_add hN]
        ring_nf
  · rw [hF, pderiv_resTest]; simp
  · rw [hF, pderiv_resTest]; simp

/-- The horizontal centering of a residual label. -/
theorem FrameGood.res_centered (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) :
    |(f.level h).c i 3 + (f.level h).c i 0 +
        (((f.level h).j i : ℕ) + (1 : ℝ) / 2) * (2 : ℝ) ^ (-(f.resT h : ℤ)) *
          (f.level h).c i 1| +
      |(f.level h).c i 4 - (((f.level h).j i : ℕ) + (1 : ℝ) / 2) *
          (2 : ℝ) ^ (-(f.resT h : ℤ))| ≤ K₂ * (2 : ℝ) ^ (-(f.resT h : ℤ)) := by
  have hq := f.q₀_pos
  set oi := (f.node h i).1
  set c := D.c k (f.depth h) oi
  have hsub := (hg.inside hh i).1
  have hT := hg.T₀_le hh
  have hj := f.resj_val hsub
  have hoff : (D.j k (f.depth 0) f.i₀ : ℕ) * 2 ^ f.resT h ≤
      (D.j k (f.depth h) (f.node h i).1 : ℕ) := (dyadic_offset hsub).1
  have hq' := hg.resq hh
  -- the residual midpoint is the original midpoint in parent time
  have hmid : (((f.level h).j i : ℕ) + (1 : ℝ) / 2) * (2 : ℝ) ^ (-(f.resT h : ℤ)) =
      (f.mid h oi - f.t₀) / f.q₀ := by
    rw [hq', hj, Nat.cast_sub hoff]
    simp only [mid, t₀, left, ql, q₀, T₀, resT, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [zpow_neg, zpow_natCast]
    have hT' : f.Tl 0 ≤ f.Tl h := hT
    have h2 : (2 : ℝ) ^ (f.Tl h - f.Tl 0) * (2 : ℝ) ^ f.Tl 0 = (2 : ℝ) ^ f.Tl h := by
      rw [← pow_add, Nat.sub_add_cancel hT']
    field_simp
    rw [← h2]
    ring
  have hc : (f.level h).c i = contactChartLabel f.t₀ f.q₀ f.Z₀ f.Y₀ c := rfl
  rw [hmid, hc]
  have hc0 : contactChartLabel f.t₀ f.q₀ f.Z₀ f.Y₀ c 0 = (c 0 + f.t₀ * c 1 - f.Z₀) / f.q₀ := rfl
  have hc1 : contactChartLabel f.t₀ f.q₀ f.Z₀ f.Y₀ c 1 = c 1 := rfl
  have hc3 : contactChartLabel f.t₀ f.q₀ f.Z₀ f.Y₀ c 3 = (c 3 + f.Z₀) / f.q₀ := rfl
  have hc4 : contactChartLabel f.t₀ f.q₀ f.Z₀ f.Y₀ c 4 = (c 4 - f.t₀) / f.q₀ := rfl
  rw [hc0, hc1, hc3, hc4]
  have e1 : (c 3 + f.Z₀) / f.q₀ + (c 0 + f.t₀ * c 1 - f.Z₀) / f.q₀ +
      (f.mid h oi - f.t₀) / f.q₀ * c 1 = (c 3 + c 0 + f.mid h oi * c 1) / f.q₀ := by
    field_simp; ring
  have e2 : (c 4 - f.t₀) / f.q₀ - (f.mid h oi - f.t₀) / f.q₀ = (c 4 - f.mid h oi) / f.q₀ := by
    field_simp; ring
  rw [e1, e2, abs_div, abs_div, abs_of_pos hq, ← add_div, hq', mul_div_assoc']
  exact div_le_div_of_nonneg_right (hg.centered h hh oi) hq.le

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
