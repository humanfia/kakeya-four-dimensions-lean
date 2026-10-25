import Submission.Obl.k4_scalar_guarded_tangent_preparation.CellBounds
import Submission.Obl.k4_scalar_guarded_tangent_preparation.GraphMass

/-!
# The bounds of one kept piece of a true layer

`PieceFacts` collects what one piece of a true layer at original depth `r` (slack
`N₀^ε = H`) knows after duration-core pruning: its chart data, the width floor, a pure
observation ceiling `B N₀^{-F}` of the reference law `σ` at depth `r`, and the current
mass floor `ν(A) / (H² 2^T) ≤ ρ(A × I)` with `ρ ≤ σ`. From these come the two-sided
full-prior bounds and the whole-block graph bound, with fixed polynomial losses in `B` and
`H`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_scalar_linear_critical_extremizers
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- What one kept piece knows. -/
structure PieceFacts (p : Code) (m : ℕ) (σ ρ : Fin (p.1 m) → Measure Incidence)
    (r H B F : ℝ) (T : ℕ) (γ : Fin (p.1 m)) (j : Fin (2 ^ T)) (A : Set Coeff)
    (C : Set Incidence) (u v J : ℝ) (P : MvPolynomial (Fin 2) ℝ) : Prop where
  N₀_gt : 1 < p.N m
  H_ge : 2 ≤ H
  B_ge : 1 ≤ B
  r_nonneg : 0 ≤ r
  sub : C ⊆ Split.E p m γ ∩ (A ×ˢ Split.I T j)
  floor : ENNReal.ofReal (p.N m ^ (-F) * J / (H * (2 : ℝ) ^ T)) ≤ Split.mu p m γ C
  J_pos : 0 < J
  J_le : J ≤ H / (2 : ℝ) ^ T
  J_ge : (H * (2 : ℝ) ^ T)⁻¹ ≤ J
  uv : |u| + |v| ≤ H
  deg : P.totalDegree ≤ 2
  coeff : ∀ l ∈ A, ∀ e, |l.2 e| ≤ H
  fit : ∀ l ∈ A, ∀ t ∈ Split.I T j,
    |Split.y l t - u - t * v| ≤ H * J ∧
    |Split.x l t - MvPolynomial.eval ![t, Split.y l t] P| ≤ H * p.N m ^ (-r)
  ceil : (σ γ).map (obsL (p.N m ^ (-r))) ≤
    ENNReal.ofReal (B * p.N m ^ (-F)) • (volume.prod Measure.count)
  ρσ : ρ γ ≤ σ γ
  kept : p.prior m γ A * ENNReal.ofReal ((H ^ 2 * (2 : ℝ) ^ T)⁻¹) ≤
    ρ γ (A ×ˢ Split.I T j)

namespace PieceFacts

variable {p : Code} {m : ℕ} {σ ρ : Fin (p.1 m) → Measure Incidence}
  {r H B F : ℝ} {T : ℕ} {γ : Fin (p.1 m)} {j : Fin (2 ^ T)} {A : Set Coeff}
  {C : Set Incidence} {u v J : ℝ} {P : MvPolynomial (Fin 2) ℝ}

theorem H_pos (h : PieceFacts p m σ ρ r H B F T γ j A C u v J P) : 0 < H := by
  linarith [h.H_ge]

theorem a_pos (h : PieceFacts p m σ ρ r H B F T γ j A C u v J P) :
    0 < p.N m ^ (-r) :=
  Real.rpow_pos_of_pos (by linarith [h.N₀_gt]) _

theorem a_le_one (h : PieceFacts p m σ ρ r H B F T γ j A C u v J P) :
    p.N m ^ (-r) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos h.N₀_gt.le (by linarith [h.r_nonneg])

/-- The prior lower bound in its width form. -/
theorem prior_lower_J (h : PieceFacts p m σ ρ r H B F T γ j A C u v J P) :
    ENNReal.ofReal (p.N m ^ (-F) * J / H) ≤ p.prior m γ A := by
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  have hmono : Split.mu p m γ C ≤ Split.mu p m γ (A ×ˢ Split.I T j) :=
    measure_mono (fun z hz => (h.sub hz).2)
  have hchain := h.floor.trans (hmono.trans (mu_rect_le p m γ A T j))
  have hfl : ENNReal.ofReal (p.N m ^ (-F) * J / H) * ENNReal.ofReal (1 / (2 : ℝ) ^ T) =
      ENNReal.ofReal (p.N m ^ (-F) * J / (H * (2 : ℝ) ^ T)) := by
    have hF : 0 ≤ p.N m ^ (-F) := Real.rpow_nonneg (by linarith [h.N₀_gt]) _
    rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hF h.J_pos.le) h.H_pos.le)]
    congr 1
    have := h.H_pos
    field_simp
  have hpos : ENNReal.ofReal (1 / (2 : ℝ) ^ T) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; positivity
  have htop : ENNReal.ofReal (1 / (2 : ℝ) ^ T) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_left hpos htop).mp (hfl.le.trans hchain)

/-- The prior lower bound. -/
theorem prior_lower (h : PieceFacts p m σ ρ r H B F T γ j A C u v J P) :
    ENNReal.ofReal (p.N m ^ (-F) / (H ^ 2 * (2 : ℝ) ^ T)) ≤ p.prior m γ A := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h.prior_lower_J
  have hH := h.H_pos
  have hJ : 1 / (H * 2 ^ T) ≤ J := by simpa [one_div] using h.J_ge
  have hF : 0 ≤ p.N m ^ (-F) := Real.rpow_nonneg (by linarith [h.N₀_gt]) _
  calc p.N m ^ (-F) / (H ^ 2 * 2 ^ T) = p.N m ^ (-F) * (1 / (H * 2 ^ T)) / H := by
        field_simp
    _ ≤ p.N m ^ (-F) * J / H := by gcongr

theorem t_mem_unit {T : ℕ} {j : Fin (2 ^ T)} {t : ℝ} (ht : t ∈ Split.I T j) :
    t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := ht
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  have hj : ((j : ℕ) : ℝ) + 1 ≤ 2 ^ T := by
    have := j.isLt
    exact_mod_cast this
  refine ⟨le_trans (by positivity) h1, h2.trans ?_⟩
  rw [div_le_one h2T]; exact hj

/-- The conformity of the piece in the coordinates of the graph lemmas. -/
theorem conf (h : PieceFacts p m σ ρ r H B F T γ j A C u v J P) :
    ∀ l ∈ A, ∀ t ∈ Icc ((j : ℕ) / (2 : ℝ) ^ T) ((j : ℕ) / (2 : ℝ) ^ T + 1 / (2 : ℝ) ^ T),
      |spatial l t - (u + v * t)| ≤ H * J ∧
      |hidden l t - MvPolynomial.eval ![t, spatial l t] P| ≤ H * p.N m ^ (-r) := by
  intro l hl t ht
  rw [← I_eq_Icc] at ht
  obtain ⟨hy, hx⟩ := h.fit l hl t ht
  refine ⟨?_, hx⟩
  have : spatial l t - (u + v * t) = Split.y l t - u - t * v := by
    simp only [spatial, Split.y]; ring
  rw [this]; exact hy

/-- The prior upper bound of a kept piece. -/
theorem prior_upper (h : PieceFacts p m σ ρ r H B F T γ j A C u v J P) :
    p.prior m γ A ≤ ENNReal.ofReal (8 * B * H ^ 5 * p.N m ^ (-F) / (2 : ℝ) ^ T) := by
  have hH := h.H_pos
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  have hF : 0 ≤ p.N m ^ (-F) := Real.rpow_nonneg (by linarith [h.N₀_gt]) _
  have hB : 0 ≤ B := by linarith [h.B_ge]
  have hrect := rect_mass_le_of_ceiling (θ := B * p.N m ^ (-F)) h.a_pos h.ceil h.deg
    (Λ := H) (w := H * J) hH.le (mul_nonneg hH.le h.J_pos.le) (A := A) (u := u) (v := v)
    (t₀ := (j : ℕ) / (2 : ℝ) ^ T) (q := 1 / (2 : ℝ) ^ T)
    (fun l hl t ht => by
      rw [← I_eq_Icc] at ht
      exact h.fit l hl t ht)
  rw [← I_eq_Icc] at hrect
  have hchain := h.kept.trans ((h.ρσ _).trans hrect)
  have hc : ENNReal.ofReal ((H ^ 2 * (2 : ℝ) ^ T)⁻¹) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; positivity
  have hct : ENNReal.ofReal ((H ^ 2 * (2 : ℝ) ^ T)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_left hc hct).mp
  refine hchain.trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hJ := h.J_le
  have hJ0 := h.J_pos
  have hH2 := h.H_ge
  -- B N^{-F} (2H+3) (2 H J / 2^T) ≤ 8 B H^5 N^{-F} / 2^T / (H^2 2^T)
  have key : (2 * H + 3) * (1 / 2 ^ T * (2 * (H * J))) ≤
      8 * H ^ 5 / 2 ^ T * (H ^ 2 * 2 ^ T)⁻¹ := by
    have hJ' : H * J ≤ H * (H / 2 ^ T) := mul_le_mul_of_nonneg_left hJ hH.le
    calc (2 * H + 3) * (1 / 2 ^ T * (2 * (H * J)))
        ≤ (2 * H + 3) * (1 / 2 ^ T * (2 * (H * (H / 2 ^ T)))) := by gcongr
      _ = 2 * (2 * H + 3) * H ^ 2 / (2 ^ T * 2 ^ T) := by field_simp
      _ ≤ 8 * H ^ 3 / (2 ^ T * 2 ^ T) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [mul_nonneg (sq_nonneg H) (by linarith : (0:ℝ) ≤ 2 * H - 3)]
      _ = 8 * H ^ 5 / 2 ^ T * (H ^ 2 * 2 ^ T)⁻¹ := by field_simp
  calc B * p.N m ^ (-F) * ((2 * H + 3) * (1 / 2 ^ T * (2 * (H * J))))
      ≤ B * p.N m ^ (-F) * (8 * H ^ 5 / 2 ^ T * (H ^ 2 * 2 ^ T)⁻¹) := by gcongr
    _ = 8 * B * H ^ 5 * p.N m ^ (-F) / 2 ^ T * (H ^ 2 * 2 ^ T)⁻¹ := by ring

/-- The whole-block graph bound of a kept piece. -/
theorem band (h : PieceFacts p m σ ρ r H B F T γ j A C u v J P) :
    ∀ t ∈ Split.I T j, ∀ w ∈ Icc (-2 : ℝ) 2,
      |MvPolynomial.eval ![t, u + t * v + w / (2 : ℝ) ^ T] P| ≤
        4665600 * (8 * B * H ^ 5) ^ 7 := by
  intro t ht w hw
  have hH := h.H_pos
  have hH2 := h.H_ge
  have h2T : (0 : ℝ) < 2 ^ T := by positivity
  have hF : 0 < p.N m ^ (-F) := Real.rpow_pos_of_pos (by linarith [h.N₀_gt]) _
  have hB := h.B_ge
  have hJ0 := h.J_pos
  have hK : 1 ≤ 8 * B * H ^ 5 := by
    have : (1 : ℝ) ≤ H ^ 5 := one_le_pow₀ (by linarith)
    nlinarith
  have hwidth : 1 / (2 : ℝ) ^ T ≤ 8 * B * H ^ 5 * (H * J) := by
    have hJ' : 1 / (H * 2 ^ T) ≤ J := by simpa [one_div] using h.J_ge
    have : 1 / (2 : ℝ) ^ T ≤ H * J := by
      calc 1 / (2 : ℝ) ^ T = H * (1 / (H * 2 ^ T)) := by field_simp
        _ ≤ H * J := by gcongr
    calc 1 / (2 : ℝ) ^ T ≤ H * J := this
      _ = 1 * (H * J) := (one_mul _).symm
      _ ≤ 8 * B * H ^ 5 * (H * J) := mul_le_mul_of_nonneg_right hK (by positivity)
  have hval : ∀ l ∈ A, ∀ t ∈ Icc ((j : ℕ) / (2 : ℝ) ^ T)
      ((j : ℕ) / (2 : ℝ) ^ T + 1 / (2 : ℝ) ^ T),
      |MvPolynomial.eval ![t, spatial l t] P| ≤ 8 * B * H ^ 5 := by
    intro l hl t ht
    have ht' : t ∈ Split.I T j := by rw [I_eq_Icc]; exact ht
    have hx := (h.conf l hl t ht).2
    have hbd := graph_value_bound_of_fit hH.le (h.coeff l hl) (t_mem_unit ht') hx
    have ha := h.a_le_one
    have : 3 * H + H * p.N m ^ (-r) ≤ 8 * B * H ^ 5 := by
      have h1 : H * p.N m ^ (-r) ≤ H := by nlinarith [h.a_pos]
      have h5 : H ≤ H ^ 5 := by
        calc H = H ^ 1 := (pow_one H).symm
          _ ≤ H ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith
    linarith
  have hmass : ENNReal.ofReal (B * p.N m ^ (-F)) * ENNReal.ofReal (2 * H + 3) *
      ENNReal.ofReal ((1 / (2 : ℝ) ^ T * (2 * (H * J))) / (8 * B * H ^ 5)) ≤
      ρ γ (A ×ˢ Icc ((j : ℕ) / (2 : ℝ) ^ T) ((j : ℕ) / (2 : ℝ) ^ T + 1 / (2 : ℝ) ^ T)) := by
    rw [← I_eq_Icc]
    refine le_trans ?_ h.kept
    have hstep : ENNReal.ofReal (p.N m ^ (-F) * J / H) * ENNReal.ofReal ((H ^ 2 * 2 ^ T)⁻¹) ≤
        p.prior m γ A * ENNReal.ofReal ((H ^ 2 * 2 ^ T)⁻¹) := by
      gcongr
      exact h.prior_lower_J
    refine le_trans ?_ hstep
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : (2 * H + 3) / (4 * H ^ 4) ≤ 1 / H ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hH 3]
    calc B * p.N m ^ (-F) * (2 * H + 3) * (1 / 2 ^ T * (2 * (H * J)) / (8 * B * H ^ 5))
        = p.N m ^ (-F) * J / 2 ^ T * ((2 * H + 3) / (4 * H ^ 4)) := by
          field_simp
          ring
      _ ≤ p.N m ^ (-F) * J / 2 ^ T * (1 / H ^ 3) := by gcongr
      _ = p.N m ^ (-F) * J / H * (H ^ 2 * 2 ^ T)⁻¹ := by field_simp
  have ht' : t ∈ Icc ((j : ℕ) / (2 : ℝ) ^ T) ((j : ℕ) / (2 : ℝ) ^ T + 1 / (2 : ℝ) ^ T) := by
    rw [← I_eq_Icc]; exact ht
  have hg := graph_norm_of_ceiling h.ρσ h.a_pos (by positivity) h.ceil h.deg hK
    (by positivity) (by positivity) hwidth hH.le h.conf hval hmass ht' hw
  have heq : u + t * v + w / (2 : ℝ) ^ T = u + t * v + w * (1 / (2 : ℝ) ^ T) := by ring
  rw [heq]
  exact hg

end PieceFacts

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
