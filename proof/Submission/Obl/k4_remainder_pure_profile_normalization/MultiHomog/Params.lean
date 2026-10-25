import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Family

/-!
# Bounds on the encoding parameters of one sample
-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set Filter
open scoped ENNReal

theorem delta_bounds' {N : ℝ} (hN : 0 < N) (r : ℝ) :
    N ^ (-r) ≤ δ N r ∧ δ N r ≤ 2 * N ^ (-r) :=
  Submission.Obl.k4_quadratic_atlas_normalization.delta_bounds hN r

theorem delta_pos (N r : ℝ) : 0 < δ N r := by
  unfold δ; positivity

namespace Sample

variable (S : Sample)

/-- The standing numerical hypotheses on one sample. -/
structure Hyp : Prop where
  N_ge : 2 ≤ S.N
  K_ge : 1 ≤ S.K
  K_le : S.K ≤ S.N ^ S.M₀
  W_ge : 1 ≤ S.W
  W_le : (S.W : ℝ) ≤ S.N ^ S.M
  ω_nonneg : ∀ γ, 0 ≤ S.ω γ
  ω_le : ∀ γ, S.ω γ ≤ 1
  B_pos : ∀ γ, 0 < S.B γ
  B_le : ∀ γ, S.B γ ≤ S.N ^ S.M
  B_inv_le : ∀ γ, (S.B γ)⁻¹ ≤ S.N ^ S.M

variable {S}

namespace Hyp

variable (h : S.Hyp)
include h

theorem N_pos : 0 < S.N := by linarith [h.N_ge]

theorem one_le_N : 1 ≤ S.N := by linarith [h.N_ge]

theorem K_pos : 0 < S.K := by linarith [h.K_ge]

theorem pow_pos' (n : ℕ) : 0 < S.N ^ n := pow_pos h.N_pos n

theorem one_le_pow (n : ℕ) : 1 ≤ S.N ^ n := one_le_pow₀ h.one_le_N

theorem Lam_pos : 0 < S.Lam := h.pow_pos' _

theorem sixteen_le_pow_four : (16 : ℝ) ≤ S.N ^ 4 := by
  calc (16 : ℝ) = 2 ^ 4 := by norm_num
    _ ≤ S.N ^ 4 := pow_le_pow_left₀ (by norm_num) h.N_ge 4

theorem Lam_ge : 16 * (S.W : ℝ) * S.K ^ 2 ≤ S.Lam := by
  have hL : S.Lam = S.N ^ S.M * (S.N ^ S.M₀) ^ 2 * S.N ^ 4 := by
    unfold Sample.Lam Sample.mL
    rw [← pow_mul, ← pow_add, ← pow_add]
    ring_nf
  rw [hL]
  have hW0 : (0 : ℝ) ≤ S.W := Nat.cast_nonneg _
  have hK2 : S.K ^ 2 ≤ (S.N ^ S.M₀) ^ 2 := pow_le_pow_left₀ h.K_pos.le h.K_le 2
  have h16 := h.sixteen_le_pow_four
  have h1 : (S.W : ℝ) * S.K ^ 2 ≤ S.N ^ S.M * (S.N ^ S.M₀) ^ 2 :=
    mul_le_mul h.W_le hK2 (by positivity) (h.pow_pos' _).le
  calc 16 * (S.W : ℝ) * S.K ^ 2 = (S.W : ℝ) * S.K ^ 2 * 16 := by ring
    _ ≤ S.N ^ S.M * (S.N ^ S.M₀) ^ 2 * S.N ^ 4 :=
      mul_le_mul h1 h16 (by norm_num) (by have := h.pow_pos' S.M; positivity)

theorem a_pos : 0 < S.a := div_pos (by linarith [h.K_pos]) h.Lam_pos

theorem aK_le : S.a * S.K ≤ 1 / 4 := by
  have hL := h.Lam_ge
  have hW : (1 : ℝ) ≤ S.W := by exact_mod_cast h.W_ge
  have hK := h.K_pos
  unfold Sample.a
  rw [div_mul_eq_mul_div, div_le_iff₀ h.Lam_pos]
  nlinarith [sq_nonneg S.K]

theorem a_le : S.a ≤ 1 / 4 := by
  have := h.aK_le
  have ha := h.a_pos
  nlinarith [h.K_ge]

theorem thr_pos : 0 < S.thr := by
  unfold Sample.thr
  have := h.pow_pos' S.M
  have := h.K_pos
  positivity

theorem thr_le_one : S.thr ≤ 1 := by
  unfold Sample.thr
  apply inv_le_one_of_one_le₀
  have h1 := h.one_le_pow S.M
  nlinarith [h.K_ge]

theorem max_pos (γ : Fin S.W) : 0 < max (S.ω γ) S.thr :=
  lt_of_lt_of_le h.thr_pos (le_max_right _ _)

theorem max_le_one (γ : Fin S.W) : max (S.ω γ) S.thr ≤ 1 :=
  max_le (h.ω_le γ) h.thr_le_one

theorem b_pos (γ : Fin S.W) : 0 < S.b γ := div_pos (h.max_pos γ) (by linarith [h.K_pos])

theorem bK_le (γ : Fin S.W) : S.b γ * S.K ≤ 1 / 4 := by
  unfold Sample.b
  have hK := h.K_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith [h.max_le_one γ]

theorem b_le (γ : Fin S.W) : S.b γ ≤ 1 / 4 := by
  have := h.bK_le γ
  have := h.b_pos γ
  nlinarith [h.K_ge]

theorem o_nonneg (γ : Fin S.W) : 0 ≤ S.o γ := by
  unfold Sample.o
  have := h.Lam_pos
  positivity

theorem o_le (γ : Fin S.W) : S.o γ ≤ 9 / 16 := by
  unfold Sample.o
  have hL := h.Lam_ge
  have hγ : ((γ : ℕ) : ℝ) ≤ S.W := by exact_mod_cast γ.2.le
  have hK := h.K_pos
  rw [div_le_iff₀ h.Lam_pos]
  have : 9 * S.K ^ 2 * ((γ : ℕ) : ℝ) ≤ 9 * S.K ^ 2 * S.W := by gcongr
  nlinarith

omit h in
theorem s0_nonneg : 0 ≤ S.s0 := by unfold Sample.s0; positivity

theorem θ_pos (γ : Fin S.W) : 0 < S.θ γ := mul_pos (h.B_pos γ) (delta_pos _ _)

/-- The encoded hidden coefficients are at most one half. -/
theorem θN_le (γ : Fin S.W) : S.θ γ * S.N ^ S.M ≤ 1 / 2 := by
  have hδ := (delta_bounds' h.N_pos S.s0).2
  have hs : S.N ^ (-S.s0) = (S.N ^ (2 * S.M + 2))⁻¹ := by
    unfold Sample.s0
    rw [Real.rpow_neg h.N_pos.le, Real.rpow_natCast]
  have hP : 0 < S.N ^ (2 * S.M + 2) := h.pow_pos' _
  have hsplit : S.N ^ (2 * S.M + 2) = S.N ^ S.M * S.N ^ S.M * S.N ^ 2 := by
    rw [← pow_add, ← pow_add]; ring_nf
  have h4 : (4 : ℝ) ≤ S.N ^ 2 := by nlinarith [h.N_ge]
  have hNM := h.pow_pos' S.M
  unfold Sample.θ
  calc S.B γ * δ S.N S.s0 * S.N ^ S.M ≤ S.N ^ S.M * (2 * (S.N ^ (2 * S.M + 2))⁻¹) * S.N ^ S.M := by
        gcongr
        · exact (delta_pos _ _).le
        · exact h.B_le γ
        · rw [← hs]; exact hδ
    _ = 2 * (S.N ^ S.M * S.N ^ S.M) / S.N ^ (2 * S.M + 2) := by
        field_simp
    _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hP, hsplit]
        nlinarith [mul_pos hNM hNM]

theorem θ_le (γ : Fin S.W) : S.θ γ ≤ 1 / 2 := by
  have := h.θN_le γ
  have h1 := h.one_le_pow S.M
  have := h.θ_pos γ
  nlinarith

/-- Lower bounds on the scales, used for the coefficients of the encoded prior. -/
theorem a_ge : (S.N ^ S.mL)⁻¹ ≤ S.a := by
  unfold Sample.a Sample.Lam
  rw [div_eq_mul_inv]
  have := h.pow_pos' S.mL
  have : (1 : ℝ) ≤ 4 * S.K := by linarith [h.K_ge]
  nlinarith [inv_pos.mpr (h.pow_pos' S.mL)]

theorem thr_ge : (S.N ^ (2 * S.M₀ + S.M + 1))⁻¹ ≤ S.thr := by
  unfold Sample.thr
  apply inv_anti₀ (by have := h.pow_pos' S.M; have := h.K_pos; positivity)
  have hsplit : S.N ^ (2 * S.M₀ + S.M + 1) = S.N ^ S.M₀ * S.N ^ S.M₀ * S.N ^ S.M * S.N := by
    rw [← pow_add, ← pow_add, ← pow_succ]; ring_nf
  rw [hsplit]
  have hK := h.K_le
  have hNM := h.pow_pos' S.M
  have hM0 := h.one_le_pow S.M₀
  have hK1 := h.K_ge
  have h2 : 2 * S.K ≤ S.N ^ S.M₀ * S.N := by nlinarith [h.N_ge]
  have h3 : 0 ≤ S.N ^ S.M₀ * S.N * S.N ^ S.M := by have := h.N_pos; positivity
  calc 2 * S.K * S.N ^ S.M ≤ (S.N ^ S.M₀ * S.N) * S.N ^ S.M := by gcongr
    _ = S.N ^ S.M₀ * S.N * S.N ^ S.M * 1 := by ring
    _ ≤ S.N ^ S.M₀ * S.N * S.N ^ S.M * S.N ^ S.M₀ := mul_le_mul_of_nonneg_left hM0 h3
    _ = S.N ^ S.M₀ * S.N ^ S.M₀ * S.N ^ S.M * S.N := by ring

theorem b_ge (γ : Fin S.W) : (S.N ^ (4 * S.M₀ + S.M + 3))⁻¹ ≤ S.b γ := by
  unfold Sample.b
  have hthr := h.thr_ge
  have hK1 := h.K_ge
  have h4 : 4 * S.K ≤ S.N ^ (2 * S.M₀ + 2) := by
    have : S.N ^ (2 * S.M₀ + 2) = S.N ^ S.M₀ * S.N ^ S.M₀ * S.N ^ 2 := by
      rw [← pow_add, ← pow_add]; ring_nf
    rw [this]
    have hM0 := h.one_le_pow S.M₀
    have hK := h.K_le
    have hN2 : (4 : ℝ) ≤ S.N ^ 2 := by nlinarith [h.N_ge]
    calc 4 * S.K ≤ 4 * S.N ^ S.M₀ := by linarith
      _ ≤ S.N ^ 2 * S.N ^ S.M₀ := by nlinarith
      _ = S.N ^ 2 * S.N ^ S.M₀ * 1 := by ring
      _ ≤ S.N ^ 2 * S.N ^ S.M₀ * S.N ^ S.M₀ :=
          mul_le_mul_of_nonneg_left hM0 (by have := h.N_pos; positivity)
      _ = S.N ^ S.M₀ * S.N ^ S.M₀ * S.N ^ 2 := by ring
  have hsplit : S.N ^ (4 * S.M₀ + S.M + 3) = S.N ^ (2 * S.M₀ + S.M + 1) * S.N ^ (2 * S.M₀ + 2) := by
    rw [← pow_add]; ring_nf
  have hA := h.pow_pos' (2 * S.M₀ + S.M + 1)
  have hB := h.pow_pos' (2 * S.M₀ + 2)
  rw [hsplit, le_div_iff₀ (by linarith)]
  calc (S.N ^ (2 * S.M₀ + S.M + 1) * S.N ^ (2 * S.M₀ + 2))⁻¹ * (4 * S.K)
      ≤ (S.N ^ (2 * S.M₀ + S.M + 1) * S.N ^ (2 * S.M₀ + 2))⁻¹ * S.N ^ (2 * S.M₀ + 2) := by
        gcongr
    _ = (S.N ^ (2 * S.M₀ + S.M + 1))⁻¹ := by
        field_simp
    _ ≤ S.thr := hthr
    _ ≤ max (S.ω γ) S.thr := le_max_right _ _

theorem θ_ge (γ : Fin S.W) : (S.N ^ (3 * S.M + 2))⁻¹ ≤ S.θ γ := by
  have hδ := (delta_bounds' h.N_pos S.s0).1
  have hs : S.N ^ (-S.s0) = (S.N ^ (2 * S.M + 2))⁻¹ := by
    unfold Sample.s0
    rw [Real.rpow_neg h.N_pos.le, Real.rpow_natCast]
  have hB : (S.N ^ S.M)⁻¹ ≤ S.B γ := by
    rw [inv_le_comm₀ (h.pow_pos' _) (h.B_pos γ)]; exact h.B_inv_le γ
  have hsplit : (S.N ^ (3 * S.M + 2))⁻¹ = (S.N ^ S.M)⁻¹ * (S.N ^ (2 * S.M + 2))⁻¹ := by
    rw [← mul_inv, ← pow_add]; ring_nf
  rw [hsplit]
  unfold Sample.θ
  rw [hs] at hδ
  exact mul_le_mul hB hδ (by have := h.pow_pos' (2 * S.M + 2); positivity) (h.B_pos γ).le

/-- Worlds are separated: their planar regions are disjoint. -/
theorem o_sep {γ γ' : Fin S.W} (hne : γ ≠ γ') :
    2 * (S.a * S.K) < |S.o γ - S.o γ'| := by
  unfold Sample.a Sample.o
  have hL := h.Lam_pos
  have hK := h.K_pos
  have hd : (1 : ℝ) ≤ |((γ : ℕ) : ℝ) - ((γ' : ℕ) : ℝ)| := by
    have : (γ : ℕ) ≠ (γ' : ℕ) := fun e => hne (Fin.ext e)
    rcases lt_or_gt_of_ne this with hlt | hlt
    · have : ((γ : ℕ) : ℝ) + 1 ≤ (γ' : ℕ) := by exact_mod_cast hlt
      rw [abs_of_neg (by linarith)]; linarith
    · have : ((γ' : ℕ) : ℝ) + 1 ≤ (γ : ℕ) := by exact_mod_cast hlt
      rw [abs_of_pos (by linarith)]; linarith
  have e : 9 * S.K ^ 2 * ((γ : ℕ) : ℝ) / S.Lam - 9 * S.K ^ 2 * ((γ' : ℕ) : ℝ) / S.Lam =
      (9 * S.K ^ 2 / S.Lam) * (((γ : ℕ) : ℝ) - ((γ' : ℕ) : ℝ)) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity)]
  have : 2 * (4 * S.K / S.Lam * S.K) = 8 * S.K ^ 2 / S.Lam := by ring
  rw [this]
  calc 8 * S.K ^ 2 / S.Lam < 9 * S.K ^ 2 / S.Lam := by
        apply div_lt_div_of_pos_right _ hL; nlinarith
    _ ≤ 9 * S.K ^ 2 / S.Lam * |((γ : ℕ) : ℝ) - ((γ' : ℕ) : ℝ)| := by
        nlinarith [show (0 : ℝ) < 9 * S.K ^ 2 / S.Lam by positivity]

/-- The density factor of a retained world is exactly `Λ`. -/
theorem weight_div (γ : Fin S.W) (hγ : S.Retained γ) : S.ω γ / (S.a * S.b γ) = S.Lam := by
  have hω : 0 < S.ω γ := lt_of_lt_of_le h.thr_pos hγ
  have hmax : max (S.ω γ) S.thr = S.ω γ := max_eq_left hγ
  unfold Sample.a Sample.b
  rw [hmax]
  have hK := h.K_pos
  have hL := h.Lam_pos
  field_simp

end Hyp

end Sample

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
