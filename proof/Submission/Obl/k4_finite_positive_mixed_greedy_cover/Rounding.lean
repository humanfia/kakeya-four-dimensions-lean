import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Selection
import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Menu
import Submission.Obl.k4_quadratic_finite_greedy_cover.GainBuffer

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- A common square-cutoff budget and the fourfold geometric fit budget. -/
theorem mixed_buffers (N ρ H h L e ε : ℝ)
    (hN : 1 ≤ N) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1 / 4) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hh : H ≤ h) (hh' : h ≤ (1 + ρ) * H) (he : 0 ≤ e) (he' : e ≤ ε)
    (habsorb : 2 ≤ N ^ ε) :
    N ^ (ρ * h * L + e) ≤ N ^ (2 * ρ * H * L + 2 * e) ∧
    (N ^ (2 * ρ * H * L + 2 * e)) ^ 2 ≤ N ^ (4 * ρ * H * L + 4 * ε) ∧
    2 * N ^ (ρ * h * L + e) * N ^ (ρ * H * L) ≤ N ^ (4 * ρ * H * L + 4 * ε) ∧
    N ^ (ρ * h * L + e) * N ^ (-h * L) ≤ N ^ (4 * ρ * H * L + 4 * ε) * N ^ (-H * L) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hε : 0 ≤ ε := he.trans he'
  have hρH : 0 ≤ ρ * H := mul_nonneg hρ hH
  have hhh : h ≤ 2 * H := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hhh hρ
  have hmulL := mul_le_mul_of_nonneg_right hmul hL
  have hpos := mul_nonneg hρH hL
  refine ⟨Real.rpow_le_rpow_of_exponent_le hN (by nlinarith), ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    apply Real.rpow_le_rpow_of_exponent_le hN
    norm_num
    linarith
  · calc
      _ ≤ N ^ ε * N ^ (ρ * h * L + e) * N ^ (ρ * H * L) := by gcongr
      _ = N ^ (ε + (ρ * h * L + e) + ρ * H * L) := by rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  · rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hm := mul_le_mul_of_nonpos_left hh (by linarith : ρ - 1 ≤ 0)
    have hmL := mul_le_mul_of_nonneg_right hm hL
    nlinarith

def timeDatum {C : ℕ} (a : Piece C) :
    Submission.Obl.k4_quadratic_finite_greedy_cover.CandidateDatum C :=
  ⟨a.parent, a.gain, a.poly, a.trajectories, ∅⟩

theorem time_geometry {W C Mc : ℕ} (Nk L d₁ ρ gain e : ℝ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (H : Fin W → Set Incidence) (a : Piece C)
    (ha : PieceGood Nk L Mc d₁ ρ gain e ν B r T lev j γ u Q A H a) (ht : a.time = true) :
    Submission.Obl.k4_quadratic_finite_greedy_cover.CandidateGeometry Nk L W C Mc B ρ a.gain e
      r T lev γ j A (timeDatum a) := by
  have hc : a.poly.totalDegree ≤ 2 ∧ ∀ b, |a.poly.coeff b| ≤ Nk ^ Mc := by
    simpa only [ht, if_true] using ha.1.2.2.2.2
  refine ⟨le_rfl,ha.1.2.1,ha.1.2.2.1,hc.1,hc.2,ha.2.1,
    ha.2.2.1.trans (envelope_subset Nk L ρ e B r T lev j γ u Q A a.toTest),?_⟩
  intro l hl t hit
  have he := ha.2.2.1 hl
  simp only [envelope, ht, if_true] at he
  exact ⟨he.2.1 t hit,he.2.2.1 t hit,he.2.2.2.1 t hit⟩

/-- Every selected time piece retains its whole-block fit at the rounded gain. -/
theorem rounded_time_fit {W C Mc : ℕ} (Nk L d₁ ρ gain e ε h : ℝ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (H : Fin W → Set Incidence) (a : Piece C)
    (ha : PieceGood Nk L Mc d₁ ρ gain e ν B r T lev j γ u Q A H a) (ht : a.time = true)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1 / 4) (hh : 0 ≤ h)
    (hlo : h ≤ a.gain) (hhi : a.gain ≤ (1 + ρ) * h)
    (he : 0 ≤ e) (he' : e ≤ ε) (habsorb : 2 ≤ Nk ^ ε) (hB : 0 ≤ B (γ a.parent)) :
    ∀ l ∈ a.trajectories, Fits (Nk ^ (4 * ρ * h * L + 4 * ε))
      (δ Nk (r (lev a.parent) + h * L)) (B (γ a.parent)) a.poly l (block T lev j a.parent) := by
  apply Submission.Obl.k4_quadratic_finite_greedy_cover.rounded_candidate_upper Nk L W C Mc B ρ a.gain e
    r T lev γ j A (timeDatum a) h (ρ * h) (Nk ^ (4 * ρ * h * L + 4 * ε))
    hN hL (mul_nonneg hρ hh) hB hlo (by dsimp [timeDatum]; nlinarith)
    (mixed_buffers Nk ρ h a.gain L e ε hN hρ hρ' hh hL hlo hhi he he' habsorb).2.2.1
    (time_geometry Nk L d₁ ρ gain e ν B r T lev j γ u Q A H a ha ht)

end
end Submission.Obl.k4_finite_positive_mixed_greedy_cover
