import Submission.Obl.k4_finite_affine_parent_sources.SourceEntropyBudget
import Submission.Obl.k4_finite_affine_parent_sources.SourceRates

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- A nominal half-window leaves ample decay after the two original errors. -/
theorem selection_window_gap {n : ℕ} {κ₁ unit T mesh δ₀ gap : ℝ}
    (hn : 2 ≤ n) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hu : 0 < unit)
    (hT : (n : ℝ) < T) (hmesh : mesh ≤ unit) (hδ : δ₀ ≤ unit)
    (hgap : selectionLookahead κ₁ T * unit / 2 - mesh ≤ gap) :
    100 * T * unit ≤ κ₁ * gap - 2 * δ₀ := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hT0 : 0 < T := by linarith
  have hκD : κ₁ * (selectionLookahead κ₁ T * unit) = 10000 * T * unit := by
    unfold selectionLookahead
    field_simp
  have hm := mul_le_mul_of_nonneg_left hmesh hκ.le
  have hκu := mul_le_mul_of_nonneg_right hκ1 hu.le
  have hg := mul_le_mul_of_nonneg_left hgap hκ.le
  have hTu := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ T by linarith) hu.le
  nlinarith

/-- Dyadic widths decay whenever the actual depth difference is large. -/
theorem delta_ratio_le_power {Nk a b unit L R : ℝ} (hNk : 1 ≤ Nk)
    (hgap : R * (unit * L) ≤ b - a) :
    δ Nk b / δ Nk a ≤ 2 * (Nk ^ (unit * L)) ^ (-R) := by
  have hNk0 : 0 < Nk := by linarith
  obtain ⟨ha, -⟩ := delta_two_sided hNk0 a
  obtain ⟨-, hb⟩ := delta_two_sided hNk0 b
  have hδa : 0 < δ Nk a := (Real.rpow_pos_of_pos hNk0 _).trans_le ha
  have heq : (Nk ^ (unit * L)) ^ (-R) = Nk ^ (-(R * (unit * L))) := by
    rw [← Real.rpow_mul hNk0.le]
    congr 1
    ring
  rw [heq, div_le_iff₀ hδa]
  calc δ Nk b ≤ 2 * Nk ^ (-b) := hb
    _ = 2 * Nk ^ (-(b - a)) * Nk ^ (-a) := by
      rw [mul_assoc, ← Real.rpow_add hNk0]
      congr 2
      ring
    _ ≤ 2 * Nk ^ (-(b - a)) * δ Nk a := by gcongr
    _ ≤ 2 * Nk ^ (-(R * (unit * L))) * δ Nk a := by
      gcongr

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The relative old dyadic time width decays in tangent units. -/
theorem time_ratio_le_power {i j : ℕ} (hi : i < m) (hj : j < m)
    (hNk : 1 ≤ Nk) (hL : 0 ≤ L) {unit R : ℝ} (hu : 0 ≤ unit) (hR : 0 ≤ R)
    (hgap : R * unit ≤ κ₁ * (sg j - sg i) - 2 * δ₀) :
    p.T i ≤ p.T j ∧
      ((2 : ℝ) ^ p.T j)⁻¹ / ((2 : ℝ) ^ p.T i)⁻¹ ≤ (Nk ^ (unit * L)) ^ (-R) := by
  have hNk0 : 0 < Nk := by linarith
  have hgap' : 2 * δ₀ ≤ κ₁ * (sg j - sg i) := by nlinarith
  obtain ⟨hT, hlo, -⟩ := level_time_increment hp hNk hL hi hj hgap'
  have hpow : (Nk ^ (unit * L)) ^ R ≤ (2 : ℝ) ^ (p.T j - p.T i) := by
    refine le_trans ?_ hlo
    rw [← Real.rpow_mul hNk0.le]
    apply Real.rpow_le_rpow_of_exponent_le hNk
    have hh := mul_le_mul_of_nonneg_right hgap hL
    nlinarith
  have heq : ((2 : ℝ) ^ p.T j)⁻¹ / ((2 : ℝ) ^ p.T i)⁻¹ =
      ((2 : ℝ) ^ (p.T j - p.T i))⁻¹ := by
    rw [pow_sub₀ _ (by norm_num) hT]
    simp [div_eq_mul_inv, mul_comm]
  refine ⟨hT, ?_⟩
  rw [heq, Real.rpow_neg (Real.rpow_pos_of_pos hNk0 _).le]
  exact inv_anti₀ (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hNk0 _) _) hpow

/-- Between each selected parent, middle and endpoint, the actual path
has both time-width and tube-thickness decay well beyond the tested range. -/
theorem source_window_scale_decay {n : ℕ} {unit T mesh : ℝ}
    (hn : 2 ≤ n) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hu : 0 < unit)
    (hT : (n : ℝ) < T) (hmesh : mesh ≤ unit) (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ unit)
    (hNk : 1 ≤ Nk) (hL : 0 ≤ L)
    (q : TangentWindows m sg (selectionLookahead κ₁ T) unit mesh) (i : ℕ) (hi : i < q.count) :
    p.T (q.level i) ≤ p.T (q.middle i) ∧
    p.T (q.middle i) ≤ p.T (q.level (i + 1)) ∧
    ((2 : ℝ) ^ p.T (q.middle i))⁻¹ / ((2 : ℝ) ^ p.T (q.level i))⁻¹ ≤
      (Nk ^ (unit * L)) ^ (-100 * T) ∧
    ((2 : ℝ) ^ p.T (q.level (i + 1)))⁻¹ / ((2 : ℝ) ^ p.T (q.middle i))⁻¹ ≤
      (Nk ^ (unit * L)) ^ (-100 * T) ∧
    ((2 : ℝ) ^ p.T (q.level (i + 1)))⁻¹ / ((2 : ℝ) ^ p.T (q.level i))⁻¹ ≤
      (Nk ^ (unit * L)) ^ (-100 * T) ∧
    δ Nk (p.r (q.middle i)) / δ Nk (p.r (q.level i)) ≤
      2 * (Nk ^ (unit * L)) ^ (-100 * T) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hT0 : 0 < T := by linarith
  have hDu0 : 0 ≤ selectionLookahead κ₁ T * unit := by
    unfold selectionLookahead
    positivity
  have hfirst : selectionLookahead κ₁ T * unit / 2 - mesh ≤
      sg (q.middle i) - sg (q.level i) := by
    linarith [(abs_le.mp (q.first_gap i hi)).1]
  have hsecond : selectionLookahead κ₁ T * unit / 2 - mesh ≤
      sg (q.level (i + 1)) - sg (q.middle i) := by
    linarith [(abs_le.mp (q.second_gap i hi)).1]
  have hfull : selectionLookahead κ₁ T * unit / 2 - mesh ≤
      sg (q.level (i + 1)) - sg (q.level i) := by
    linarith [(abs_le.mp (q.full_gap i hi)).1]
  have hg₁ := selection_window_gap hn hκ hκ1 hu hT hmesh hδ hfirst
  have hg₂ := selection_window_gap hn hκ hκ1 hu hT hmesh hδ hsecond
  have hg₃ := selection_window_gap hn hκ hκ1 hu hT hmesh hδ hfull
  obtain ⟨hT₁, hq₁⟩ := time_ratio_le_power hp (q.level_lt i) (q.middle_lt i hi)
    hNk hL hu.le (show 0 ≤ 100 * T by positivity) hg₁
  obtain ⟨hT₂, hq₂⟩ := time_ratio_le_power hp (q.middle_lt i hi) (q.level_lt (i + 1))
    hNk hL hu.le (show 0 ≤ 100 * T by positivity) hg₂
  obtain ⟨-, hq₃⟩ := time_ratio_le_power hp (q.level_lt i) (q.level_lt (i + 1))
    hNk hL hu.le (show 0 ≤ 100 * T by positivity) hg₃
  refine ⟨hT₁, hT₂, by simpa only [neg_mul] using hq₁,
    by simpa only [neg_mul] using hq₂, by simpa only [neg_mul] using hq₃, ?_⟩
  have hgap0 : 0 ≤ sg (q.middle i) - sg (q.level i) := by
    have : 0 ≤ κ₁ * (sg (q.middle i) - sg (q.level i)) := by
      nlinarith
    exact nonneg_of_mul_nonneg_right this hκ
  have hκgap := mul_le_mul_of_nonneg_right hκ1 hgap0
  have hdepth : 100 * T * (unit * L) ≤ p.r (q.middle i) - p.r (q.level i) := by
    have hlevel₁ := abs_le.mp (hp.level_bounds (q.level i) (q.level_lt i)).1
    have hlevel₂ := abs_le.mp (hp.level_bounds (q.middle i) (q.middle_lt i hi)).1
    have hg : 100 * T * unit ≤ sg (q.middle i) - sg (q.level i) - 2 * δ₀ := by
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hg hL
    nlinarith
  simpa only [neg_mul] using delta_ratio_le_power hNk hdepth

end Path

/-- The large half-window decay pays the state-mesh errors even after
one power of group distortion and four powers of the row bound. -/
theorem kept_state_mesh_budget {N T M H a q₁ q₂ : ℝ}
    (hN : 4 ≤ N) (hT : 2 ≤ T) (hM0 : 0 ≤ M) (hM : M ≤ N)
    (hH0 : 0 ≤ H) (hH : H ≤ N) (ha0 : 0 ≤ a)
    (ha : a ≤ 2 * N ^ (-100 * T))
    (hq₁0 : 0 ≤ q₁) (hq₁ : q₁ ≤ N ^ (-100 * T))
    (hq₂0 : 0 ≤ q₂) (hq₂ : q₂ ≤ N ^ (-100 * T)) :
    16 * H ^ 4 * q₂ ≤ N ^ (-T) ∧
      M * (a + 16 * H ^ 4 * q₁) + 16 * H ^ 4 * q₂ ≤ N ^ (-T) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hH4 : H ^ 4 ≤ N ^ 4 := pow_le_pow_left₀ hH0 hH 4
  have hU4 : N ^ (-100 * T) ≤ N ^ 4 * N ^ (-100 * T) := by
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hN1)
  have hU45 : N ^ 4 * N ^ (-100 * T) ≤ N ^ 5 * N ^ (-100 * T) := by
    gcongr
    norm_num
  have hcoarse : M * (a + 16 * H ^ 4 * q₁) + 16 * H ^ 4 * q₂ ≤
      34 * N ^ 5 * N ^ (-100 * T) := by
    calc M * (a + 16 * H ^ 4 * q₁) + 16 * H ^ 4 * q₂
        ≤ N * (2 * N ^ (-100 * T) + 16 * N ^ 4 * N ^ (-100 * T)) +
          16 * N ^ 4 * N ^ (-100 * T) := by gcongr
      _ ≤ N * (2 * (N ^ 4 * N ^ (-100 * T)) + 16 * N ^ 4 * N ^ (-100 * T)) +
          16 * N ^ 5 * N ^ (-100 * T) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (add_le_add (by linarith [hU4]) le_rfl) hN0.le)
              (by linarith [hU45])
      _ = _ := by ring
  have h34 : (34 : ℝ) ≤ N ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hN 3
    norm_num at hh
    linarith
  have hpower : 34 * N ^ 5 * N ^ (-100 * T) ≤ N ^ (-T) := by
    calc 34 * N ^ 5 * N ^ (-100 * T) ≤ N ^ 3 * N ^ 5 * N ^ (-100 * T) := by gcongr
      _ = N ^ ((8 : ℝ) - 100 * T) := by
        rw [← pow_add, ← Real.rpow_natCast, ← Real.rpow_add hN0]
        congr 1
        norm_num <;> ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hmain := hcoarse.trans hpower
  refine ⟨?_, hmain⟩
  have : 0 ≤ M * (a + 16 * H ^ 4 * q₁) := by positivity
  linarith

end
end Submission.Obl.k4_finite_affine_parent_sources
