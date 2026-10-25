import Mathlib

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

/-- The numerical requirements of the frozen comparison conclusion. -/
def ComparisonExponents (d κ ℓ U r u v m : ℝ) : Prop :=
  (0 < r ∧ 0 < v ∧ v < r ∧ 100 * (r + v) < m ∧ ℓ * r ≤ m ∧
    r + 3 * m / κ < U) ∧
  0 < u ∧ u < r ∧ v < (1 - d) * u / 4 ∧
    10000 * (1 + ℓ) * r < m ∧ (10 / (1 - d) + 4 + ℓ) * u < κ * r

/-- Every positive cap allows fixed comparison exponents and a valid wide-layer query. -/
theorem exists_comparison_exponents {d κ ℓ U L Ucap : ℝ}
    (hd : 0 ≤ d) (hd1 : d < 1) (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hU : 0 < U) (hL : 2 < L) (hcap : 0 < Ucap) :
    ∃ r u v m : ℝ, ComparisonExponents d κ ℓ U r u v m ∧ m ≤ Ucap ∧
      L * r < U ∧ L * r < m := by
  let m := min Ucap (κ * U / 12)
  have hm : 0 < m := lt_min hcap (by positivity)
  have hmcap : m ≤ Ucap := min_le_left _ _
  have hmU : m ≤ κ * U / 12 := min_le_right _ _
  let C := 10000 * (1 + ℓ) + L + 200
  have hC : 0 < C := by dsimp [C]; linarith
  let r := min (m / (2 * C)) (U / (2 * L))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrm : C * r ≤ m / 2 := by
    have := min_le_left (m / (2 * C)) (U / (2 * L))
    dsimp only [r] at this ⊢
    nlinarith [(le_div_iff₀ (by positivity : 0 < 2 * C)).mp this]
  have hrU : L * r ≤ U / 2 := by
    have := min_le_right (m / (2 * C)) (U / (2 * L))
    exact (by nlinarith [(le_div_iff₀ (by linarith : 0 < 2 * L)).mp this])
  have hroom : r + 3 * m / κ < U := by
    have : 3 * m / κ ≤ U / 4 := (div_le_iff₀ hκ).mpr (by nlinarith)
    have : r < U / 2 := by nlinarith
    linarith
  let C₁ := 10 / (1 - d) + 4 + ℓ
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  let u := min (r / 2) (κ * r / (2 * C₁))
  have hu : 0 < u := lt_min (by positivity) (by positivity)
  have hur : u < r := (min_le_left _ _).trans_lt (by linarith)
  have huκ : C₁ * u < κ * r := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * C₁)).mp
      (min_le_right (r / 2) (κ * r / (2 * C₁)))
    nlinarith [mul_pos hκ hr]
  let v := (1 - d) * u / 8
  have hv : 0 < v := by dsimp [v]; positivity
  have hvu : v < u := by dsimp [v]; nlinarith
  have hvr : v < r := hvu.trans hur
  have hvm : 100 * (r + v) < m := by
    have : 200 * r < m := by dsimp [C] at hrm; nlinarith
    nlinarith
  have hℓm : ℓ * r ≤ m := by dsimp [C] at hrm; nlinarith
  have hmr : 10000 * (1 + ℓ) * r < m := by dsimp [C] at hrm; nlinarith
  have hLm : L * r < m := by dsimp [C] at hrm; nlinarith
  refine ⟨r, u, v, m, ⟨⟨hr, hv, hvr, hvm, hℓm, hroom⟩, hu, hur, ?_, hmr, huκ⟩,
    hmcap, by linarith, hLm⟩
  dsimp [v]
  nlinarith [mul_pos (sub_pos.mpr hd1) hu]

end Submission.Obl.k4_general_wide_layer_offset_comparison
