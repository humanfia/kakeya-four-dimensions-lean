import Submission.Obl.k4_scalar_grid_cartesian_field.DataFacts

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter

/-- Put the exact frozen joint cap on the original three-coordinate physical cube. -/
theorem original_physical_palette_cap (data : Data) (k : ℕ) (g : Fin (data.W k))
    {B r : ℝ} (hN : 0 < data.N k)
    (hcap : ∀ (q : Fin 2 → ℤ) (a c : ℤ), data.ρ k g
      {p | z data (data.N k) B p = q ∧
        (⌊x data p.1 p.2 / data.N k ^ (-B)⌋ : ℤ) = a ∧ p.1.2 1 ∈ vel data k r c} ≤
      ENNReal.ofReal (data.K k * data.N k ^ (-2 * B - data.d * B)) * data.π k g (vel data k r c)) :
    ∀ (q : Fin 3 → ℤ) (c : ℤ), data.ρ k g
      {p | physCube (data.N k) B p = q ∧ p.1.2 1 ∈ vel data k r c} ≤
      ENNReal.ofReal (data.K k * (data.N k ^ (-B)) ^ (2 + data.d)) * data.π k g (vel data k r c) := by
  intro q c
  have hweight : data.N k ^ (-2 * B - data.d * B) = (data.N k ^ (-B)) ^ (2 + data.d) := by
    rw [← Real.rpow_mul hN.le]
    congr 1
    ring
  apply (measure_mono (t := {p | z data (data.N k) B p = ![q 0, q 1] ∧
    (⌊x data p.1 p.2 / data.N k ^ (-B)⌋ : ℤ) = q 2 ∧ p.1.2 1 ∈ vel data k r c}) ?_).trans
    (by simpa only [hweight] using hcap ![q 0, q 1] (q 2) c)
  intro p hp
  refine ⟨?_, ?_, hp.2⟩
  · funext e
    fin_cases e
    · simpa [z, physCube, y_eq_scalarY] using congrFun hp.1 0
    · simpa [z, physCube, y_eq_scalarY] using congrFun hp.1 1
  · simpa [physCube, x_eq_scalarX] using congrFun hp.1 2

/-- Original fine-cube palette numerators hold uniformly at every requested compact angular range. -/
theorem original_physical_palette_compact (data : Data) (hs : scaleHyp data) (hcap : capHyp data)
    {B : ℝ} (hB : 1 ≤ B) (R : ℝ) (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ (g : Fin (data.W k)) (r : ℝ), R⁻¹ ≤ r → r ≤ R →
      ∀ (q : Fin 3 → ℤ) (c : ℤ), data.ρ k g
        {p | physCube (data.N k) B p = q ∧ p.1.2 1 ∈ vel data k r c} ≤
        ENNReal.ofReal (data.K k * (data.N k ^ (-B)) ^ (2 + data.d)) * data.π k g (vel data k r c) := by
  let R' := max R (B + 1)
  have hR' : 1 < R' := hR.trans_le (le_max_left _ _)
  have hBB : B ≤ R' := (show B ≤ B + 1 by linarith).trans (le_max_right _ _)
  have hinv : R'⁻¹ ≤ R⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by linarith : 0 < R) (le_max_left R (B + 1))
  have hinvB : R'⁻¹ ≤ B := (inv_le_one_of_one_le₀ hR'.le).trans hB
  filter_upwards [hcap R' hR'] with k hk
  intro g r hr₀ hr₁
  apply original_physical_palette_cap data k g (by linarith [hs.1 k])
  exact (hk g B B r hinvB hBB hinvB hBB (hinv.trans hr₀) (hr₁.trans (le_max_left _ _))).2.2

/-- The same original physical cap can be included in a slowly varying angular mesh diagonal. -/
theorem original_physical_palette_fixed (data : Data) (hs : scaleHyp data) (hcap : capHyp data)
    {B b : ℝ} (hB : 1 ≤ B) (hb : 0 < b) :
    ∀ᶠ k in atTop, ∀ (g : Fin (data.W k)) (q : Fin 3 → ℤ) (c : ℤ), data.ρ k g
      {p | physCube (data.N k) B p = q ∧ p.1.2 1 ∈ vel data k b c} ≤
      ENNReal.ofReal (data.K k * (data.N k ^ (-B)) ^ (2 + data.d)) * data.π k g (vel data k b c) := by
  let R := max 2 (max (2 / b) b)
  have hR : 1 < R := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
  have hRb : 2 / b ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hbR : b ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hRinv : R⁻¹ ≤ b := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < R)]
    have h := (div_le_iff₀ hb).mp hRb
    nlinarith
  filter_upwards [original_physical_palette_compact data hs hcap hB R hR] with k hk
  exact fun g => hk g b hRinv hbR

end Submission.Obl.k4_scalar_grid_cartesian_field
