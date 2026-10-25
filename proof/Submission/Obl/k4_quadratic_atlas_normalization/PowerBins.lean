import Mathlib

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Set

/-- A finite chain of intervals covers the interval between its endpoints. -/
theorem finite_chain_interval_cover (v : ℕ → ℝ) {m : ℕ} (hm : 0 < m)
    {x : ℝ} (hx0 : v 0 ≤ x) (hxm : x ≤ v m) :
    ∃ s ∈ Finset.range m, v s ≤ x ∧ x ≤ v (s + 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst m
      exact ⟨0, by simp, hx0, hxm⟩
    by_cases hxm' : x ≤ v m
    · obtain ⟨s, hs, hsl, hsu⟩ := ih (Nat.pos_of_ne_zero hm0) hxm'
      exact ⟨s, Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hs) (Nat.lt_succ_self _)),
        hsl, hsu⟩
    · exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self _), le_of_not_ge hxm', hxm⟩

/-- The base of a power bin in the fixed range of exponents `[-2a, 2a]`. -/
noncomputable def powerBin (N a : ℝ) (m s : ℕ) : ℝ :=
  N ^ (-2 * a + (s : ℝ) * (4 * a / (m : ℝ)))

lemma powerBin_pos {N : ℝ} (hN : 0 < N) (a : ℝ) (m s : ℕ) :
    0 < powerBin N a m s := Real.rpow_pos_of_pos hN _

lemma powerBin_zero (N a : ℝ) (m : ℕ) : powerBin N a m 0 = N ^ (-2 * a) := by
  simp [powerBin]

lemma powerBin_last (N a : ℝ) {m : ℕ} (hm : 0 < m) :
    powerBin N a m m = N ^ (2 * a) := by
  unfold powerBin
  congr 1
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp
  ring

lemma powerBin_succ {N : ℝ} (hN : 0 < N) (a : ℝ) (m s : ℕ) :
    powerBin N a m (s + 1) = powerBin N a m s * N ^ (4 * a / (m : ℝ)) := by
  unfold powerBin
  rw [← Real.rpow_add hN]
  congr 1
  push_cast
  ring

lemma powerBin_bounds {N a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a)
    {m s : ℕ} (hm : 0 < m) (hs : s ≤ m) :
    N ^ (-2 * a) ≤ powerBin N a m s ∧ powerBin N a m s ≤ N ^ (2 * a) := by
  have hstep : 0 ≤ 4 * a / (m : ℝ) := by positivity
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hmul : (s : ℝ) * (4 * a / (m : ℝ)) ≤ 4 * a := by
    have hs' : (s : ℝ) ≤ m := Nat.cast_le.mpr hs
    calc
      _ ≤ (m : ℝ) * (4 * a / (m : ℝ)) := mul_le_mul_of_nonneg_right hs' hstep
      _ = 4 * a := mul_div_cancel₀ _ hm'
  constructor
  · apply Real.rpow_le_rpow_of_exponent_le hN
    have hprod := mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) hstep
    linarith
  · apply Real.rpow_le_rpow_of_exponent_le hN
    linarith

/-- Finitely many power bins cover the entire range needed for derivative sizes. -/
theorem powerBin_cover {N a x : ℝ} (hN : 0 < N) {m : ℕ} (hm : 0 < m)
    (hx0 : N ^ (-2 * a) ≤ x) (hxm : x ≤ N ^ (2 * a)) :
    ∃ s ∈ Finset.range m,
      powerBin N a m s ≤ x ∧ x ≤ powerBin N a m s * N ^ (4 * a / (m : ℝ)) := by
  have h0 : powerBin N a m 0 ≤ x := by simpa [powerBin_zero] using hx0
  have hm' : x ≤ powerBin N a m m := by simpa [powerBin_last N a hm] using hxm
  obtain ⟨s, hs, hsl, hsu⟩ := finite_chain_interval_cover (powerBin N a m) hm h0 hm'
  rw [powerBin_succ hN] at hsu
  exact ⟨s, hs, hsl, hsu⟩

/-- The multiplicative width of the bins can have any prescribed positive exponent. -/
theorem exists_fine_power_bins (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ 0 < 4 * a / (m : ℝ) ∧ 4 * a / (m : ℝ) ≤ ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt (4 * a / ε)
  have hratio : 0 < 4 * a / ε := by positivity
  have hm0 : 0 < m := by exact_mod_cast (hratio.trans hm)
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  refine ⟨m, hm0, by positivity, ?_⟩
  apply (div_le_iff₀ hmpos).mpr
  have hmul := (div_lt_iff₀ hε).mp hm
  nlinarith

end Submission.Obl.k4_quadratic_atlas_normalization
