import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Filter

/-- Positive comparison exponents can be chosen after the requested depth
and loss, without changing the common structural buffer. -/
structure ComparisonExponents (δ s T : ℝ) where
  x : ℝ
  η : ℝ
  ε : ℝ
  x_pos : 0 < x
  η_pos : 0 < η
  ε_pos : 0 < ε
  ε_η : ε ≤ η
  η_x : η < x
  ε_x : ε < x
  ε_δ : ε ≤ δ
  row_gap : η + x * T < δ
  mass_gap : x * (T + 3) + ε < δ
  width_gap : η + x * T < s

theorem exists_comparison_exponents {δ s T : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (hT : 1 ≤ T) : Nonempty (ComparisonExponents δ s T) := by
  let x := min (δ / (100 * (T + 10))) (s / (100 * (T + 10)))
  have hden : 0 < 100 * (T + 10) := by positivity
  have hx : 0 < x := lt_min (div_pos hδ hden) (div_pos hs hden)
  have hxδ : x * (100 * (T + 10)) ≤ δ :=
    (le_div_iff₀ hden).mp (min_le_left _ _)
  have hxs : x * (100 * (T + 10)) ≤ s :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  refine ⟨{
    x := x
    η := x / 100
    ε := x / 10000
    x_pos := hx
    η_pos := by positivity
    ε_pos := by positivity
    ε_η := by linarith
    η_x := by linarith
    ε_x := by linarith
    ε_δ := by nlinarith
    row_gap := by nlinarith
    mass_gap := by nlinarith
    width_gap := by nlinarith }⟩

/-- Real reserve inequalities can be used directly with original incidence
mass, including a retained law whose total mass has not been normalized. -/
theorem retained_mass_of_budget {m : ENNReal} {W F L target : ℝ}
    (hF : 0 < F) (hL : 0 ≤ L) (hreserve : F * target + L ≤ W)
    (hmass : ENNReal.ofReal W ≤ ENNReal.ofReal F * m + ENNReal.ofReal L) :
    ENNReal.ofReal target ≤ m := by
  by_cases hm : m = ⊤
  · simp only [hm, le_top]
  have hreal : W ≤ F * m.toReal + L := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ F * m.toReal + L)).mp
    calc
      ENNReal.ofReal W ≤ ENNReal.ofReal F * m + ENNReal.ofReal L := hmass
      _ = ENNReal.ofReal (F * m.toReal + L) := by
        rw [ENNReal.ofReal_add (by positivity : 0 ≤ F * m.toReal) hL,
          ENNReal.ofReal_mul hF.le, ENNReal.ofReal_toReal hm]
  have ht : target ≤ m.toReal := by nlinarith
  exact (ENNReal.ofReal_le_ofReal ht).trans_eq (ENNReal.ofReal_toReal hm)

namespace ComparisonExponents

variable {δ s T : ℝ} (p : ComparisonExponents δ s T)

/-- Match thresholds, scalar rows and bad-event powers have these exact
physical scales before any inequality is used. -/
theorem scale_identities {N : ℝ} (hN : 0 < N) :
    (N ^ p.η * N ^ (-s)) / N ^ (-s) = N ^ p.η ∧
    8 * (N ^ p.η * N ^ (-s)) * (N ^ p.x) ^ T = 8 * N ^ (p.η - s + p.x * T) ∧
    (8 * (N ^ p.η * N ^ (-s)) * (N ^ p.x) ^ T) / N ^ (-s) =
      8 * N ^ (p.η + p.x * T) ∧
    (N ^ p.x) ^ (-5 : ℝ) = N ^ (-5 * p.x) := by
  have ha : N ^ (-s) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  have ht : (N ^ p.x) ^ T = N ^ (p.x * T) := (Real.rpow_mul hN.le _ _).symm
  refine ⟨by field_simp, ?_, ?_, ?_⟩
  · rw [ht]
    calc
      _ = 8 * (N ^ p.η * N ^ (-s) * N ^ (p.x * T)) := by ring
      _ = 8 * N ^ (p.η + -s + p.x * T) := by
        rw [← Real.rpow_add hN, ← Real.rpow_add hN]
      _ = _ := rfl
  · rw [ht]
    calc
      _ = 8 * (N ^ p.η * N ^ (p.x * T)) := by field_simp
      _ = _ := by rw [Real.rpow_add hN]
  · rw [← Real.rpow_mul hN.le]
    congr 1
    ring

/-- The finite numerical budgets at one original sample. -/
def Budgets (N K d : ℝ) : Prop :=
  16 * K ≤ N ^ p.x ∧
  N ^ p.ε * K + 128 * K ^ 5 ≤ N ^ p.x ∧
  28672 * K * (N ^ p.η) ^ d ≤ N ^ p.x ∧
  (100800 * K * (8 * N ^ (p.η + p.x * T)) ^ d) / N ^ (-2 * p.x) ≤
    N ^ (p.x * (T + 3)) ∧
  32 * N ^ (p.η + p.x * T) ≤ N ^ δ ∧
  16 * N ^ (p.η - s + p.x * T) ≤ 1 ∧
  N ^ (p.x * (T + 3) - δ) + N ^ (-5 * p.x) + N ^ (-p.x) ≤ N ^ (-p.ε) ∧
  6 * (811008 * K ^ 12) ≤ N ^ δ

/-- All coarse comparison losses and the fine scalar support count fit within
one requested exponent. Every use of subpower growth is on the original K. -/
theorem eventually_budgets {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ a : ℝ, 0 < a → ∀ᶠ k in atTop, K k ≤ N k ^ a)
    {d : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1) (hT : 1 ≤ T) :
    ∀ᶠ k in atTop, p.Budgets (N k) (K k) d := by
  have hx := p.x_pos
  have hη := p.η_pos
  have hε := p.ε_pos
  have hδ : 0 < δ := hε.trans_le p.ε_δ
  have hFgap : p.η + p.x * (T + 2) < p.x * (T + 3) := by nlinarith [p.η_x]
  have hbadgap : -5 * p.x < -p.ε := by linarith [p.ε_x]
  have hcutgap : -p.x < -p.ε := by linarith [p.ε_x]
  have hreservegap : p.x * (T + 3) - δ < -p.ε := by linarith [p.mass_gap]
  have hwidthgap : p.η - s + p.x * T < (0 : ℝ) := by linarith [p.width_gap]
  have hKX := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 1 (a := 0) (b := p.x) hx (A := 16) (by norm_num)
  have hW₁ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 1 p.ε_x (A := 2) (by norm_num)
  have hW₂ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 5 (a := 0) (b := p.x) hx (A := 256) (by norm_num)
  have hρ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 1 p.η_x (A := 28672) (by norm_num)
  have hF := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 1 hFgap (A := 806400) (by norm_num)
  have hrow := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (A := 32) p.row_gap
  have hwidth := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (A := 16) hwidthgap
  have hreserve := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (A := 3) hreservegap
  have hbad := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (A := 3) hbadgap
  have hcut := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (A := 3) hcutgap
  have hcount := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 12 (a := 0) (b := δ) hδ (A := 4866048) (by norm_num)
  filter_upwards [hKX, hW₁, hW₂, hρ, hF, hrow, hwidth, hreserve, hbad, hcut, hcount]
    with k hKX hW₁ hW₂ hρ hF hrow hwidth hreserve hbad hcut hcount
  have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
  have hKp : 0 < K k := zero_lt_one.trans_le (hK k)
  have hη1 : 1 ≤ N k ^ p.η := Real.one_le_rpow (hN k) hη.le
  have hm1 : 1 ≤ 8 * N k ^ (p.η + p.x * T) := by
    have hh := Real.one_le_rpow (hN k) (show 0 ≤ p.η + p.x * T by positivity)
    linarith
  have hdim (B : ℝ) (hB : 1 ≤ B) : B ^ d ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB hd1
  have hFform : (100800 * K k * (8 * N k ^ (p.η + p.x * T))) / N k ^ (-2 * p.x) =
      806400 * K k * N k ^ (p.η + p.x * (T + 2)) := by
    rw [show 100800 * K k * (8 * N k ^ (p.η + p.x * T)) =
      (806400 * K k) * N k ^ (p.η + p.x * T) by ring,
      mul_div_assoc, ← Real.rpow_sub hNp]
    congr 1
    ring
  refine ⟨?_, ?_, ?_, ?_, hrow.le, ?_, ?_, ?_⟩
  · simpa only [pow_one, Real.rpow_zero, mul_one] using hKX.le
  · simp only [pow_one, Real.rpow_zero, mul_one] at hW₁ hW₂
    nlinarith
  · exact (mul_le_mul_of_nonneg_left (hdim _ hη1) (by positivity)).trans
      (by simpa only [pow_one] using hρ.le)
  · calc
      _ ≤ (100800 * K k * (8 * N k ^ (p.η + p.x * T))) / N k ^ (-2 * p.x) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hdim _ hm1) (by positivity)) (Real.rpow_nonneg hNp.le _)
      _ = _ := hFform
      _ ≤ _ := by simpa only [pow_one] using hF.le
  · simpa only [Real.rpow_zero] using hwidth.le
  · linarith
  · rw [show 6 * (811008 * K k ^ 12) = 4866048 * K k ^ 12 by ring]
    simpa only [Real.rpow_zero, mul_one] using hcount.le

end ComparisonExponents

/-- A positive widening power absorbs the original native fit and contact
errors without any change to the original incidence measure. -/
theorem eventually_native_witness_fit {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ a : ℝ, 0 < a → ∀ᶠ k in atTop, K k ≤ N k ^ a)
    {η s e₀ : ℝ} (hη : 0 < η) (he : s < e₀) :
    ∀ᶠ k in atTop, K k * N k ^ (-s) + 16 * K k ^ 4 * N k ^ (-e₀) ≤
      N k ^ η * N k ^ (-s) := by
  have hfirst := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 1 (a := -s) (b := η - s) (by linarith) (A := 2) (by norm_num)
  have hsecond := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 4 (a := -e₀) (b := η - s) (by linarith) (A := 32) (by norm_num)
  filter_upwards [hfirst, hsecond] with k hfirst hsecond
  have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
  rw [← Real.rpow_add hNp]
  have heq : η + -s = η - s := rfl
  rw [heq]
  simp only [pow_one] at hfirst
  linarith

end Submission.Obl.k4_horizontal_strict_parameter_step
