import Submission.Obl.k4_narrow_projected_row_parents.Growth

namespace Submission.Obl.k4_narrow_projected_row_parents

open Filter

/-- One fixed integer power pays both the matching threshold and the comparison
mass loss. The inputs may be any subpower budgets at the later application. -/
theorem comparison_cutoff_bounds {ε U C B H R L : ℝ} (hε : 0 < ε)
    (hU : 100 ≤ U) (hC0 : 0 ≤ C) (hC : C ≤ U)
    (hB0 : 0 ≤ B) (hB : B ≤ U) (hH0 : 0 < H) (hH : H ≤ U)
    (hR0 : 0 ≤ R) (hR : R ≤ U) (hL0 : 0 ≤ L) (hL : L ≤ U)
    (n : ℕ) (hn : 1 + 1 / ε ≤ (n : ℝ)) (hnε : 6 ≤ (n : ℝ) * ε) :
    C * L ^ (1 / ε) ≤ U ^ n ∧
      C * (6 * B) * (U ^ n) ^ (-ε) * R ≤ 1 / (64 * H) := by
  have hUpos : 0 < U := by linarith
  have hU1 : 1 ≤ U := by linarith
  have hpow_eq : (U ^ n) ^ ε = U ^ ((n : ℝ) * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hUpos.le]
  constructor
  · calc C * L ^ (1 / ε) ≤ U * U ^ (1 / ε) :=
           mul_le_mul hC (Real.rpow_le_rpow hL0 hL (by positivity))
             (Real.rpow_nonneg hL0 _) hUpos.le
         _ = U ^ (1 + 1 / ε) := by rw [Real.rpow_add hUpos, Real.rpow_one]
         _ ≤ U ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hU1 hn
         _ = U ^ n := Real.rpow_natCast _ _
  · have hprod : C * B * R * H ≤ U ^ 4 := by
      calc C * B * R * H ≤ U * U * U * U := by gcongr
           _ = U ^ 4 := by ring
    have hU2 : (384 : ℝ) ≤ U ^ 2 := by nlinarith
    have hpow : 384 * C * B * R * H ≤ (U ^ n) ^ ε := by
      calc 384 * C * B * R * H = 384 * (C * B * R * H) := by ring
           _ ≤ 384 * U ^ 4 := by gcongr
           _ ≤ U ^ 2 * U ^ 4 := mul_le_mul_of_nonneg_right hU2 (pow_nonneg hUpos.le _)
           _ = U ^ 6 := by ring
           _ ≤ U ^ ((n : ℝ) * ε) := by
             rw [← Real.rpow_natCast]
             exact Real.rpow_le_rpow_of_exponent_le hU1 hnε
           _ = (U ^ n) ^ ε := hpow_eq.symm
    have hPpos : 0 < (U ^ n) ^ ε := Real.rpow_pos_of_pos (pow_pos hUpos _) _
    have hdiv : (384 * C * B * R * H) / (U ^ n) ^ ε ≤ 1 := (div_le_one hPpos).mpr hpow
    rw [le_div_iff₀ (by positivity : 0 < 64 * H), Real.rpow_neg (pow_nonneg hUpos.le _)]
    rw [div_eq_mul_inv] at hdiv
    convert hdiv using 1 <;> ring

/-- The comparison exponent can be chosen before any sequence-dependent budgets. -/
theorem exists_comparison_integer {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 1 + 1 / ε ≤ (n : ℝ) ∧ 6 ≤ (n : ℝ) * ε := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max (1 + 1 / ε) (6 / ε))
  refine ⟨n, (le_max_left _ _).trans hn, ?_⟩
  exact (div_le_iff₀ hε).mp ((le_max_right _ _).trans hn)

/-- The cutoffs consumed by the finite comparison theorem, uniformly subpower. -/
structure ComparisonBudgets (N B H R : ℕ → ℝ) (ε C : ℝ) where
  floor : ℕ → ℝ
  list : ℕ → ℝ
  discrepancy : ℕ → ℝ
  floor_pos : ∀ k, 0 < floor k
  list_one : ∀ k, 1 ≤ list k
  discrepancy_one : ∀ k, 1 ≤ discrepancy k
  floor_subpow : Model.Subpow N floor
  list_subpow : Model.Subpow N list
  discrepancy_subpow : Model.Subpow N discrepancy
  list_floor : ∀ k, 14 * B k * floor k ≤ list k
  threshold : ∀ k, C * (list k) ^ (1 / ε) ≤ discrepancy k
  error : ∀ k, R k / floor k + C * (6 * B k) * (discrepancy k) ^ (-ε) * R k ≤ 1 / (32 * H k)

/-- Every subpower reference budget admits subpower matching cutoffs which
leave all but a small fixed fraction of the retained mass floor. -/
theorem exists_comparison_budgets (N B H R : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hB : ∀ k, 1 ≤ B k) (hH : ∀ k, 1 ≤ H k)
    (hR : ∀ k, 1 ≤ R k) (hBsub : Model.Subpow N B) (hHsub : Model.Subpow N H)
    (hRsub : Model.Subpow N R) {ε C : ℝ} (hε : 0 < ε) (hC : 1 ≤ C) :
    Nonempty (ComparisonBudgets N B H R ε C) := by
  obtain ⟨n, hn, hnε⟩ := exists_comparison_integer hε
  let F : ℕ → ℝ := fun k => 64 * H k * R k
  let L : ℕ → ℝ := fun k => 14 * B k * F k
  let U : ℕ → ℝ := fun k => 100 + C + B k + H k + R k + L k
  let Λ : ℕ → ℝ := fun k => U k ^ n
  have hNp : ∀ k, 0 < N k := fun k => zero_lt_one.trans_le (hN k)
  have hB0 : ∀ k, 0 ≤ B k := fun k => zero_le_one.trans (hB k)
  have hH0 : ∀ k, 0 ≤ H k := fun k => zero_le_one.trans (hH k)
  have hR0 : ∀ k, 0 ≤ R k := fun k => zero_le_one.trans (hR k)
  have hF1 : ∀ k, 1 ≤ F k := by
    intro k
    have hHR : (1 : ℝ) * 1 ≤ H k * R k :=
      mul_le_mul (hH k) (hR k) (by norm_num) (hH0 k)
    dsimp [F]
    nlinarith
  have hL1 : ∀ k, 1 ≤ L k := by
    intro k
    have hBF : (1 : ℝ) * 1 ≤ B k * F k :=
      mul_le_mul (hB k) (hF1 k) (by norm_num) (hB0 k)
    dsimp [L]
    nlinarith
  have hUb : ∀ k, 100 ≤ U k ∧ C ≤ U k ∧ B k ≤ U k ∧ H k ≤ U k ∧ R k ≤ U k ∧ L k ≤ U k := by
    intro k
    have hb := hB k; have hh := hH k; have hr := hR k; have hl := hL1 k
    dsimp [U]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  have hc (c : ℝ) : Model.Subpow N (fun _ => c) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_const hNt c
  have hm {f g : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
      (hf : Model.Subpow N f) (hg : Model.Subpow N g) :
      Model.Subpow N (fun k => f k * g k) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNp hf0 hg0 hf hg
  have hFsub : Model.Subpow N F := hm (fun k => by positivity [hH0 k]) hR0
    (hm (fun _ => by norm_num) hH0 (hc 64) hHsub) hRsub
  have hLsub : Model.Subpow N L := hm (fun k => by positivity [hB0 k])
    (fun k => zero_le_one.trans (hF1 k))
    (hm (fun _ => by norm_num) hB0 (hc 14) hBsub) hFsub
  have hUsub : Model.Subpow N U :=
    (((((hc 100).add hNp hNt (hc C)).add hNp hNt hBsub).add hNp hNt hHsub).add hNp hNt hRsub).add hNp hNt hLsub
  have hΛsub : Model.Subpow N Λ := Submission.Obl.k4_discrete_of_terminal_charts.subpower_pow
    hN (fun k => by linarith [(hUb k).1]) hUsub n
  have hcut (k : ℕ) : C * L k ^ (1 / ε) ≤ Λ k ∧
      C * (6 * B k) * Λ k ^ (-ε) * R k ≤ 1 / (64 * H k) := by
    obtain ⟨hu, hc, hb, hh, hr, hl⟩ := hUb k
    exact comparison_cutoff_bounds hε hu (by linarith) hc (hB0 k) hb
      (by linarith [hH k]) hh (hR0 k) hr (zero_le_one.trans (hL1 k)) hl n hn hnε
  refine ⟨{
    floor := F
    list := L
    discrepancy := Λ
    floor_pos := fun k => zero_lt_one.trans_le (hF1 k)
    list_one := hL1
    discrepancy_one := fun k => one_le_pow₀ (by linarith [(hUb k).1])
    floor_subpow := hFsub
    list_subpow := hLsub
    discrepancy_subpow := hΛsub
    list_floor := fun _ => le_rfl
    threshold := fun k => (hcut k).1
    error := ?_ }⟩
  intro k
  have hHp : 0 < H k := zero_lt_one.trans_le (hH k)
  have hRp : 0 < R k := zero_lt_one.trans_le (hR k)
  have hid : R k / F k = 1 / (64 * H k) := by dsimp [F]; field_simp
  calc R k / F k + C * (6 * B k) * Λ k ^ (-ε) * R k
      ≤ 1 / (64 * H k) + 1 / (64 * H k) := by rw [hid]; exact add_le_add le_rfl (hcut k).2
    _ = 1 / (32 * H k) := by field_simp; norm_num

end Submission.Obl.k4_narrow_projected_row_parents
