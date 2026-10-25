import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.Group

/-!
# Global scalar supports and occupied groups

* `support_global`: at a time `t`, the labeled scalars in `[-R, R]` meet at most
  `(2R + 2) K q^(-d)` cells of width `q` (cover `[-R, R]` by unit intervals).
* `scal_bound`: `|S_l(t)| ≤ 2K + 2K²` for `t ∈ [0, 1]`.
* `occupied_groups`: the `H`-bins of the base values of the trajectories labeled at `ts`
  form a finite set of size `≤ (4K + 4K² + 2) K H^(-d) (2⌈K⌉₊ + 3)`.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

variable {Ω : Type*} [MeasurableSpace Ω]

theorem scal_bound {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (h : Data ν y β γ E F d K ζ) (hK : 0 ≤ K) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (l : Ω) : |scal y β γ F l t| ≤ 2 * K + 2 * K ^ 2 := by
  have hβ := h.bound_β l
  have hγ := h.bound_γ l
  have hy0 := h.bound_y l 0
  have hy1 := h.bound_y l 1
  have hF0 := h.bound_F t 0
  have hF1 := h.bound_F t 1
  unfold scal xbar
  have h1 : |t * γ l| ≤ K := by
    rw [abs_mul]
    have : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    nlinarith [abs_nonneg t, abs_nonneg (γ l)]
  have h2 : |F t 0 * y l 0| ≤ K ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul hF0 hy0 (abs_nonneg _) hK
  have h3 : |F t 1 * y l 1| ≤ K ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul hF1 hy1 (abs_nonneg _) hK
  calc |β l + t * γ l - (F t 0 * y l 0 + F t 1 * y l 1)|
      ≤ |β l| + |t * γ l| + (|F t 0 * y l 0| + |F t 1 * y l 1|) := by
        refine (abs_sub _ _).trans ?_
        gcongr
        · exact abs_add_le _ _
        · exact abs_add_le _ _
    _ ≤ K + K + (K ^ 2 + K ^ 2) := by gcongr
    _ = 2 * K + 2 * K ^ 2 := by ring

/-- The labeled scalars in `[-R, R]` at one time meet few cells of width `q`. -/
theorem support_global {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (h : Data ν y β γ E F d K ζ) (hK : 0 ≤ K) (t : ℝ)
    {q R : ℝ} (hq : ζ ≤ q) (hq1 : q ≤ 1) (hq0 : 0 < q) (hR : 0 ≤ R) :
    ∃ C : Finset ℤ, (C.card : ℝ) ≤ (2 * R + 2) * (K * (1 / q) ^ d) ∧
      ∀ l, (l, t) ∈ E → |scal y β γ F l t| ≤ R → ⌊scal y β γ F l t / q⌋ ∈ C := by
  classical
  set n : ℕ := ⌈2 * R⌉₊ + 1 with hn
  choose C hC hmem using fun j : ℕ => h.support t q 1 (-R + j) hq hq1 le_rfl
  refine ⟨(Finset.range n).biUnion C, ?_, ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
    push_cast
    calc ∑ j ∈ Finset.range n, ((C j).card : ℝ) ≤ ∑ _j ∈ Finset.range n, K * (1 / q) ^ d :=
          Finset.sum_le_sum (fun j _ => hC j)
      _ = n * (K * (1 / q) ^ d) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (2 * R + 2) * (K * (1 / q) ^ d) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hK (Real.rpow_nonneg (by positivity) _))
          rw [hn]; push_cast
          have := Nat.ceil_lt_add_one (show 0 ≤ 2 * R by linarith)
          linarith
  · intro l hl hb
    set j : ℕ := ⌊scal y β γ F l t + R⌋₊ with hj
    have h0 : 0 ≤ scal y β γ F l t + R := by linarith [(abs_le.mp hb).1]
    have hjn : j < n := by
      rw [hn]
      have h1 : (j : ℝ) ≤ scal y β γ F l t + R := Nat.floor_le h0
      have h2 : scal y β γ F l t + R ≤ 2 * R := by linarith [(abs_le.mp hb).2]
      have h3 : (j : ℝ) ≤ ⌈2 * R⌉₊ := h1.trans (h2.trans (Nat.le_ceil _))
      exact_mod_cast Nat.lt_succ_of_le (by exact_mod_cast h3)
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjn, hmem j l hl ?_ ?_⟩
    · have := Nat.floor_le h0; linarith
    · have := Nat.lt_floor_add_one (scal y β γ F l t + R); rw [← hj] at this; linarith

/-- The occupied groups at the reading time. -/
theorem occupied_groups {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (h : Data ν y β γ E F d K ζ) (hK : 0 ≤ K)
    {t₀ ts H : ℝ} (hH : 0 < H) (hζH : ζ ≤ H) (hH1 : H ≤ 1) (hts : ts ∈ Icc (0 : ℝ) 1)
    (hts0 : ts - t₀ ∈ Icc (0 : ℝ) H) :
    ∃ Gs : Finset ℤ, (Gs.card : ℝ) ≤
        (2 * (2 * K + 2 * K ^ 2) + 2) * (K * (1 / H) ^ d) * (2 * ⌈K⌉₊ + 3) ∧
      ∀ l, (l, ts) ∈ E → ⌊baseVal y β γ F t₀ ts l / H⌋ ∈ Gs := by
  classical
  obtain ⟨C, hC, hmem⟩ := support_global h hK ts hζH hH1 hH (R := 2 * K + 2 * K ^ 2)
    (by positivity)
  set k : ℤ := ⌈K⌉₊ + 1 with hk
  refine ⟨C.biUnion (fun n => Finset.Icc (n - k) (n + k)), ?_, ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
    push_cast
    calc ∑ n ∈ C, ((Finset.Icc (n - k) (n + k)).card : ℝ)
        = ∑ _n ∈ C, (2 * (⌈K⌉₊ : ℝ) + 3) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [Int.card_Icc]
          have : n + k + 1 - (n - k) = 2 * k + 1 := by ring
          rw [this, hk]
          have : (0 : ℤ) ≤ 2 * ((⌈K⌉₊ : ℤ) + 1) + 1 := by positivity
          rw [show ((2 * ((⌈K⌉₊ : ℤ) + 1) + 1).toNat : ℝ) = (2 * ((⌈K⌉₊ : ℤ) + 1) + 1 : ℤ) from
            by exact_mod_cast Int.toNat_of_nonneg this]
          push_cast; ring
      _ = C.card * (2 * (⌈K⌉₊ : ℝ) + 3) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)
  · intro l hl
    have hsb := scal_bound h hK hts l
    have hn := hmem l hl hsb
    refine Finset.mem_biUnion.mpr ⟨_, hn, ?_⟩
    -- base value and scalar differ by `(ts - t₀) γ_l`, at most `K H`
    have hdiff : |baseVal y β γ F t₀ ts l - scal y β γ F l ts| ≤ K * H := by
      have : baseVal y β γ F t₀ ts l - scal y β γ F l ts = -((ts - t₀) * γ l) := by
        unfold baseVal scal xbar; ring
      rw [this, abs_neg, abs_mul, mul_comm]
      exact mul_le_mul (h.bound_γ l) (by rw [abs_le]; constructor <;> linarith [hts0.1, hts0.2])
        (abs_nonneg _) hK
    have a1 := Int.floor_le (scal y β γ F l ts / H)
    have a2 := Int.lt_floor_add_one (scal y β γ F l ts / H)
    have b1 := Int.floor_le (baseVal y β γ F t₀ ts l / H)
    have b2 := Int.lt_floor_add_one (baseVal y β γ F t₀ ts l / H)
    have hK' : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
    have hd : |baseVal y β γ F t₀ ts l / H - scal y β γ F l ts / H| ≤ K := by
      rw [← sub_div, abs_div, abs_of_pos hH, div_le_iff₀ hH]; linarith
    rw [Finset.mem_Icc, hk]
    constructor
    · have : (⌊scal y β γ F l ts / H⌋ : ℝ) - ((⌈K⌉₊ : ℝ) + 1) <
          (⌊baseVal y β γ F t₀ ts l / H⌋ : ℝ) + 1 := by
        linarith [(abs_le.mp hd).1]
      have : ⌊scal y β γ F l ts / H⌋ - ((⌈K⌉₊ : ℤ) + 1) < ⌊baseVal y β γ F t₀ ts l / H⌋ + 1 := by
        exact_mod_cast this
      omega
    · have : (⌊baseVal y β γ F t₀ ts l / H⌋ : ℝ) <
          (⌊scal y β γ F l ts / H⌋ : ℝ) + ((⌈K⌉₊ : ℝ) + 1) + 1 := by
        linarith [(abs_le.mp hd).2]
      have : ⌊baseVal y β γ F t₀ ts l / H⌋ < ⌊scal y β γ F l ts / H⌋ + ((⌈K⌉₊ : ℤ) + 1) + 1 := by
        exact_mod_cast this
      omega

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
