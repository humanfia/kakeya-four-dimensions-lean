import Mathlib
import Submission.WZ.Seed.Kakeya
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Dyadic

open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace Submission.Lib.KakeyaCovering

open WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate (dyadic dyadic_pos dyadic_antitone)

/-- Indices of a countable ball cover whose radii lie at dyadic scale `k`. -/
def dyadicClass (ρ : ℕ → ℝ) (k : ℕ) : Set ℕ :=
  {i | dyadic (k + 1) < ρ i ∧ ρ i ≤ dyadic k}

/-- The union at one scale, before its finite index set has been extracted. -/
def dyadicCover {X : Type*} [MetricSpace X] (c : ℕ → X) (ρ : ℕ → ℝ) (k : ℕ) : Set X :=
  ⋃ i ∈ dyadicClass ρ k, ball (c i) (ρ i)

/-- Summability makes each positive-radius dyadic class finite. -/
theorem dyadicClass_finite {ρ : ℕ → ℝ} {s : ℝ} (hs : 0 < s)
    (hsum : (∑' i, ENNReal.ofReal (ρ i ^ s)) ≠ ⊤) (k : ℕ) :
    (dyadicClass ρ k).Finite := by
  have hp : ENNReal.ofReal (dyadic (k + 1) ^ s) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (dyadic_pos _) _)).ne'
  apply (ENNReal.finite_const_le_of_tsum_ne_top hsum hp).subset
  intro i hi
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow (dyadic_pos _).le hi.1.le hs.le)

/-- The radius-power budget bounds the number of balls at each dyadic scale. -/
theorem dyadicClass_card_le {ρ : ℕ → ℝ} {s : ℝ} (hs : 0 < s)
    (hsum : ∑' i, ENNReal.ofReal (ρ i ^ s) ≤ 1) (k : ℕ) :
    ∃ F : Finset ℕ, (↑F : Set ℕ) = dyadicClass ρ k ∧
      (F.card : ℝ) ≤ (2 : ℝ) ^ (((k : ℝ) + 1) * s) := by
  classical
  have hfin := dyadicClass_finite hs (ne_top_of_le_ne_top (by norm_num) hsum) k
  let F : Finset ℕ := hfin.toFinset
  have hF : (↑F : Set ℕ) = dyadicClass ρ k := Set.Finite.coe_toFinset hfin
  refine ⟨F, hF, ?_⟩
  have hbudget : ENNReal.ofReal ((F.card : ℝ) * dyadic (k + 1) ^ s) ≤ 1 := by
    calc
      ENNReal.ofReal ((F.card : ℝ) * dyadic (k + 1) ^ s) =
          ∑ i ∈ F, ENNReal.ofReal (dyadic (k + 1) ^ s) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
            simp [nsmul_eq_mul]
      _ ≤ ∑ i ∈ F, ENNReal.ofReal (ρ i ^ s) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ∈ dyadicClass ρ k := by simpa only [← hF, Finset.mem_coe] using hi
        exact ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (dyadic_pos _).le hi'.1.le hs.le)
      _ ≤ ∑' i, ENNReal.ofReal (ρ i ^ s) := ENNReal.sum_le_tsum F
      _ ≤ 1 := hsum
  have hreal : (F.card : ℝ) * dyadic (k + 1) ^ s ≤ 1 := by
    exact (ENNReal.ofReal_le_ofReal_iff zero_le_one).mp (by simpa using hbudget)
  have hinv : (dyadic (k + 1) ^ s)⁻¹ = (2 : ℝ) ^ (((k : ℝ) + 1) * s) := by
    simp only [dyadic, one_div, inv_pow]
    rw [Real.inv_rpow (by positivity), inv_inv, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [← hinv]
  simpa only [one_div] using
    (le_div_iff₀ (Real.rpow_pos_of_pos (dyadic_pos _) _)).mpr hreal

/-- Every positive radius at most one belongs to a dyadic class. -/
theorem iUnion_dyadicCover {X : Type*} [MetricSpace X] (c : ℕ → X) (ρ : ℕ → ℝ)
    (hρ : ∀ i, 0 < ρ i ∧ ρ i ≤ 1) :
    (⋃ i, ball (c i) (ρ i)) ⊆ ⋃ k, dyadicCover c ρ k := by
  intro x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  obtain ⟨k, hk⟩ := exists_nat_pow_near_of_lt_one (hρ i).1 (hρ i).2
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hk, hxi⟩⟩⟩

/-- A cover with mesh at most `2⁻ᴺ` has no balls in scales below `N`. -/
theorem dyadicCover_eq_empty_of_lt {X : Type*} [MetricSpace X]
    {c : ℕ → X} {ρ : ℕ → ℝ} {N k : ℕ} (hρ : ∀ i, ρ i ≤ dyadic N) (hk : k < N) :
    dyadicCover c ρ k = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨hik, _⟩ := mem_iUnion.mp hi
  exact (not_lt_of_ge ((hρ i).trans (dyadic_antitone (by omega)))) hik.1

/-- The time pigeonhole works for countable covers and arbitrary trajectory maps. -/
theorem exists_dyadic_time_mass {X : Type*} [MetricSpace X]
    (c : ℕ → X) (ρ : ℕ → ℝ) (hρ : ∀ i, 0 < ρ i ∧ ρ i ≤ 1)
    (f : ℝ → X) (hcover : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ ⋃ i, ball (c i) (ρ i)) :
    ∃ k : ℕ, ENNReal.ofReal (1 / (4 * ((k : ℝ) + 1) ^ 2)) ≤
      volume {t : ℝ | t ∈ Icc 0 1 ∧ f t ∈ dyadicCover c ρ k} := by
  let T : ℕ → Set ℝ := fun k => {t | t ∈ Icc 0 1 ∧ f t ∈ dyadicCover c ρ k}
  have hI : Icc (0 : ℝ) 1 ⊆ ⋃ k, T k := by
    intro t ht
    obtain ⟨k, hk⟩ := mem_iUnion.mp (iUnion_dyadicCover c ρ hρ (hcover t ht))
    exact mem_iUnion.mpr ⟨k, ht, hk⟩
  have hsum : (1 : ENNReal) ≤ ∑' k, volume (T k) := by
    simpa using (measure_mono (μ := volume) hI).trans (measure_iUnion_le T)
  obtain ⟨k, hk⟩ := WangZahlLot.Seed.Kakeya.exists_le_of_le_tsum
    (by norm_num : (1 : ENNReal) ≠ 0) (by norm_num : (1 : ENNReal) ≠ ⊤) hsum
  refine ⟨k, ?_⟩
  have heq : ENNReal.ofReal (1 / (4 * ((k : ℝ) + 1) ^ 2)) =
      (1 : ENNReal) / (4 * ((k : ENNReal) + 1) ^ 2) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  exact heq ▸ hk

end Submission.Lib.KakeyaCovering
