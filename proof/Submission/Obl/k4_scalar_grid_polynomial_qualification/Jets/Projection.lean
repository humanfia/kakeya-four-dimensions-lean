import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Basic

/-!
# The projection estimate (deterministic replacement of `a04:projection-entropy`)

At a fixed time, the labelled trajectories whose tangential coordinate `y` lies within `L` of one
of at most `KY` points prescribed by the `q`-bin of their scalar `S` carry prior mass at most
`400 K⁵ KY (L + q)`.  This is the counting form of the paper's projection entropy bound: the
scalar has an upper `d`-dimensional support count (`SS`), so there are at most `≈ K q^{-d}`
occupied scalar bins, and each `q`-bin of `S` times an interval of length `L` in `y` is a
parallelogram covered by `≈ K (L/q + 1)` squares of side `q`, each of mass `≤ K q^{1+d}` (`AC`).
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

/-- **Projection estimate.** -/
theorem thin_y_mass {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} {c : Λ → Fin 5 → ℝ}
    {E : Set (Λ × ℝ)} {F : ℝ → ℝ} {piece : ℝ → Λ → Fin 5 → ℤ} {K ζ d : ℝ}
    (hSN : ScalarNormal ν c E F piece K ζ d) (hd1 : d ≤ 1) (t q L : ℝ)
    (hζq : ζ ≤ q) (hq1 : q ≤ 1) (hL : 0 ≤ L) (Y : ℤ → Finset ℝ) (KY : ℕ)
    (hY : ∀ σ, (Y σ).card ≤ KY) :
    ν {l | (l, t) ∈ E ∧ ∃ y₀ ∈ Y ⌊zS F (c l) t / q⌋, |zy (c l) t - y₀| ≤ L} ≤
      ENNReal.ofReal (400 * K ^ 5 * KY * (L + q)) := by
  classical
  have hK := hSN.one_le_K
  have hK0 : 0 ≤ K := by linarith
  have hq : 0 < q := lt_of_lt_of_le hSN.zeta_pos hζq
  by_cases hex : ∃ l₀, (l₀, t) ∈ E
  swap
  · push Not at hex
    have : {l | (l, t) ∈ E ∧ ∃ y₀ ∈ Y ⌊zS F (c l) t / q⌋, |zy (c l) t - y₀| ≤ L} = ∅ := by
      ext l; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h; exact absurd h (hex l)
    rw [this, measure_empty]; exact bot_le
  obtain ⟨l₀, hl₀⟩ := hex
  have ht : t ∈ Icc (0 : ℝ) 1 := hSN.time_mem _ hl₀
  have hFt : |F t| ≤ K := hSN.row_le _ hl₀
  set A : ℝ := 5 * K ^ 2 + 3 * K with hA
  have hA8 : 8 ≤ A := by rw [hA]; nlinarith
  have hsub : {s | ∃ l, (l, t) ∈ E ∧ zS F (c l) t = s} ⊆ Icc (-A) A := by
    rintro s ⟨l, hl, rfl⟩
    exact abs_le.mp (abs_zS_le (hSN.coeff_le _ hl) ht hFt)
  obtain ⟨B, hBcard, hBmem⟩ := occupied_bins_le (hSN.support t) hζq hq (by linarith) hsub
  -- the covering squares
  set ny : ℕ := ⌊2 * L / q⌋₊ + 1 with hny
  set nx : ℕ := ⌊2 * K⌋₊ + 2 with hnx
  let bb : ℝ → ℕ → ℝ := fun y₀ j => y₀ - L + j * q
  let aa : ℤ → ℝ → ℕ → ℝ := fun σ y₀ j => σ * q + F t * bb y₀ j - |F t| * q
  let Sq : ℤ → ℝ → ℕ → ℕ → Set Λ := fun σ y₀ j i =>
    {l | (l, t) ∈ E ∧ zx (c l) t ∈ Ico (aa σ y₀ j + i * q) (aa σ y₀ j + i * q + q) ∧
      zy (c l) t ∈ Ico (bb y₀ j) (bb y₀ j + q)}
  have hcover : {l | (l, t) ∈ E ∧ ∃ y₀ ∈ Y ⌊zS F (c l) t / q⌋, |zy (c l) t - y₀| ≤ L} ⊆
      ⋃ σ ∈ B, ⋃ y₀ ∈ Y σ, ⋃ j ∈ Finset.range ny, ⋃ i ∈ Finset.range nx, Sq σ y₀ j i := by
    rintro l ⟨hl, y₀, hy₀, hyL⟩
    set σ := ⌊zS F (c l) t / q⌋ with hσ
    have hσB : σ ∈ B := hBmem _ ⟨l, hl, rfl⟩
    set y := zy (c l) t
    set x := zx (c l) t
    set S := zS F (c l) t
    have hyb : 0 ≤ y - (y₀ - L) := by rw [abs_le] at hyL; linarith
    set j : ℕ := ⌊(y - (y₀ - L)) / q⌋₊ with hj
    have hj1 : (j : ℝ) ≤ (y - (y₀ - L)) / q := Nat.floor_le (div_nonneg hyb hq.le)
    have hj2 : (y - (y₀ - L)) / q < j + 1 := Nat.lt_floor_add_one _
    have hjy1 : bb y₀ j ≤ y := by
      have := (le_div_iff₀ hq).mp hj1
      simp only [bb]; linarith
    have hjy2 : y < bb y₀ j + q := by
      have := (div_lt_iff₀ hq).mp hj2
      simp only [bb]; nlinarith
    have hjny : j < ny := by
      have h2 : (y - (y₀ - L)) / q ≤ 2 * L / q := by
        apply div_le_div_of_nonneg_right _ hq.le
        rw [abs_le] at hyL; linarith
      have : j ≤ ⌊2 * L / q⌋₊ := Nat.floor_mono h2
      omega
    -- the scalar bin and the row
    have hS1 : (σ : ℝ) * q ≤ S := by
      have := Int.floor_le (S / q)
      calc (σ : ℝ) * q ≤ S / q * q := by gcongr
        _ = S := by field_simp
    have hS2 : S < σ * q + q := by
      have := Int.lt_floor_add_one (S / q)
      calc S = S / q * q := by field_simp
        _ < ((σ : ℝ) + 1) * q := by gcongr
        _ = σ * q + q := by ring
    have hxS : x = S + F t * y := by simp only [x, S, y, zS]; ring
    have hdy0 : 0 ≤ y - bb y₀ j := by linarith
    have hdyq : y - bb y₀ j < q := by linarith
    have hFy1 : -(|F t| * q) ≤ F t * (y - bb y₀ j) := by
      have := neg_abs_le (F t)
      have h' : |F t * (y - bb y₀ j)| ≤ |F t| * q := by
        rw [abs_mul, abs_of_nonneg hdy0]; gcongr
      linarith [neg_abs_le (F t * (y - bb y₀ j))]
    have hFy2 : F t * (y - bb y₀ j) ≤ |F t| * q := by
      have h' : |F t * (y - bb y₀ j)| ≤ |F t| * q := by
        rw [abs_mul, abs_of_nonneg hdy0]; gcongr
      linarith [le_abs_self (F t * (y - bb y₀ j))]
    have hxa0 : 0 ≤ x - aa σ y₀ j := by
      simp only [aa]; rw [hxS]; nlinarith
    have hxa1 : x - aa σ y₀ j < q * (1 + 2 * K) := by
      simp only [aa]; rw [hxS]; nlinarith
    set i : ℕ := ⌊(x - aa σ y₀ j) / q⌋₊ with hi
    have hi1 : (i : ℝ) ≤ (x - aa σ y₀ j) / q := Nat.floor_le (div_nonneg hxa0 hq.le)
    have hi2 : (x - aa σ y₀ j) / q < i + 1 := Nat.lt_floor_add_one _
    have hinx : i < nx := by
      have h1 : (x - aa σ y₀ j) / q < 1 + 2 * K := by
        rw [div_lt_iff₀ hq]; linarith
      have h2 : (i : ℝ) < 1 + 2 * K := lt_of_le_of_lt hi1 h1
      have h3 : 2 * K < ⌊2 * K⌋₊ + 1 := Nat.lt_floor_add_one _
      have h4 : (i : ℝ) < (⌊2 * K⌋₊ : ℝ) + 2 := by linarith
      have : (i : ℝ) < (nx : ℝ) := by rw [hnx]; push_cast; linarith
      exact_mod_cast this
    simp only [mem_iUnion, exists_prop, Finset.mem_range]
    refine ⟨σ, hσB, y₀, hy₀, j, hjny, i, hinx, hl, ⟨?_, ?_⟩, hjy1, hjy2⟩
    · have := (le_div_iff₀ hq).mp hi1; linarith
    · have := (div_lt_iff₀ hq).mp hi2; nlinarith
  -- measure of each square
  have hsq : ∀ σ y₀ j i, ν (Sq σ y₀ j i) ≤ ENNReal.ofReal (K * q ^ (1 + d)) := by
    intro σ y₀ j i
    have := hSN.abs_cap t (aa σ y₀ j + i * q) (bb y₀ j) q hζq hq1
    simpa only [Sq] using this
  have hsum : ν {l | (l, t) ∈ E ∧ ∃ y₀ ∈ Y ⌊zS F (c l) t / q⌋, |zy (c l) t - y₀| ≤ L} ≤
      ∑ σ ∈ B, ∑ y₀ ∈ Y σ, ∑ j ∈ Finset.range ny, ∑ i ∈ Finset.range nx,
        ENNReal.ofReal (K * q ^ (1 + d)) := by
    refine (measure_mono hcover).trans ?_
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun y₀ _ => ?_)
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact hsq σ y₀ j i
  refine hsum.trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- real arithmetic
  have hKq : 0 ≤ K * q ^ (1 + d) := by positivity
  have hYle : ∀ σ ∈ B, ((Y σ).card : ENNReal) * (ny * (nx * ENNReal.ofReal (K * q ^ (1 + d)))) ≤
      (KY : ENNReal) * (ny * (nx * ENNReal.ofReal (K * q ^ (1 + d)))) := by
    intro σ _; gcongr; exact_mod_cast hY σ
  refine (Finset.sum_le_sum hYle).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hconv : (B.card : ENNReal) * ((KY : ENNReal) * (ny * (nx * ENNReal.ofReal (K * q ^ (1 + d))))) =
      ENNReal.ofReal (B.card * (KY * (ny * (nx * (K * q ^ (1 + d)))))) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  rw [hconv]
  apply ENNReal.ofReal_le_ofReal
  -- bounds on the counts
  have hny' : (ny : ℝ) ≤ 2 * L / q + 1 := by
    rw [hny]; push_cast; linarith [Nat.floor_le (by positivity : (0:ℝ) ≤ 2 * L / q)]
  have hnx' : (nx : ℝ) ≤ 2 * K + 2 := by
    rw [hnx]; push_cast; linarith [Nat.floor_le (by positivity : (0:ℝ) ≤ 2 * K)]
  have hpow : (2 * A / q) ^ d * q ^ (1 + d) = (2 * A) ^ d * q := by
    rw [Real.div_rpow (by positivity) hq.le, Real.rpow_add hq, Real.rpow_one]
    field_simp
  have hAd : (2 * A) ^ d ≤ 2 * A := by
    calc (2 * A) ^ d ≤ (2 * A) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hd1
      _ = 2 * A := Real.rpow_one _
  have hA' : 2 * A ≤ 16 * K ^ 2 := by rw [hA]; nlinarith
  have hBc : (B.card : ℝ) ≤ 3 * (K * (2 * A / q) ^ d) := hBcard
  have hKY : (0 : ℝ) ≤ KY := Nat.cast_nonneg _
  calc (B.card : ℝ) * (KY * (ny * (nx * (K * q ^ (1 + d)))))
      ≤ 3 * (K * (2 * A / q) ^ d) * (KY * ((2 * L / q + 1) * ((2 * K + 2) * (K * q ^ (1 + d))))) := by
        gcongr
    _ = 3 * K ^ 2 * KY * (2 * K + 2) * ((2 * A / q) ^ d * q ^ (1 + d)) * ((2 * L + q) / q) := by
        field_simp
    _ = 3 * K ^ 2 * KY * (2 * K + 2) * ((2 * A) ^ d * q) * ((2 * L + q) / q) := by rw [hpow]
    _ = 3 * K ^ 2 * KY * (2 * K + 2) * (2 * A) ^ d * (2 * L + q) := by field_simp
    _ ≤ 3 * K ^ 2 * KY * (2 * K + 2) * (16 * K ^ 2) * (2 * L + q) := by
        gcongr; exact hAd.trans hA'
    _ ≤ 400 * K ^ 5 * KY * (L + q) := by
        have h1 : 2 * K + 2 ≤ 4 * K := by linarith
        have h2 : 2 * L + q ≤ 2 * (L + q) := by linarith
        calc 3 * K ^ 2 * KY * (2 * K + 2) * (16 * K ^ 2) * (2 * L + q)
            ≤ 3 * K ^ 2 * KY * (4 * K) * (16 * K ^ 2) * (2 * (L + q)) := by gcongr
          _ = 384 * K ^ 5 * KY * (L + q) := by ring
          _ ≤ 400 * K ^ 5 * KY * (L + q) := by
              have : 0 ≤ K ^ 5 * KY * (L + q) := by positivity
              nlinarith

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
