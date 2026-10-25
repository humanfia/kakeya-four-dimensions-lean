import Submission.Obl.k4_scalar_candidate_original_return.Core.QuadBounds
import Submission.Obl.k4_scalar_candidate_original_return.Prepared

/-!
# Cells: Lipschitz quadratics, base cells and cell masses of fitted sets
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return.Cells

open MeasureTheory Set MvPolynomial

/-- The exact base point `(t, y(t))` of an incidence. -/
noncomputable def base (p : Inc) : Fin 2 → ℝ := ![p.2, y p.1 p.2]

/-- A filtered coefficient sum selects the unique monomial with the given exponents. -/
theorem filtered_sum_eq_coeff (P : Poly) (i j : ℕ) :
    (∑ m ∈ P.support, if m 0 = i ∧ m 1 = j then P.coeff m else 0) =
      P.coeff (Finsupp.single 0 i + Finsupp.single 1 j) := by
  classical
  set m₀ : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j with hm₀
  have key : ∀ m : Fin 2 →₀ ℕ, (m 0 = i ∧ m 1 = j) ↔ m = m₀ := by
    intro m
    constructor
    · rintro ⟨h0, h1⟩
      ext e
      fin_cases e
      · simp [hm₀, h0]
      · simp [hm₀, h1]
    · rintro rfl
      simp [hm₀]
  have hsum : (∑ m ∈ P.support, if m 0 = i ∧ m 1 = j then P.coeff m else 0) =
      ∑ m ∈ P.support, if m = m₀ then P.coeff m else 0 := by
    apply Finset.sum_congr rfl
    intro m _
    exact if_congr (key m) rfl rfl
  rw [hsum, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (MvPolynomial.notMem_support_iff.mp h).symm

/-- The normal form of a quadratic with its coefficients bounded by any common bound of
the polynomial's coefficients. -/
theorem quad_normal_form_bounded (P : Poly) (hP : P.totalDegree ≤ 2) {Bc : ℝ}
    (hc : ∀ α, |P.coeff α| ≤ Bc) :
    ∃ a b c d e f : ℝ, |a| ≤ Bc ∧ |b| ≤ Bc ∧ |c| ≤ Bc ∧ |d| ≤ Bc ∧ |e| ≤ Bc ∧ |f| ≤ Bc ∧
      ∀ z : Fin 2 → ℝ,
        eval z P = a + b * z 0 + c * z 1 + d * z 0 ^ 2 + e * z 0 * z 1 + f * z 1 ^ 2 := by
  classical
  refine ⟨∑ m ∈ P.support, if m 0 = 0 ∧ m 1 = 0 then P.coeff m else 0,
    ∑ m ∈ P.support, if m 0 = 1 ∧ m 1 = 0 then P.coeff m else 0,
    ∑ m ∈ P.support, if m 0 = 0 ∧ m 1 = 1 then P.coeff m else 0,
    ∑ m ∈ P.support, if m 0 = 2 ∧ m 1 = 0 then P.coeff m else 0,
    ∑ m ∈ P.support, if m 0 = 1 ∧ m 1 = 1 then P.coeff m else 0,
    ∑ m ∈ P.support, if m 0 = 0 ∧ m 1 = 2 then P.coeff m else 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [filtered_sum_eq_coeff]; exact hc _
  · rw [filtered_sum_eq_coeff]; exact hc _
  · rw [filtered_sum_eq_coeff]; exact hc _
  · rw [filtered_sum_eq_coeff]; exact hc _
  · rw [filtered_sum_eq_coeff]; exact hc _
  · rw [filtered_sum_eq_coeff]; exact hc _
  intro z
  rw [MvPolynomial.eval_eq']
  simp only [Fin.prod_univ_two]
  have key : ∀ m ∈ P.support, P.coeff m * (z 0 ^ m 0 * z 1 ^ m 1) =
      (if m 0 = 0 ∧ m 1 = 0 then P.coeff m else 0) +
      (if m 0 = 1 ∧ m 1 = 0 then P.coeff m else 0) * z 0 +
      (if m 0 = 0 ∧ m 1 = 1 then P.coeff m else 0) * z 1 +
      (if m 0 = 2 ∧ m 1 = 0 then P.coeff m else 0) * z 0 ^ 2 +
      (if m 0 = 1 ∧ m 1 = 1 then P.coeff m else 0) * z 0 * z 1 +
      (if m 0 = 0 ∧ m 1 = 2 then P.coeff m else 0) * z 1 ^ 2 := by
    intro m hm
    have hdeg := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hdeg
    have hs : m 0 + m 1 ≤ 2 := hdeg.trans hP
    have h0 : m 0 ≤ 2 := by omega
    have h1 : m 1 ≤ 2 := by omega
    interval_cases h : m 0 <;> interval_cases h' : m 1 <;> simp_all
    all_goals ring
  rw [Finset.sum_congr rfl key]
  simp only [Finset.sum_add_distrib, Finset.sum_mul]

/-- Coefficient-bounded quadratics are Lipschitz on bounded sets. -/
theorem quad_lipschitz (P : Poly) (hP : P.totalDegree ≤ 2) {Bc Ru : ℝ}
    (hc : ∀ α, |P.coeff α| ≤ Bc) (u u' : Fin 2 → ℝ) (hu : ∀ e, |u e| ≤ Ru)
    (hu' : ∀ e, |u' e| ≤ Ru) :
    |eval u P - eval u' P| ≤ 10 * Bc * (1 + Ru) * (|u 0 - u' 0| + |u 1 - u' 1|) := by
  obtain ⟨a, b, c, d, e, f, ha, hb, hcc, hd, he, hf, hform⟩ :=
    quad_normal_form_bounded P hP hc
  have hBc : 0 ≤ Bc := (abs_nonneg _).trans ha
  have hRu : 0 ≤ Ru := (abs_nonneg _).trans (hu 0)
  set D0 := u 0 - u' 0 with hD0
  set D1 := u 1 - u' 1 with hD1
  have hid : eval u P - eval u' P =
      b * D0 + c * D1 + d * (D0 * (u 0 + u' 0)) + e * (u 0 * D1 + u' 1 * D0) +
        f * (D1 * (u 1 + u' 1)) := by
    rw [hform u, hform u', hD0, hD1]; ring
  have hs0 : |u 0 + u' 0| ≤ 2 * Ru := by
    calc |u 0 + u' 0| ≤ |u 0| + |u' 0| := abs_add_le _ _
      _ ≤ 2 * Ru := by linarith [hu 0, hu' 0]
  have hs1 : |u 1 + u' 1| ≤ 2 * Ru := by
    calc |u 1 + u' 1| ≤ |u 1| + |u' 1| := abs_add_le _ _
      _ ≤ 2 * Ru := by linarith [hu 1, hu' 1]
  have h1 : |b * D0| ≤ Bc * |D0| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have h2 : |c * D1| ≤ Bc * |D1| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hcc (abs_nonneg _)
  have h3 : |d * (D0 * (u 0 + u' 0))| ≤ Bc * (|D0| * (2 * Ru)) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul hd (mul_le_mul_of_nonneg_left hs0 (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hBc
  have h4 : |e * (u 0 * D1 + u' 1 * D0)| ≤ Bc * (Ru * |D1| + Ru * |D0|) := by
    rw [abs_mul]
    have hin : |u 0 * D1 + u' 1 * D0| ≤ Ru * |D1| + Ru * |D0| := by
      calc |u 0 * D1 + u' 1 * D0| ≤ |u 0 * D1| + |u' 1 * D0| := abs_add_le _ _
        _ = |u 0| * |D1| + |u' 1| * |D0| := by rw [abs_mul, abs_mul]
        _ ≤ Ru * |D1| + Ru * |D0| := by
          gcongr
          · exact hu 0
          · exact hu' 1
    exact mul_le_mul he hin (abs_nonneg _) hBc
  have h5 : |f * (D1 * (u 1 + u' 1))| ≤ Bc * (|D1| * (2 * Ru)) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul hf (mul_le_mul_of_nonneg_left hs1 (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hBc
  have htri : |b * D0 + c * D1 + d * (D0 * (u 0 + u' 0)) + e * (u 0 * D1 + u' 1 * D0) +
      f * (D1 * (u 1 + u' 1))| ≤ |b * D0| + |c * D1| + |d * (D0 * (u 0 + u' 0))| +
        |e * (u 0 * D1 + u' 1 * D0)| + |f * (D1 * (u 1 + u' 1))| := by
    have := abs_add_le (b * D0 + c * D1 + d * (D0 * (u 0 + u' 0)) +
      e * (u 0 * D1 + u' 1 * D0)) (f * (D1 * (u 1 + u' 1)))
    have := abs_add_le (b * D0 + c * D1 + d * (D0 * (u 0 + u' 0)))
      (e * (u 0 * D1 + u' 1 * D0))
    have := abs_add_le (b * D0 + c * D1) (d * (D0 * (u 0 + u' 0)))
    have := abs_add_le (b * D0) (c * D1)
    linarith
  rw [hid]
  have hA0 := abs_nonneg D0
  have hA1 := abs_nonneg D1
  have hfinal : Bc * |D0| + Bc * |D1| + Bc * (|D0| * (2 * Ru)) + Bc * (Ru * |D1| + Ru * |D0|) +
      Bc * (|D1| * (2 * Ru)) ≤ 10 * Bc * (1 + Ru) * (|D0| + |D1|) := by
    nlinarith [mul_nonneg (mul_nonneg hBc (add_nonneg hA0 hA1)) (by linarith : (0 : ℝ) ≤ 9 + 7 * Ru)]
  linarith

set_option linter.unusedVariables false in
/-- The mass of a fitted set in one base cell is at most five non-concentration bounds:
on a cell the fitted hidden coordinate ranges over at most five hidden bins. -/
theorem cell_mass_le (ρ : Measure Inc) {N K d r s' δ : ℝ} (hN : 1 < N) (hδ : 0 ≤ δ)
    (hδs : δ ≤ N ^ (-s'))
    (hnc : ∀ (q : Fin 2 → ℤ) (c : ℤ), ρ {p | baseBin N r p = q ∧ hiddenBin N s' p = c} ≤
      ENNReal.ofReal (K * N ^ (-2 * r - d * s')))
    (P : Poly) (C : Set Inc) (hfit : ∀ p ∈ C, |x p.1 p.2 - eval (base p) P| ≤ δ)
    (hvar : ∀ p ∈ C, ∀ p' ∈ C, baseBin N r p = baseBin N r p' →
      |eval (base p) P - eval (base p') P| ≤ N ^ (-s'))
    (q : Fin 2 → ℤ) :
    ρ (C ∩ {p | baseBin N r p = q}) ≤ ENNReal.ofReal (5 * K * N ^ (-2 * r - d * s')) := by
  classical
  rcases (C ∩ {p | baseBin N r p = q}).eq_empty_or_nonempty with hempty | ⟨p₀, hp₀C, hp₀q⟩
  · rw [hempty, measure_empty]; exact bot_le
  set w : ℝ := N ^ (-s') with hw
  have hwpos : 0 < w := Real.rpow_pos_of_pos (by linarith) _
  set c₀ : ℤ := ⌊eval (base p₀) P / w⌋ with hc₀
  have hsub : C ∩ {p | baseBin N r p = q} ⊆
      ⋃ j ∈ Finset.Icc (c₀ - 2) (c₀ + 2), {p | baseBin N r p = q ∧ hiddenBin N s' p = j} := by
    rintro p ⟨hpC, hpq⟩
    have hpq' : baseBin N r p = q := hpq
    have hp₀q' : baseBin N r p₀ = q := hp₀q
    have hclose : |x p.1 p.2 - eval (base p₀) P| ≤ 2 * w := by
      have h1 := hfit p hpC
      have h2 := hvar p hpC p₀ hp₀C (hpq'.trans hp₀q'.symm)
      calc |x p.1 p.2 - eval (base p₀) P|
          = |(x p.1 p.2 - eval (base p) P) + (eval (base p) P - eval (base p₀) P)| := by
            ring_nf
        _ ≤ |x p.1 p.2 - eval (base p) P| + |eval (base p) P - eval (base p₀) P| :=
            abs_add_le _ _
        _ ≤ 2 * w := by linarith
    have hdiv : |x p.1 p.2 / w - eval (base p₀) P / w| ≤ 2 := by
      rw [← sub_div, abs_div, abs_of_pos hwpos, div_le_iff₀ hwpos]
      exact hclose
    have hlo : eval (base p₀) P / w - 2 ≤ x p.1 p.2 / w := by
      linarith [neg_abs_le (x p.1 p.2 / w - eval (base p₀) P / w)]
    have hhi : x p.1 p.2 / w ≤ eval (base p₀) P / w + 2 := by
      linarith [le_abs_self (x p.1 p.2 / w - eval (base p₀) P / w)]
    have hfl_lo : c₀ - 2 ≤ ⌊x p.1 p.2 / w⌋ := by
      have := Int.floor_mono hlo
      have hsub2 : ⌊eval (base p₀) P / w - 2⌋ = c₀ - 2 := by
        rw [hc₀]
        exact_mod_cast Int.floor_sub_intCast (eval (base p₀) P / w) 2
      omega
    have hfl_hi : ⌊x p.1 p.2 / w⌋ ≤ c₀ + 2 := by
      have := Int.floor_mono hhi
      have hadd2 : ⌊eval (base p₀) P / w + 2⌋ = c₀ + 2 := by
        rw [hc₀]
        exact_mod_cast Int.floor_add_intCast (eval (base p₀) P / w) 2
      omega
    refine Set.mem_biUnion (x := ⌊x p.1 p.2 / w⌋) ?_ ⟨hpq', rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hfl_lo, hfl_hi⟩)
  calc ρ (C ∩ {p | baseBin N r p = q})
      ≤ ρ (⋃ j ∈ Finset.Icc (c₀ - 2) (c₀ + 2), {p | baseBin N r p = q ∧ hiddenBin N s' p = j}) :=
        measure_mono hsub
    _ ≤ ∑ j ∈ Finset.Icc (c₀ - 2) (c₀ + 2), ρ {p | baseBin N r p = q ∧ hiddenBin N s' p = j} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.Icc (c₀ - 2) (c₀ + 2), ENNReal.ofReal (K * N ^ (-2 * r - d * s')) :=
        Finset.sum_le_sum (fun j _ => hnc q j)
    _ = ENNReal.ofReal (5 * K * N ^ (-2 * r - d * s')) := by
        rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
        have h5 : ((c₀ + 2 + 1 - (c₀ - 2)).toNat : ENNReal) = ENNReal.ofReal 5 := by
          have : (c₀ + 2 + 1 - (c₀ - 2)).toNat = 5 := by omega
          rw [this]; norm_num
        rw [h5, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5), mul_assoc]

/-- Counting charged cells: a set whose mass in each cell of a countable cover is at most
`β` charges cells whose disjoint images have total volume at least `ρ C * v / β`. -/
theorem volume_charged_cells {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (ρ : Measure α) (C : Set α) (cell : ι → Set α) (hcov : C ⊆ ⋃ q, cell q)
    (β : ENNReal) (hβ : ∀ q, ρ (C ∩ cell q) ≤ β)
    (img : ι → Set (Fin 2 → ℝ)) (himg : ∀ q, MeasurableSet (img q))
    (hdisj : Pairwise (fun q q' => Disjoint (img q) (img q')))
    (v : ENNReal) (hv : ∀ q, v ≤ volume (img q)) :
    ρ C * v ≤ β * volume (⋃ (q : ι) (_ : ρ (C ∩ cell q) ≠ 0), img q) := by
  classical
  set S : Set ι := {q | ρ (C ∩ cell q) ≠ 0} with hS
  set cnt : ENNReal := ∑' q, S.indicator (fun _ => (1 : ENNReal)) q with hcnt
  -- mass side
  have hC : ρ C ≤ β * cnt := by
    have h1 : ρ C ≤ ∑' q, ρ (C ∩ cell q) := by
      have hCU : C = ⋃ q, C ∩ cell q := by
        ext p
        constructor
        · intro hp
          obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (hcov hp)
          exact Set.mem_iUnion.mpr ⟨q, hp, hq⟩
        · intro hp
          obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hp
          exact hq.1
      calc ρ C = ρ (⋃ q, C ∩ cell q) := by rw [← hCU]
        _ ≤ ∑' q, ρ (C ∩ cell q) := measure_iUnion_le _
    have h2 : ∑' q, ρ (C ∩ cell q) ≤ ∑' q, β * S.indicator (fun _ => (1 : ENNReal)) q := by
      apply ENNReal.tsum_le_tsum
      intro q
      by_cases hq : q ∈ S
      · rw [Set.indicator_of_mem hq, mul_one]; exact hβ q
      · rw [Set.indicator_of_notMem hq, mul_zero]
        have : ρ (C ∩ cell q) = 0 := by
          by_contra h
          exact hq h
        rw [this]
    calc ρ C ≤ ∑' q, ρ (C ∩ cell q) := h1
      _ ≤ ∑' q, β * S.indicator (fun _ => (1 : ENNReal)) q := h2
      _ = β * cnt := ENNReal.tsum_mul_left
  -- volume side
  set f : ι → Set (Fin 2 → ℝ) := fun q => ⋃ (_ : ρ (C ∩ cell q) ≠ 0), img q with hf
  have hfm : ∀ q, MeasurableSet (f q) := by
    intro q
    by_cases hq : ρ (C ∩ cell q) ≠ 0
    · have : f q = img q := iSup_pos hq
      rw [this]; exact himg q
    · have : f q = ∅ := iSup_neg hq
      rw [this]; exact MeasurableSet.empty
  have hfsub : ∀ q, f q ⊆ img q := by
    intro q
    exact Set.iUnion_subset (fun _ => subset_rfl)
  have hfd : Pairwise (fun q q' => Disjoint (f q) (f q')) := by
    intro q q' hqq'
    exact (hdisj hqq').mono (hfsub q) (hfsub q')
  have hvol : volume (⋃ q, f q) = ∑' q, volume (f q) := measure_iUnion hfd hfm
  have hge : v * cnt ≤ volume (⋃ q, f q) := by
    rw [hvol, hcnt, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro q
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq, mul_one]
      have : f q = img q := by
        have hq' : ρ (C ∩ cell q) ≠ 0 := hq
        exact iSup_pos hq'
      rw [this]; exact hv q
    · rw [Set.indicator_of_notMem hq, mul_zero]; exact bot_le
  calc ρ C * v ≤ (β * cnt) * v := by gcongr
    _ = β * (v * cnt) := by ring
    _ ≤ β * volume (⋃ q, f q) := by gcongr

end Submission.Obl.k4_scalar_candidate_original_return.Cells
