-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGCovering.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.CoveringStability

/-!
# More stability of the one-dimensional covering condition

* finite unions add the constants;
* a covering condition at a coarse scale `d'` gives one at a finer scale `d` with the
  constant multiplied by `2 d' / d`.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric

/-- Covering of a finite union. -/
theorem Covering.biUnion {ι : Type*} {d α C : ℝ} (s : Finset ι) {B : ι → Set ℝ}
    (h : ∀ i ∈ s, Covering d α C (B i)) (hd : 0 < d) (hC : 0 ≤ C) :
    Covering d α (s.card * C) (⋃ i ∈ s, B i) := by
  classical
  intro r R a hdr hrR
  have hr : 0 < r := hd.trans_le hdr
  choose! m c hc hm using fun i hi => h i hi r R a hdr hrR
  -- concatenate the covers
  let N : ℕ := ∑ i ∈ s, m i
  have hcover : ∀ i ∈ s, ∀ x ∈ B i ∩ Icc a (a + R), ∃ j : Fin (m i), x ∈ closedBall (c i j) r :=
    fun i hi x hx => mem_iUnion.mp (hc i hi hx)
  -- index the union of the covers by a sigma type
  let T : Finset (Σ i : ι, Fin (m i)) := s.sigma fun i => Finset.univ
  have hTcard : T.card = N := by
    simp [T, N, Finset.card_sigma]
  let e : Fin T.card ≃ T := T.equivFin.symm
  refine ⟨T.card, fun k => c (e k).1.1 (e k).1.2, ?_, ?_⟩
  · rintro x ⟨hx, hxI⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    obtain ⟨j, hj⟩ := hcover i hi x ⟨hxi, hxI⟩
    have hmem : (⟨i, j⟩ : Σ i : ι, Fin (m i)) ∈ T := Finset.mem_sigma.mpr ⟨hi, Finset.mem_univ _⟩
    refine mem_iUnion.mpr ⟨e.symm ⟨⟨i, j⟩, hmem⟩, ?_⟩
    have he : e (e.symm ⟨⟨i, j⟩, hmem⟩) = ⟨⟨i, j⟩, hmem⟩ := Equiv.apply_symm_apply e _
    show x ∈ closedBall (c (e (e.symm ⟨⟨i, j⟩, hmem⟩)).1.1 (e (e.symm ⟨⟨i, j⟩, hmem⟩)).1.2) r
    rw [he]
    exact hj
  · rw [hTcard]
    have hpow : 0 ≤ (R / r) ^ α := Real.rpow_nonneg (div_nonneg (hr.le.trans hrR) hr.le) _
    calc (N : ℝ) = ∑ i ∈ s, (m i : ℝ) := by simp [N]
      _ ≤ ∑ i ∈ s, C * (R / r) ^ α := Finset.sum_le_sum fun i hi => hm i hi
      _ = s.card * C * (R / r) ^ α := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- A covering condition at a coarse scale gives one at a finer scale. -/
theorem Covering.refine_scale {d d' α C : ℝ} {B : Set ℝ} (h : Covering d' α C B)
    (hd : 0 < d) (hdd : d ≤ d') (hα : 0 ≤ α) (_hα1 : α ≤ 1) (hC : 0 ≤ C) :
    Covering d α (2 * C * (d' / d)) B := by
  intro r R a hdr hrR
  have hr : 0 < r := hd.trans_le hdr
  rcases le_or_gt d' r with hd'r | hrd'
  · -- the coarse condition already applies
    obtain ⟨m, c, hc, hm⟩ := h r R a hd'r hrR
    refine ⟨m, c, hc, hm.trans ?_⟩
    have h1 : 1 ≤ d' / d := by rw [le_div_iff₀ hd]; linarith
    have hpow : 0 ≤ C * (R / r) ^ α :=
      mul_nonneg hC (Real.rpow_nonneg (div_nonneg (hr.le.trans hrR) hr.le) _)
    nlinarith
  · -- cover at scale `d'`, then split each ball
    have hd'0 : 0 < d' := hd.trans_le hdd
    set R' := max R d' with hR'
    obtain ⟨m, c, hc, hm⟩ := h d' R' a le_rfl (le_max_right _ _)
    -- each ball of radius `d'` is covered by `K` balls of radius `r`
    set K : ℕ := ⌈d' / r⌉₊ with hK
    have hKr : d' ≤ K * r := by
      have := Nat.le_ceil (d' / r)
      rw [div_le_iff₀ hr] at this
      exact this
    refine ⟨m * K, fun k => c (finProdFinEquiv.symm k).1 - d' +
        (2 * ((finProdFinEquiv.symm k).2 : ℝ) + 1) * r, ?_, ?_⟩
    · rintro x ⟨hx, hxlo, hxhi⟩
      have hxI : x ∈ B ∩ Icc a (a + R') :=
        ⟨hx, hxlo, hxhi.trans (by linarith [le_max_left R d'])⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hc hxI)
      rw [mem_closedBall, Real.dist_eq, abs_le] at hj
      -- the position of `x` in the ball of radius `d'`
      set t : ℝ := (x - (c j - d')) / (2 * r) with ht
      have ht0 : 0 ≤ t := div_nonneg (by linarith) (by positivity)
      set l : ℕ := min ⌊t⌋₊ (K - 1) with hl
      have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (by
        intro h0; rw [h0] at hKr; simp at hKr; linarith)
      have hlK : l < K := by
        have : l ≤ K - 1 := min_le_right _ _
        omega
      refine mem_iUnion.mpr ⟨finProdFinEquiv (j, ⟨l, hlK⟩), ?_⟩
      simp only [Equiv.symm_apply_apply]
      rw [mem_closedBall, Real.dist_eq, abs_le]
      have hfl := Nat.floor_le ht0
      have hfl2 := Nat.lt_floor_add_one t
      rcases le_or_gt ⌊t⌋₊ (K - 1) with hle | hgt
      · have hl' : (l : ℝ) = ⌊t⌋₊ := by rw [hl, min_eq_left hle]
        rw [hl']
        have e1 : x - (c j - d') = 2 * r * t := by rw [ht]; field_simp
        constructor <;> nlinarith
      · have hl' : (l : ℝ) = (K - 1 : ℕ) := by rw [hl, min_eq_right hgt.le]
        rw [hl']
        have hKc : ((K - 1 : ℕ) : ℝ) = K - 1 := by
          rw [Nat.cast_sub hK1]; simp
        rw [hKc]
        have e1 : x - (c j - d') = 2 * r * t := by rw [ht]; field_simp
        have ht2 : ((K - 1 : ℕ) : ℝ) ≤ t := by
          have : (K - 1 : ℕ) + 1 ≤ ⌊t⌋₊ := hgt
          have h2 : ((K - 1 : ℕ) : ℝ) + 1 ≤ ⌊t⌋₊ := by exact_mod_cast this
          linarith
        rw [hKc] at ht2
        constructor
        · nlinarith
        · nlinarith
    · -- counting
      have hKle : (K : ℝ) ≤ 2 * (d' / r) := by
        have h1 : (K : ℝ) < d' / r + 1 := Nat.ceil_lt_add_one (by positivity)
        have h2 : 1 ≤ d' / r := by rw [le_div_iff₀ hr]; linarith
        linarith
      have hRr : 1 ≤ R / r := by rw [le_div_iff₀ hr]; linarith
      have hpowR : 1 ≤ (R / r) ^ α := Real.one_le_rpow hRr hα
      push_cast
      rcases le_or_gt R d' with hRd' | hRd'
      · -- `R' = d'`
        have hR'e : R' = d' := max_eq_right hRd'
        rw [hR'e, div_self hd'0.ne', Real.one_rpow, mul_one] at hm
        have hd'r : d' / r ≤ d' / d := div_le_div_of_nonneg_left hd'0.le hd hdr
        calc (m : ℝ) * K ≤ C * (2 * (d' / r)) :=
              mul_le_mul hm hKle (Nat.cast_nonneg _) hC
          _ ≤ C * (2 * (d' / d)) := by gcongr
          _ = 2 * C * (d' / d) * 1 := by ring
          _ ≤ 2 * C * (d' / d) * (R / r) ^ α := by
              apply mul_le_mul_of_nonneg_left hpowR; positivity
      · -- `R' = R`
        have hR'e : R' = R := max_eq_left hRd'.le
        rw [hR'e] at hm
        have hsplit : (R / d') ^ α * (d' / r) = (R / r) ^ α * (d' / r) ^ (1 - α) := by
          have h1 : R / d' = (R / r) * (d' / r)⁻¹ := by field_simp
          rw [h1, Real.mul_rpow (by positivity) (by positivity),
            Real.inv_rpow (by positivity)]
          rw [Real.rpow_sub (by positivity), Real.rpow_one]
          field_simp
        have hd'r1 : 1 ≤ d' / r := by rw [le_div_iff₀ hr]; linarith
        have hpow1 : (d' / r) ^ (1 - α) ≤ d' / r := by
          calc (d' / r) ^ (1 - α) ≤ (d' / r) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hd'r1 (by linarith)
            _ = d' / r := Real.rpow_one _
        have hd'r : d' / r ≤ d' / d := div_le_div_of_nonneg_left hd'0.le hd hdr
        calc (m : ℝ) * K ≤ C * (R / d') ^ α * (2 * (d' / r)) :=
              mul_le_mul hm hKle (Nat.cast_nonneg _)
                (mul_nonneg hC (Real.rpow_nonneg (div_nonneg (by linarith) hd'0.le) _))
          _ = 2 * C * ((R / r) ^ α * (d' / r) ^ (1 - α)) := by rw [← hsplit]; ring
          _ ≤ 2 * C * ((R / r) ^ α * (d' / d)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left (hpow1.trans hd'r) (by positivity)
          _ = 2 * C * (d' / d) * (R / r) ^ α := by ring

/-- Covering is preserved by positive affine maps, with the scale multiplied. -/
theorem Covering.affine {d α C : ℝ} {B : Set ℝ} (h : Covering d α C B) {l : ℝ} (hl : 0 < l)
    (κ : ℝ) : Covering (l * d) α C ((fun u => l * u + κ) '' B) := by
  intro r R a hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h (r / l) (R / l) ((a - κ) / l)
    (by rw [le_div_iff₀ hl]; linarith) (div_le_div_of_nonneg_right hrR hl.le)
  refine ⟨m, fun j => l * c j + κ, ?_, ?_⟩
  · rintro _ ⟨⟨u, hu, rfl⟩, hlo, hhi⟩
    have huI : u ∈ Icc ((a - κ) / l) ((a - κ) / l + R / l) := by
      constructor
      · rw [div_le_iff₀ hl]; linarith
      · rw [← add_div, le_div_iff₀ hl]; linarith
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc ⟨hu, huI⟩)
    refine mem_iUnion.mpr ⟨j, ?_⟩
    rw [mem_closedBall, Real.dist_eq] at hj ⊢
    have : l * u + κ - (l * c j + κ) = l * (u - c j) := by ring
    rw [this, abs_mul, abs_of_pos hl]
    calc l * |u - c j| ≤ l * (r / l) := mul_le_mul_of_nonneg_left hj hl.le
      _ = r := by field_simp
  · have : R / l / (r / l) = R / r := by field_simp
    rwa [this] at hm

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
