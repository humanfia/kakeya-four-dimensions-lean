import Submission.Obl.k4_scalar_initial_true_horizon.InitialFrostman

/-!
# The bad mass of one group, at grid scale `δ = q / 2^(kmax + s + r)`

Combines the dyadic plank caps, the planar collision estimate, the dyadic sum and the
Cauchy–Schwarz group bound.  The constant does not depend on the grid parameter `s`.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction (Coeff spatial hidden obsL)

/-- The hidden bin moves by at most `3Kb + 1` bins along a block of length `q ≤ aL`. -/
theorem xBin_window {aL q t₀ Kb : ℝ} (haL : 0 < aL) (hqa : q ≤ aL) (ht₀ : 0 ≤ t₀)
    (ht₁ : t₀ + q ≤ 1) (hKb : 0 ≤ Kb) {l : Coeff} (hl : ∀ e, |l.2 e| ≤ Kb)
    {t : ℝ} (ht : t ∈ Ico t₀ (t₀ + q)) :
    ⌊hidden l t / aL⌋ ∈ Icc (xBin aL t₀ l - (⌈3 * Kb⌉ + 1)) (xBin aL t₀ l + (⌈3 * Kb⌉ + 1)) := by
  have hdiff : |hidden l t - hidden l t₀| ≤ 3 * Kb * aL := by
    simp only [Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden]
    have heq : l.2 2 + t * l.2 3 + t ^ 2 * l.2 4 - (l.2 2 + t₀ * l.2 3 + t₀ ^ 2 * l.2 4) =
        (t - t₀) * (l.2 3 + (t + t₀) * l.2 4) := by ring
    rw [heq, abs_mul]
    have h1 : |t - t₀| ≤ aL := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have h2 : |l.2 3 + (t + t₀) * l.2 4| ≤ 3 * Kb := by
      calc |l.2 3 + (t + t₀) * l.2 4| ≤ |l.2 3| + |t + t₀| * |l.2 4| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ Kb + 2 * Kb := by
            have : |t + t₀| ≤ 2 := by
              rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
            have h4 : |t + t₀| * |l.2 4| ≤ 2 * Kb :=
              mul_le_mul this (hl 4) (abs_nonneg _) (by norm_num)
            linarith [hl 3]
        _ = 3 * Kb := by ring
    calc |t - t₀| * |l.2 3 + (t + t₀) * l.2 4| ≤ aL * (3 * Kb) :=
          mul_le_mul h1 h2 (abs_nonneg _) haL.le
      _ = 3 * Kb * aL := by ring
  have hd : |hidden l t / aL - hidden l t₀ / aL| ≤ 3 * Kb := by
    rw [← sub_div, abs_div, abs_of_pos haL, div_le_iff₀ haL]; exact hdiff
  rw [abs_le] at hd
  have hc := Int.le_ceil (3 * Kb)
  simp only [xBin, mem_Icc]
  constructor
  · have h1 : ⌊hidden l t₀ / aL - 3 * Kb⌋ ≤ ⌊hidden l t / aL⌋ := Int.floor_mono (by linarith)
    have h2 : ⌊hidden l t₀ / aL⌋ - (⌈3 * Kb⌉ + 1) ≤ ⌊hidden l t₀ / aL - 3 * Kb⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le (hidden l t₀ / aL)]
    omega
  · have h1 : ⌊hidden l t / aL⌋ ≤ ⌊hidden l t₀ / aL + 3 * Kb⌋ := Int.floor_mono (by linarith)
    have h2 : ⌊hidden l t₀ / aL + 3 * Kb⌋ ≤ ⌊hidden l t₀ / aL⌋ + (⌈3 * Kb⌉ + 1) := by
      rw [Int.floor_le_iff]; push_cast
      linarith [Int.lt_floor_add_one (hidden l t₀ / aL)]
    omega

/-- **Bad mass of one group, final form.**  The block is `[j q, j q + q)` inside `[0,1]`,
`q ≤ aL`, `2^r ≥ Kb + 1`, the grid scale is `δ = q / 2^(kmax + s + r)`, and the prior has
polynomial plank density `Rd`. -/
theorem group_bad_mass_final (ν : Measure Coeff) [IsFiniteMeasure ν] {E : Set (Coeff × ℝ)}
    (hE : MeasurableSet E) (f : (Fin 2 → ℝ) × ℤ → ℝ≥0∞) {aL : ℝ}
    (hlaw : Measure.map (obsL aL) ((ν.prod volume).restrict E) =
      (volume.prod Measure.count).withDensity f)
    {Nb Kb q Φf φ₀ c₀ Rd : ℝ} (haL : 0 < aL) (hq : 0 < q) (hqa : q ≤ aL) (hKb : 0 ≤ Kb)
    (hΦf : 0 ≤ Φf) (hφ₀ : 0 < φ₀) (hc₀ : 0 < c₀) (j : ℕ) (hj : (j : ℝ) * q + q ≤ 1)
    (m : ℤ) (kmax r s : ℕ) (hr : Kb + 1 ≤ 2 ^ r)
    (hdens : ∀ l₀ : Coeff, ∀ w : ℝ, 0 < w →
      ν {l | bddTraj Nb Kb l ∧ xBin aL (j * q) l = m ∧
        l ∈ plank (fun l : Coeff => l.2 0) (fun l => l.2 1) (j * q) q l₀ w} ≤
        ENNReal.ofReal (Rd * w ^ 2 / q))
    (hRd : Rd * (q / 2 ^ kmax) ≤ 30 * 2 ^ r * Φf / φ₀) :
    ((ν.prod volume).restrict E)
        (badLong ((ν.prod volume).restrict E) E Nb Kb aL q (j * q) Φf φ₀ m kmax ×ˢ
          Ico (j * q) (j * q + q)) ≤
      ENNReal.ofReal (4 * (8 * q * (30 * 2 ^ r * Φf / (φ₀ * q)) * 2 ^ r * (kmax + r + 3)) /
          (c₀ * φ₀ * q)) *
        ((ν.prod volume).restrict E) {p | p.2 ∈ Ico (j * q) (j * q + q) ∧
          ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - (⌈3 * Kb⌉ + 1)) (m + (⌈3 * Kb⌉ + 1))} +
      2 * ((ν.prod volume).restrict E)
        ((badLong ((ν.prod volume).restrict E) E Nb Kb aL q (j * q) Φf φ₀ m kmax ×ˢ
          Ico (j * q) (j * q + q)) ∩ obsL aL ⁻¹' lowCells ((volume.prod Measure.count).withDensity f)
            (q / 2 ^ (kmax + s + r)) c₀) := by
  set μa := (ν.prod volume).restrict E with hμa
  set t₀ : ℝ := j * q with ht₀
  set BL := badLong μa E Nb Kb aL q t₀ Φf φ₀ m kmax with hBL
  set M' : ℕ := kmax + s + r with hM'
  set δ : ℝ := q / 2 ^ M' with hδ
  set R : ℕ := 2 ^ M' with hR
  set A : ℝ := 30 * 2 ^ r * Φf / (φ₀ * q) with hA
  set C₁ : ℝ := 8 * q * A * 2 ^ r * (kmax + r + 3) with hC₁
  set ε : ℝ := (q / 2 ^ kmax) / 2 ^ s with hε
  have hδpos : 0 < δ := by positivity
  have hRδ : (R : ℝ) * δ = q := by rw [hR, hδ]; push_cast; field_simp
  have hj₀ : ((j * 2 ^ M' : ℕ) : ℤ) * δ = t₀ := by
    rw [ht₀, hδ]; push_cast; field_simp
  have hεδ : ε = 2 ^ r * δ := by
    rw [hε, hδ, hM']; rw [pow_add, pow_add]; field_simp
  have hBLm : MeasurableSet BL := measurableSet_badLong _ hE _ _ _ _ _ _ _ m kmax
  have hBLbdd : ∀ l ∈ BL, ∀ e, |l.2 e| ≤ Kb := fun l hl => hl.1.2
  have ht₀nn : 0 ≤ t₀ := by positivity
  -- the collision hypothesis
  have hcollision : ∑ i ∈ Finset.range R, ∑' i' : ℤ,
      (∫⁻ l, cellTime (fun l : Coeff => l.2 0) (fun l => l.2 1)
        (tCell (((j * 2 ^ M' : ℕ) : ℤ) * δ) δ i) (yCell δ i') l ∂(ν.restrict BL)) ^ 2 ≤
      ENNReal.ofReal δ * (ν.restrict BL) univ * ENNReal.ofReal (C₁ * δ) := by
    rw [hj₀]
    have hcoll := collision_energy_bound (ν.restrict BL) (fun l : Coeff => l.2 0)
      (fun l => l.2 1) (by fun_prop) (by fun_prop) (t₀ := t₀) (q := q) (δ := δ) (K := Kb)
      (ε := ε) hq hδpos (by positivity) (by rw [hεδ]; gcongr) (s + (kmax + r))
      (by
        rw [hε]
        have h2 : (2 : ℝ) ^ (s + (kmax + r) + 1) * (q / 2 ^ kmax / 2 ^ s) = 2 * 2 ^ r * q := by
          rw [show s + (kmax + r) + 1 = (s + kmax) + (r + 1) by omega, pow_add, pow_add]
          field_simp; ring
        rw [h2]
        have : q / 2 ^ kmax / 2 ^ s ≤ q := by
          rw [div_div]; exact div_le_self hq.le (one_le_mul_of_one_le_of_one_le
            (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)))
        nlinarith)
      ((ae_restrict_iff' hBLm).mpr (Filter.Eventually.of_forall fun l hl => hBLbdd l hl 1))
      (tCell t₀ δ) R (fun i => measurableSet_Ico) (fun i => (volume_tCell hδpos i).le)
      (fun i => tCell_diam i)
      (fun i hi => by
        have := tCell_subset (t₀ := t₀) hδpos hi
        rwa [hRδ] at this)
      (tCell_disjoint hδpos)
      (fun i => ENNReal.ofReal (A * (2 ^ (i + 1) * ε) * min 1 (2 ^ (i + 1) * ε / (q / 2 ^ kmax))))
      (fun l₀ _ i hi => badLong_dyadic_cap ν hE hq hφ₀ hΦf m kmax r s hdens hRd l₀ hi)
    refine hcoll.trans ?_
    gcongr
    have hdy := dyadic_collision_sum_le (q := q) (A := A) (w₁ := q / 2 ^ kmax) hq.le
      (by positivity) (by positivity) s (kmax + r)
    rw [show s + (kmax + r) + 1 = s + (kmax + r) + 1 from rfl]
    refine hdy.trans (le_of_eq ?_)
    congr 1
    rw [hC₁, ← hε, hεδ]
    push_cast
    ring
  -- the group bound in reals
  have hwin : ∀ l ∈ BL, ∀ t ∈ Ico ((((j * 2 ^ M' : ℕ) : ℤ) : ℝ) * δ)
      ((((j * 2 ^ M' : ℕ) : ℤ) : ℝ) * δ + R * δ),
      ⌊hidden l t / aL⌋ ∈ Icc (m - (⌈3 * Kb⌉ + 1)) (m + (⌈3 * Kb⌉ + 1)) := by
    intro l hl t ht
    rw [hj₀, hRδ] at ht
    have h := xBin_window haL hqa ht₀nn (by rw [ht₀]; exact hj) hKb (hBLbdd l hl) ht
    rwa [hl.2.1] at h
  have hbdd : ∀ l ∈ BL, ∀ t ∈ Ico ((((j * 2 ^ M' : ℕ) : ℤ) : ℝ) * δ)
      ((((j * 2 ^ M' : ℕ) : ℤ) : ℝ) * δ + R * δ), |spatial l t| ≤ 2 * Kb := by
    intro l hl t ht
    rw [hj₀, hRδ] at ht
    have ht1 : |t| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2, ht₀nn, hj]
    simp only [spatial]
    calc |l.2 0 + t * l.2 1| ≤ |l.2 0| + |t| * |l.2 1| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ Kb + 1 * Kb := by
          gcongr
          · exact hBLbdd l hl 0
          · exact hBLbdd l hl 1
      _ = 2 * Kb := by ring
  have hlong : ∀ l ∈ BL, ENNReal.ofReal (φ₀ * (R * δ)) ≤
      volume {t ∈ Ico ((((j * 2 ^ M' : ℕ) : ℤ) : ℝ) * δ)
        ((((j * 2 ^ M' : ℕ) : ℤ) : ℝ) * δ + R * δ) | (l, t) ∈ E} := by
    intro l hl
    rw [hj₀, hRδ]
    exact hl.2.2.2
  have hreal := group_bad_mass_le ν E hE f aL hlaw BL hBLm hδpos hφ₀ hc₀
    (by rw [hC₁, hA]; positivity) ((j * 2 ^ M' : ℕ) : ℤ) R (by positivity)
    (m - (⌈3 * Kb⌉ + 1)) (m + (⌈3 * Kb⌉ + 1)) hwin hbdd hlong hcollision
  rw [hj₀, hRδ] at hreal
  -- back to `ℝ≥0∞`
  have hfinBlock : ∀ S : Set (Coeff × ℝ), S ⊆ univ ×ˢ Ico t₀ (t₀ + q) → μa S ≠ ⊤ := by
    intro S hS
    refine ne_top_of_le_ne_top ?_ ((Measure.restrict_le_self _).trans (measure_mono hS))
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (by rw [Real.volume_Ico]; simp)
  have hY := hfinBlock (BL ×ˢ Ico t₀ (t₀ + q)) (prod_mono (subset_univ _) subset_rfl)
  have hM := hfinBlock {p | p.2 ∈ Ico t₀ (t₀ + q) ∧
      ⌊hidden p.1 p.2 / aL⌋ ∈ Icc (m - (⌈3 * Kb⌉ + 1)) (m + (⌈3 * Kb⌉ + 1))}
    (fun p hp => ⟨mem_univ _, hp.1⟩)
  have hZ := hfinBlock ((BL ×ˢ Ico t₀ (t₀ + q)) ∩ obsL aL ⁻¹' lowCells
      ((volume.prod Measure.count).withDensity f) δ c₀)
    (inter_subset_left.trans (prod_mono (subset_univ _) subset_rfl))
  rw [← ENNReal.ofReal_toReal hY]
  have hcoef : 4 * (8 * q * (30 * 2 ^ r * Φf / (φ₀ * q)) * 2 ^ r * (kmax + r + 3)) /
      (c₀ * φ₀ * q) = 4 * (C₁ / (c₀ * φ₀ * q)) := by rw [hC₁, hA]; ring
  rw [hcoef, ← ENNReal.ofReal_toReal hM, ← ENNReal.ofReal_toReal hZ,
    ← ENNReal.ofReal_mul (by rw [hC₁, hA]; positivity)]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by rw [hC₁, hA]; positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith [hreal]

end Submission.Obl.k4_scalar_initial_true_horizon
