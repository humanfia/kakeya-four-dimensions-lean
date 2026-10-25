import Submission.Obl.k4_scalar_marked_coefficient_smoothing.RawDensity
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.AnalyticClaims

/-!
# The density transfer

`densityTransferClaim : DensityTransferClaim`: the pure, joint and angular density ceilings of
the marked law hold with the loss `30000 K⁴`, for any valid rounding and marking data.
-/

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw

open MeasureTheory Set
open scoped ENNReal

theorem cardP_le {K : ℝ} (hK : 1 ≤ K) :
    (((3 * ((2 * (⌈K⌉₊ + 5) + 1) * (2 * (3 * ⌈K⌉₊ + 9) + 1))) : ℕ) : ℝ) ≤ 1395 * K ^ 2 := by
  have hL : (⌈K⌉₊ : ℝ) < K + 1 := Nat.ceil_lt_add_one (by linarith)
  have hL0 : (0 : ℝ) ≤ ⌈K⌉₊ := Nat.cast_nonneg _
  have h1 : 2 * ((⌈K⌉₊ : ℝ) + 5) + 1 ≤ 15 * K := by linarith
  have h2 : 2 * (3 * (⌈K⌉₊ : ℝ) + 9) + 1 ≤ 31 * K := by linarith
  push_cast
  calc 3 * ((2 * ((⌈K⌉₊ : ℝ) + 5) + 1) * (2 * (3 * (⌈K⌉₊ : ℝ) + 9) + 1))
      ≤ 3 * ((15 * K) * (31 * K)) := by gcongr
    _ = 1395 * K ^ 2 := by ring

theorem cardA_le {K : ℝ} (hK : 1 ≤ K) :
    (((3 * ((2 * (⌈K⌉₊ + 5) + 1) * ((2 * (3 * ⌈K⌉₊ + 9) + 1) * (2 * 2 + 1)))) : ℕ) : ℝ) ≤
      6975 * K ^ 2 := by
  have hL : (⌈K⌉₊ : ℝ) < K + 1 := Nat.ceil_lt_add_one (by linarith)
  have hL0 : (0 : ℝ) ≤ ⌈K⌉₊ := Nat.cast_nonneg _
  have h1 : 2 * ((⌈K⌉₊ : ℝ) + 5) + 1 ≤ 15 * K := by linarith
  have h2 : 2 * (3 * (⌈K⌉₊ : ℝ) + 9) + 1 ≤ 31 * K := by linarith
  push_cast
  calc _ ≤ 3 * ((15 * K) * ((31 * K) * 5)) := by gcongr
    _ = 6975 * K ^ 2 := by ring

theorem ofReal_prod5 {a b c e : ℝ} {n : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ENNReal.ofReal a * ENNReal.ofReal b * (ENNReal.ofReal c * (n : ℝ≥0∞) * ENNReal.ofReal e) =
      ENNReal.ofReal (a * b * (c * n * e)) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ha,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc, ENNReal.ofReal_natCast]

/-- The numerical comparison behind all three ceilings. -/
theorem ceiling_arith {σ J K c P κr n B : ℝ} (hσ : 0 < σ) (hJσ : (J : ℝ) * σ ≤ 2)
    (_hJ : 0 ≤ J) (hK : 1 ≤ K) (hc : 0 < c) (hP : 0 ≤ P) (hκ : 0 ≤ κr) (hn : 0 ≤ n)
    (hnB : n ≤ B * K ^ 2) (hB : 4 * B ≤ 30000) :
    σ⁻¹ * κr * (J * (2 * K) * n * (K * σ ^ 2 * c * P)) ≤ 30000 * K ^ 4 * c * P * κr := by
  have e : σ⁻¹ * κr * (J * (2 * K) * n * (K * σ ^ 2 * c * P)) =
      (J * σ) * n * (2 * K ^ 2 * c * P * κr) := by
    field_simp
  rw [e]
  have h1 : (J * σ) * n ≤ 2 * (B * K ^ 2) := mul_le_mul hJσ hnB hn (by norm_num)
  have h2 : 0 ≤ 2 * K ^ 2 * c * P * κr := by positivity
  have hK4 : 0 ≤ K ^ 4 * c * P * κr := by positivity
  calc (J * σ) * n * (2 * K ^ 2 * c * P * κr) ≤ 2 * (B * K ^ 2) * (2 * K ^ 2 * c * P * κr) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = (4 * B) * (K ^ 4 * c * P * κr) := by ring
    _ ≤ 30000 * (K ^ 4 * c * P * κr) := mul_le_mul_of_nonneg_right hB hK4
    _ = 30000 * K ^ 4 * c * P * κr := by ring

/-- The density of a dominated measure, bounded by a real ceiling. -/
theorem density_of_le {X : Type*} [MeasurableSpace X] {ν : Measure X} [SigmaFinite ν]
    {lam : Measure X} {C : ℝ≥0∞} {x : ℝ} (h : lam ≤ C • ν) (hC : C ≤ ENNReal.ofReal x) :
    ∃ g : X → ℝ≥0∞, Measurable g ∧ lam = ν.withDensity g ∧ ∀ᵐ z ∂ν, g z ≤ ENNReal.ofReal x := by
  obtain ⟨hg, heq, hle⟩ := exists_density_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hC) h
  refine ⟨lam.rnDeriv ν, hg, heq, ?_⟩
  filter_upwards [hle] with z hz
  exact hz.trans hC

/-- **The density transfer.** -/
theorem densityTransferClaim : DensityTransferClaim := by
  refine ⟨30000, by norm_num, 4, ?_⟩
  intro N K d s m S U c hN hK hd hd1 hs hsm hS hU hUm hc α _ ν μ b angular hinput
    H J tag b₀ w mark hJ hJlow hJhigh hw hsum hb₀ hcoup
  obtain ⟨htag, hweight, hround, hfloor⟩ := hcoup
  rcases hinput with ⟨hb, hprob, hdom, htimes, hmass, hbound, hcap,
    ⟨F, hFbudget, hFsupport⟩, hangular⟩
  have := sigmaFinite_baseRef
  have := sigmaFinite_jointRef
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hm : 0 < m := hs.trans hsm
  have hσ : 0 < N ^ (-m) := Real.rpow_pos_of_pos hNp _
  have hσ1 : N ^ (-m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hδσ : N ^ (-10 * (m + s + 1)) ≤ N ^ (-m) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
  have hK₁ : (0 : ℝ) < 2 * K := by linarith
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hρσ : ∀ r : ℝ, r ≤ s → N ^ (-m) ≤ N ^ (-r) := fun r hr =>
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hρpos : ∀ r : ℝ, 0 < N ^ (-r) := fun r => Real.rpow_pos_of_pos hNp _
  have hρd : ∀ r : ℝ, (N ^ (-r)) ^ d = N ^ (-d * r) := fun r => by
    rw [← Real.rpow_mul hNp.le]; congr 1; ring
  have hmin : ∀ u : ℝ, N ^ (-u) / N ^ (-m) = N ^ (m - u) := fun u => by
    rw [← Real.rpow_sub hNp]; congr 1; ring
  -- the pure weight bound
  have hWpure : ∀ r : ℝ, 0 ≤ r → r ≤ s → ∀ (i : ℤ) (Ksl : Set ℝ) (q : ℝ × ℝ),
      ∑ j, (tagWindow (N ^ (-m)) (N ^ (-r)) b₀ mark j i Ksl).indicator
        (fun _ => ENNReal.ofReal (w j)) q ≤
      ENNReal.ofReal ((J : ℝ) * (2 * K)) *
        ((3 * ((2 * (⌈K⌉₊ + 5) + 1) * (2 * (3 * ⌈K⌉₊ + 9) + 1)) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (K * (N ^ (-m)) ^ 2 * c * (N ^ (-r)) ^ d) :=
    fun r hr hrs i Ksl q => weight_sum_le_pure htag hK hK₁ hσ hσ1 hδσ (hρσ r hrs) hJlow
      hbound hround hfloor (fun q i' => hcap r q i' hr hrs) i Ksl q
  -- the pure constant
  have hCpure : ∀ r : ℝ, 0 ≤ r → r ≤ s → ∀ κr : ℝ, 0 ≤ κr →
      ENNReal.ofReal ((N ^ (-m))⁻¹) * ENNReal.ofReal κr *
        (ENNReal.ofReal ((J : ℝ) * (2 * K)) *
          ((3 * ((2 * (⌈K⌉₊ + 5) + 1) * (2 * (3 * ⌈K⌉₊ + 9) + 1)) : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (K * (N ^ (-m)) ^ 2 * c * (N ^ (-r)) ^ d)) ≤
      ENNReal.ofReal (30000 * K ^ 4 * c * N ^ (-d * r) * κr) := by
    intro r hr hrs κr hκr
    rw [ofReal_prod5 (inv_nonneg.mpr hσ.le) hκr (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← hρd r]
    exact ceiling_arith hσ hJhigh hJ0 hK hc (by positivity) hκr (Nat.cast_nonneg _)
      (cardP_le hK) (by norm_num)
  refine ⟨?_, ?_⟩
  · -- the pure ceiling
    intro r hr hrs
    have hlam := map_obsAt_restrict_le hσ (hρpos r) b₀ w mark MeasurableSet.univ
      (κ := ENNReal.ofReal 1) (fun j => by rw [ENNReal.ofReal_one]; exact noise1_le_one hσ _)
      (hWpure r hr hrs · univ)
    simp only [mem_univ, ofPred_true, Measure.restrict_univ] at hlam
    obtain ⟨g, hg, heq, hle⟩ := density_of_le hlam (hCpure r hr hrs 1 zero_le_one)
    refine ⟨g, hg, ?_, ?_⟩
    · rw [observation_eq_obsAt]; exact heq
    · filter_upwards [hle] with z hz
      simpa only [mul_one] using hz
  · -- the joint ceilings
    intro r u hr hrs hu huV
    have hκ : ∀ (k : ℤ) j, noise1 (N ^ (-m)) {v | b₀ j 1 + v ∈ {v : ℝ | ⌊v / N ^ (-u)⌋ = k}} ≤
        ENNReal.ofReal (min 1 (N ^ (-u) / N ^ (-m))) := fun k j =>
      noise1_bin_le hσ (hρpos u) (b₀ j 1) k
    have hlam := map_velocity_le hσ (hρpos r) b₀ w mark hκ (fun k i q => hWpure r hr hrs i _ q)
    have hmin0 : 0 ≤ min 1 (N ^ (-u) / N ^ (-m)) :=
      le_min zero_le_one (div_nonneg (hρpos u).le hσ.le)
    have hC1 := hCpure r hr hrs _ hmin0
    obtain ⟨hGm, hGeq, hGle⟩ := exists_density_le
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hC1) hlam
    refine ⟨_, hGm, hGeq, ?_, ?_⟩
    · filter_upwards [hGle] with z hz
      rw [← hmin u]
      exact hz.trans hC1
    · -- the angular ceiling
      intro hrs' hang hu0 huU
      subst hrs'
      have hσu : N ^ (-m) ≤ N ^ (-u) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      have hWang : ∀ (k i : ℤ) (q : ℝ × ℝ),
          ∑ j, (tagWindow (N ^ (-m)) (N ^ (-r)) b₀ mark j i {v : ℝ | ⌊v / N ^ (-u)⌋ = k}).indicator
            (fun _ => ENNReal.ofReal (w j)) q ≤
          ENNReal.ofReal ((J : ℝ) * (2 * K)) *
            ((3 * ((2 * (⌈K⌉₊ + 5) + 1) * ((2 * (3 * ⌈K⌉₊ + 9) + 1) * (2 * 2 + 1))) : ℕ) :
              ℝ≥0∞) *
            ENNReal.ofReal (K * (N ^ (-m)) ^ 2 * c * (N ^ (-r)) ^ d * N ^ (-S * u)) :=
        fun k i q => weight_sum_le_ang htag hK hK₁ hσ hσ1 hδσ (hρσ r le_rfl) hσu hJlow hbound
          hround hfloor (fun q i' k' => hangular hang u q i' k' hu0 huU) i k q
      have hlam2 := map_velocity_le hσ (hρpos r) b₀ w mark hκ hWang
      have hC2 : ENNReal.ofReal ((N ^ (-m))⁻¹) * ENNReal.ofReal (min 1 (N ^ (-u) / N ^ (-m))) *
          (ENNReal.ofReal ((J : ℝ) * (2 * K)) *
            ((3 * ((2 * (⌈K⌉₊ + 5) + 1) * ((2 * (3 * ⌈K⌉₊ + 9) + 1) * (2 * 2 + 1))) : ℕ) :
              ℝ≥0∞) *
            ENNReal.ofReal (K * (N ^ (-m)) ^ 2 * c * (N ^ (-r)) ^ d * N ^ (-S * u))) ≤
          ENNReal.ofReal (30000 * K ^ 4 * c * N ^ (-d * r - S * u)) := by
        rw [ofReal_prod5 (inv_nonneg.mpr hσ.le) hmin0 (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hpow : N ^ (-d * r - S * u) = (N ^ (-r)) ^ d * N ^ (-S * u) := by
          rw [hρd r, ← Real.rpow_add hNp]; congr 1; ring
        have hmin1 : min 1 (N ^ (-u) / N ^ (-m)) ≤ 1 := min_le_left _ _
        have h := ceiling_arith (P := (N ^ (-r)) ^ d * N ^ (-S * u)) hσ hJhigh hJ0 hK hc
          (by positivity) hmin0 (Nat.cast_nonneg _) (cardA_le hK) (by norm_num)
        rw [hpow]
        calc (N ^ (-m))⁻¹ * min 1 (N ^ (-u) / N ^ (-m)) *
              ((J : ℝ) * (2 * K) *
                (((3 * ((2 * (⌈K⌉₊ + 5) + 1) * ((2 * (3 * ⌈K⌉₊ + 9) + 1) * (2 * 2 + 1)))) : ℕ) :
                  ℝ) * (K * (N ^ (-m)) ^ 2 * c * (N ^ (-r)) ^ d * N ^ (-S * u)))
            = (N ^ (-m))⁻¹ * min 1 (N ^ (-u) / N ^ (-m)) *
              ((J : ℝ) * (2 * K) *
                (((3 * ((2 * (⌈K⌉₊ + 5) + 1) * ((2 * (3 * ⌈K⌉₊ + 9) + 1) * (2 * 2 + 1)))) : ℕ) :
                  ℝ) * (K * (N ^ (-m)) ^ 2 * c * ((N ^ (-r)) ^ d * N ^ (-S * u)))) := by ring
          _ ≤ 30000 * K ^ 4 * c * ((N ^ (-r)) ^ d * N ^ (-S * u)) *
                min 1 (N ^ (-u) / N ^ (-m)) := h
          _ ≤ 30000 * K ^ 4 * c * ((N ^ (-r)) ^ d * N ^ (-S * u)) * 1 := by
              gcongr
          _ = 30000 * K ^ 4 * c * ((N ^ (-r)) ^ d * N ^ (-S * u)) := mul_one _
      filter_upwards [rnDeriv_le_of_le_smul hlam2] with z hz
      exact hz.trans hC2

end Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw
