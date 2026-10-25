-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.SingleScaleFinal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.SingleScaleCore
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.FromSingleScale

/-!
# The single-scale estimate `P2Statement` from the Furstenberg bush estimate and
the rich-strip count

Choice of the parameters: with `ε₀, η_A` from the Furstenberg estimate, take
`τ = θ = η = κ = min ε₀ η_A / 16` and `r₀` small.
-/

namespace WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

lemma exists_rpow_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r ≤ r₁ → r ^ a ≤ c := by
  refine ⟨c ^ a⁻¹, Real.rpow_pos_of_pos hc _, fun r hr hr1 => ?_⟩
  calc r ^ a ≤ (c ^ a⁻¹) ^ a := Real.rpow_le_rpow hr.le hr1 ha.le
    _ = c := Real.rpow_inv_rpow hc.le ha.ne'

lemma exists_log_lt_rpow {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r ≤ r₁ → A * (1 + Real.log (1 / r)) < r ^ (-a) := by
  set M : ℝ := A + 2 * A / a + 1 with hMdef
  have hM : 1 ≤ M := by rw [hMdef]; have : 0 ≤ 2 * A / a := by positivity
                        linarith
  refine ⟨min 1 ((M ^ (2 / a))⁻¹ / 2), by positivity, ?_⟩
  intro r hr hr1
  set x := 1 / r with hxdef
  have hr1' : r ≤ 1 := hr1.trans (min_le_left _ _)
  have hx1 : 1 ≤ x := by rw [hxdef, le_div_iff₀ hr]; linarith
  have hx0 : 0 < x := by linarith
  -- x ^ (a / 2) > M
  have hrM : r < (M ^ (2 / a))⁻¹ := by
    have := hr1.trans (min_le_right _ _)
    have hp : 0 < (M ^ (2 / a))⁻¹ := by positivity
    linarith
  have hxM : M ^ (2 / a) < x := by
    rw [hxdef, lt_div_iff₀ hr]
    have hp : 0 < M ^ (2 / a) := by positivity
    calc M ^ (2 / a) * r < M ^ (2 / a) * (M ^ (2 / a))⁻¹ := mul_lt_mul_of_pos_left hrM hp
      _ = 1 := mul_inv_cancel₀ hp.ne'
  set y := x ^ (a / 2) with hydef
  have hyM : M < y := by
    have h := Real.rpow_lt_rpow (by positivity) hxM (by positivity : 0 < a / 2)
    rw [← Real.rpow_mul (by positivity)] at h
    have : 2 / a * (a / 2) = 1 := by field_simp
    rw [this, Real.rpow_one] at h
    exact h
  have hy1 : 1 ≤ y := by linarith
  have hlog : Real.log x ≤ y / (a / 2) := Real.log_le_rpow_div hx0.le (by positivity)
  have hya : y ^ 2 = x ^ a := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have hra : r ^ (-a) = x ^ a := by
    rw [hxdef, Real.rpow_neg hr.le, Real.div_rpow zero_le_one hr.le, Real.one_rpow, one_div]
  rw [hra, ← hya]
  have h2 : y / (a / 2) = 2 / a * y := by field_simp
  rw [h2] at hlog
  have hA2 : A * (1 + Real.log x) ≤ A + 2 * A / a * y := by
    have : A * Real.log x ≤ A * (2 / a * y) := mul_le_mul_of_nonneg_left hlog hA
    have : A * (2 / a * y) = 2 * A / a * y := by ring
    nlinarith
  have hfin : A + 2 * A / a * y < y ^ 2 := by
    have h2A : 0 ≤ 2 * A / a := by positivity
    have : y * M < y * y := mul_lt_mul_of_pos_left hyM (by linarith)
    nlinarith
  linarith

/-- `P2Statement` from the Furstenberg bush estimate and the rich-strip count, in
their internal forms. -/
theorem P2_of_furstenberg_richstrip
    (hA : ∀ ε : ℝ, 0 < ε → ∃ ε₀ ηA rA : ℝ, 0 < ε₀ ∧ 0 < ηA ∧ 0 < rA ∧
      ∀ r σ : ℝ, 0 < r → r ≤ rA → 1 / 4 ≤ σ → σ ≤ 1 - ε → FurstenbergAt r σ ε₀ ηA)
    (hB : ∃ AB : ℝ, 0 < AB ∧ ∀ r C : ℝ, 0 < r → r ≤ 1 → 1 ≤ C → RichStripAt r C AB) :
    P2Statement := by
  intro Fr hFr ε hε
  subst hFr
  obtain ⟨ε₀, ηA, rA, hε₀, hηA, hrA, hFurst⟩ := hA ε hε
  obtain ⟨AB, hAB, hRich⟩ := hB
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min ε₀ ηA / 16 := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; exact div_pos (lt_min hε₀ hηA) (by norm_num)
  have hκε : κ ≤ ε₀ / 16 := by
    rw [hκdef]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hκη : κ ≤ ηA / 16 := by
    rw [hκdef]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨r₁, hr₁, hr₁spec⟩ :=
    exists_rpow_le (a := ηA - 2 * κ) (c := 1 / 258) (by linarith) (by norm_num)
  obtain ⟨r₂, hr₂, hr₂spec⟩ := exists_log_lt_rpow (a := ε₀ / 2) (A := AB) (by positivity) hAB.le
  refine ⟨κ, κ, κ, min (min rA (1 / 6)) (min r₁ r₂), hκ, hκ, hκ, by positivity, ?_⟩
  intro δ r σ K C hδ hδr hrr₀ hσ1 hσ2 hK hKr hC hCr G G' E hG hG' hsep hE hthin
  have hr : 0 < r := lt_of_lt_of_le hδ hδr
  have hrA' : r ≤ rA := hrr₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr6 : r ≤ 1 / 6 := hrr₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hr1 : r ≤ r₁ := hrr₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr2 : r ≤ r₂ := hrr₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrle1 : r ≤ 1 := by linarith
  have hs := hr₁spec r hr hr1
  set s := r ^ (ηA - 2 * κ) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hr _
  set t := r ^ (-(2 * κ)) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hr _
  have hrκ0 : 0 < r ^ (-κ) := Real.rpow_pos_of_pos hr _
  have htt : r ^ (-κ) * r ^ (-κ) = t := by
    rw [htdef, ← Real.rpow_add hr]; congr 1; ring
  have hηt : r ^ (-ηA) = t / s := by
    rw [htdef, hsdef, eq_div_iff hs0.ne', ← Real.rpow_add hr]; congr 1; ring
  have hts : 258 * t ≤ t / s := by
    rw [le_div_iff₀ hs0]; nlinarith
  have hFrostC : 2 * C * r ^ (-κ) ≤ r ^ (-ηA) := by
    rw [hηt]
    have : C * r ^ (-κ) ≤ r ^ (-κ) * r ^ (-κ) := mul_le_mul_of_nonneg_right hCr hrκ0.le
    nlinarith
  have hKTC : 9 * K * r ^ (-κ) ≤ r ^ (-ηA) := by
    rw [hηt]
    have : K * r ^ (-κ) ≤ r ^ (-κ) * r ^ (-κ) := mul_le_mul_of_nonneg_right hKr hrκ0.le
    nlinarith
  have hbushC : r ^ (ηA - σ) ≤ r ^ (κ - σ) / (258 * K) := by
    have hK0 : 0 < K := by linarith
    have hsplit : r ^ (ηA - σ) = s * (r ^ (κ - σ) * r ^ κ) := by
      rw [hsdef, ← Real.rpow_add hr, ← Real.rpow_add hr]; congr 1; ring
    have hKκ : K * r ^ κ ≤ 1 := by
      have h1 : r ^ (-κ) = (r ^ κ)⁻¹ := Real.rpow_neg hr.le κ
      rw [h1] at hKr
      have hp : 0 < r ^ κ := Real.rpow_pos_of_pos hr κ
      have := mul_le_mul_of_nonneg_right hKr hp.le
      rwa [inv_mul_cancel₀ hp.ne'] at this
    rw [hsplit, le_div_iff₀ (by positivity)]
    have hp1 : 0 < r ^ (κ - σ) := Real.rpow_pos_of_pos hr _
    have hp2 : 0 < r ^ κ := Real.rpow_pos_of_pos hr κ
    calc s * (r ^ (κ - σ) * r ^ κ) * (258 * K) = (258 * s) * r ^ (κ - σ) * (K * r ^ κ) := by ring
      _ ≤ 1 * r ^ (κ - σ) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hp1.le) hKκ
            (by positivity) (by positivity)
      _ = r ^ (κ - σ) := by ring
  have hfinal : AB * C * (1 + Real.log (1 / r)) < r ^ (2 * κ - ε₀) := by
    have hlog0 : 0 ≤ 1 + Real.log (1 / r) := by
      have : 0 ≤ Real.log (1 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
      linarith
    have h1 := hr₂spec r hr hr2
    have h2 : AB * C * (1 + Real.log (1 / r)) ≤ r ^ (-κ) * (AB * (1 + Real.log (1 / r))) := by
      have : 0 ≤ AB * (1 + Real.log (1 / r)) := by positivity
      nlinarith
    have h3 : r ^ (-κ) * (AB * (1 + Real.log (1 / r))) < r ^ (-κ) * r ^ (-(ε₀ / 2)) :=
      mul_lt_mul_of_pos_left h1 hrκ0
    have h4 : r ^ (-κ) * r ^ (-(ε₀ / 2)) ≤ r ^ (2 * κ - ε₀) := by
      rw [← Real.rpow_add hr]
      exact Real.rpow_le_rpow_of_exponent_ge hr hrle1 (by linarith)
    linarith
  exact heavy_count_le_core (τ := κ) (θ := κ) (η := ηA) (ε₀ := ε₀) (AB := AB) hδ hδr hr6
    (by linarith) (by linarith) hK hC hFrostC hbushC hKTC hfinal
    (hFurst r σ hr hrA' hσ1 hσ2) (hRich r C hr hrle1 hC) hG hG' hsep hE hthin

end WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs
