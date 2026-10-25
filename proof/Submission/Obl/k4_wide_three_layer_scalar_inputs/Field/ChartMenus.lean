import Submission.Obl.k4_horizontal_coefficient_count.LMBand
import Submission.Obl.k4_scalar_guarded_tangent_preparation.CodeVelocity

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Field

open Finset

noncomputable section

open scoped Classical

/-- The intercept in the time-normalized coordinates of the original block. -/
def normalizedIntercept (t₀ q c₀ c₁ b v : ℝ) : ℝ :=
  (b + t₀ * v - c₀ - t₀ * c₁) / q

/-- The physical intercept at the left endpoints of a normalized chart. -/
def physicalChartCenter (t₀ c₀ c₁ χ : ℝ) (B V : ℤ) : ℝ :=
  c₀ + t₀ * c₁ + χ * (B : ℝ) - t₀ * (χ * (V : ℝ))

/-- Five original intercept bins cover one normalized-intercept/velocity chart. -/
def physicalChartBins (t₀ c₀ c₁ χ : ℝ) (B V : ℤ) : Finset ℤ :=
  (Finset.Icc (-2 : ℤ) 2).image (fun d => ⌊physicalChartCenter t₀ c₀ c₁ χ B V / χ⌋ + d)

theorem physicalChartBins_card (t₀ c₀ c₁ χ : ℝ) (B V : ℤ) :
    (physicalChartBins t₀ c₀ c₁ χ B V).card ≤ 5 := by
  exact Finset.card_image_le.trans (by norm_num)

theorem mem_physicalChartBins {t₀ q c₀ c₁ χ b v : ℝ} {B V : ℤ}
    (hq : 0 < q) (hχ : 0 < χ) (ht₀ : |t₀| ≤ 1)
    (hB : ⌊normalizedIntercept t₀ q c₀ c₁ b v / (χ / q)⌋ = B)
    (hV : ⌊v / χ⌋ = V) :
    ⌊b / χ⌋ ∈ physicalChartBins t₀ c₀ c₁ χ B V := by
  have hB' : ⌊(b + t₀ * v - c₀ - t₀ * c₁) / χ⌋ = B := by
    convert hB using 1
    congr 1
    unfold normalizedIntercept
    field_simp
  have hbc := Submission.Obl.k4_scalar_guarded_tangent_preparation.floor_center_error hχ B hB'
  have hvc := Submission.Obl.k4_scalar_guarded_tangent_preparation.floor_center_error hχ V hV
  have hclose : |b - physicalChartCenter t₀ c₀ c₁ χ B V| ≤ 2 * χ := by
    have hid : b - physicalChartCenter t₀ c₀ c₁ χ B V =
        (b + t₀ * v - c₀ - t₀ * c₁ - (B : ℝ) * χ) - t₀ * (v - (V : ℝ) * χ) := by
      unfold physicalChartCenter
      ring
    rw [hid]
    calc _ ≤ |b + t₀ * v - c₀ - t₀ * c₁ - (B : ℝ) * χ| + |t₀| * |v - (V : ℝ) * χ| := by
          simpa only [abs_mul] using
            abs_sub (b + t₀ * v - c₀ - t₀ * c₁ - (B : ℝ) * χ) (t₀ * (v - (V : ℝ) * χ))
      _ ≤ χ + 1 * χ := by gcongr
      _ = 2 * χ := by ring
  have hm := Submission.Obl.k4_horizontal_coefficient_count.floor_div_mem_window hχ hclose
  norm_num only [Int.ceil_ofNat] at hm
  apply Finset.mem_image.mpr
  exact ⟨_, hm, by omega⟩

/-- Union the original per-chart menus across these five intercept bins. -/
def normalizedChartMenu {Γ : Type*} [DecidableEq Γ] (G : (ℤ × ℤ) → Finset Γ)
    (t₀ c₀ c₁ χ : ℝ) (B V : ℤ) : Finset Γ :=
  (physicalChartBins t₀ c₀ c₁ χ B V).biUnion (fun J => G (V, J))

theorem normalizedChartMenu_card {Γ : Type*} [DecidableEq Γ]
    (G : (ℤ × ℤ) → Finset Γ) (t₀ c₀ c₁ χ : ℝ) (B V : ℤ) {H : ℝ}
    (hH : 0 ≤ H) (hG : ∀ ch, ((G ch).card : ℝ) ≤ H) :
    ((normalizedChartMenu G t₀ c₀ c₁ χ B V).card : ℝ) ≤ 5 * H := by
  calc _ ≤ ∑ J ∈ physicalChartBins t₀ c₀ c₁ χ B V, ((G (V, J)).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le :
          (normalizedChartMenu G t₀ c₀ c₁ χ B V).card ≤
            ∑ J ∈ physicalChartBins t₀ c₀ c₁ χ B V, (G (V, J)).card)
    _ ≤ ∑ _J ∈ physicalChartBins t₀ c₀ c₁ χ B V, H :=
        Finset.sum_le_sum fun J _ => hG (V, J)
    _ = ((physicalChartBins t₀ c₀ c₁ χ B V).card : ℝ) * H := by simp
    _ ≤ 5 * H := mul_le_mul_of_nonneg_right (by exact_mod_cast physicalChartBins_card t₀ c₀ c₁ χ B V) hH

theorem mem_normalizedChartMenu {Γ : Type*} [DecidableEq Γ]
    (G : (ℤ × ℤ) → Finset Γ) {t₀ q c₀ c₁ χ b v : ℝ} {B V : ℤ} {γ : Γ}
    (hq : 0 < q) (hχ : 0 < χ) (ht₀ : |t₀| ≤ 1)
    (hB : ⌊normalizedIntercept t₀ q c₀ c₁ b v / (χ / q)⌋ = B)
    (hV : ⌊v / χ⌋ = V) (hγ : γ ∈ G (⌊v / χ⌋, ⌊b / χ⌋)) :
    γ ∈ normalizedChartMenu G t₀ c₀ c₁ χ B V := by
  apply Finset.mem_biUnion.mpr
  exact ⟨_, mem_physicalChartBins hq hχ ht₀ hB hV, by simpa [hV] using hγ⟩

/-- An affine coefficient pair restricted to the line through a chart center. -/
def affineOption (tc : Fin 4 → ℝ) (βc vc c₁ : ℝ) : Fin 3 → ℝ :=
  ![tc 0 + tc 2 * βc, tc 1 + tc 2 * (vc - c₁), tc 3]

/-- The finite common-field menu, with its coefficient bound enforced even on
unoccupied charts. The original velocity chart is kept. -/
def affineMenu {Γ : Type*} [DecidableEq Γ] (G : (ℤ × ℤ) → Finset Γ)
    (tc : Γ → Fin 4 → ℝ) (t₀ q c₀ c₁ χ H K : ℝ) (ch : ℤ × ℤ) :
    Finset (Fin 3 → ℝ) :=
  ((normalizedChartMenu G t₀ c₀ c₁ χ ch.1 ch.2).image
    (fun γ => affineOption (tc γ) ((χ / q) * (ch.1 : ℝ)) (χ * (ch.2 : ℝ)) c₁)).filter
      (fun a => ∀ e, |a e| ≤ H * (1 + 3 * K))

theorem affineMenu_card {Γ : Type*} [DecidableEq Γ]
    (G : (ℤ × ℤ) → Finset Γ) (tc : Γ → Fin 4 → ℝ) (t₀ q c₀ c₁ χ H K : ℝ)
    (hH : 0 ≤ H) (hG : ∀ ch, ((G ch).card : ℝ) ≤ H) (ch : ℤ × ℤ) :
    ((affineMenu G tc t₀ q c₀ c₁ χ H K ch).card : ℝ) ≤ 5 * H := by
  calc _ ≤ ((normalizedChartMenu G t₀ c₀ c₁ χ ch.1 ch.2).card : ℝ) := by
        exact_mod_cast (Finset.card_filter_le _ _).trans Finset.card_image_le
    _ ≤ 5 * H := normalizedChartMenu_card G t₀ c₀ c₁ χ ch.1 ch.2 hH hG

theorem affineMenu_bound {Γ : Type*} [DecidableEq Γ]
    (G : (ℤ × ℤ) → Finset Γ) (tc : Γ → Fin 4 → ℝ) (t₀ q c₀ c₁ χ H K : ℝ)
    (ch : ℤ × ℤ) (a : Fin 3 → ℝ) (ha : a ∈ affineMenu G tc t₀ q c₀ c₁ χ H K ch) :
    ∀ e, |a e| ≤ H * (1 + 3 * K) := (Finset.mem_filter.mp ha).2

theorem affineOption_bound {tc : Fin 4 → ℝ} {H K β v c₁ χb χv : ℝ}
    (hH : 0 ≤ H) (hK : 1 ≤ K) (htc : ∀ e, |tc e| ≤ H)
    (hβ : |β| ≤ K) (hv : |v| ≤ K) (hc₁ : |c₁| ≤ K)
    (hχb : 0 < χb) (hχb1 : χb ≤ 1) (hχv : 0 < χv) (hχv1 : χv ≤ 1) :
    ∀ e, |affineOption tc (χb * (⌊β / χb⌋ : ℝ)) (χv * (⌊v / χv⌋ : ℝ)) c₁ e| ≤
      H * (1 + 3 * K) := by
  have hβerr := Submission.Obl.k4_scalar_guarded_tangent_preparation.floor_center_error hχb ⌊β / χb⌋ rfl
  have hverr := Submission.Obl.k4_scalar_guarded_tangent_preparation.floor_center_error hχv ⌊v / χv⌋ rfl
  have hβc : |χb * (⌊β / χb⌋ : ℝ)| ≤ 2 * K := by
    calc _ ≤ |β| + |β - (⌊β / χb⌋ : ℝ) * χb| := by
          convert abs_sub β (β - (⌊β / χb⌋ : ℝ) * χb) using 1
          congr 1
          ring
      _ ≤ 2 * K := by linarith
  have hvc : |χv * (⌊v / χv⌋ : ℝ)| ≤ 2 * K := by
    calc _ ≤ |v| + |v - (⌊v / χv⌋ : ℝ) * χv| := by
          convert abs_sub v (v - (⌊v / χv⌋ : ℝ) * χv) using 1
          congr 1
          ring
      _ ≤ 2 * K := by linarith
  have hvcc : |χv * (⌊v / χv⌋ : ℝ) - c₁| ≤ 3 * K :=
    (abs_sub _ _).trans (by linarith)
  intro e
  fin_cases e
  · change |tc 0 + tc 2 * (χb * (⌊β / χb⌋ : ℝ))| ≤ _
    calc _ ≤ |tc 0| + |tc 2| * |χb * (⌊β / χb⌋ : ℝ)| := by
          simpa only [abs_mul] using abs_add_le (tc 0) (tc 2 * (χb * (⌊β / χb⌋ : ℝ)))
      _ ≤ H + H * (2 * K) := by gcongr <;> exact htc _
      _ ≤ H * (1 + 3 * K) := by nlinarith
  · change |tc 1 + tc 2 * (χv * (⌊v / χv⌋ : ℝ) - c₁)| ≤ _
    calc _ ≤ |tc 1| + |tc 2| * |χv * (⌊v / χv⌋ : ℝ) - c₁| := by
          simpa only [abs_mul] using abs_add_le (tc 1) (tc 2 * (χv * (⌊v / χv⌋ : ℝ) - c₁))
      _ ≤ H + H * (3 * K) := by gcongr <;> exact htc _
      _ = H * (1 + 3 * K) := by ring
  · change |tc 3| ≤ _
    exact (htc 3).trans (by nlinarith)

/-- Freezing the intercept and original velocity in the coefficient menu costs
only their chart widths. -/
theorem affineOption_fit {tc : Fin 4 → ℝ} {H β v c₁ χb χv t : ℝ}
    (hH : 0 ≤ H) (htc : |tc 2| ≤ H) (hχb : 0 < χb) (hχv : 0 < χv) (ht : |t| ≤ 1) :
    let a := affineOption tc (χb * (⌊β / χb⌋ : ℝ)) (χv * (⌊v / χv⌋ : ℝ)) c₁
    |(tc 0 + tc 1 * t + tc 2 * (β + t * (v - c₁))) - a 0 - a 1 * t| ≤ H * (χb + χv) := by
  dsimp only
  have hβerr := Submission.Obl.k4_scalar_guarded_tangent_preparation.floor_center_error hχb ⌊β / χb⌋ rfl
  have hverr := Submission.Obl.k4_scalar_guarded_tangent_preparation.floor_center_error hχv ⌊v / χv⌋ rfl
  have hid : tc 0 + tc 1 * t + tc 2 * (β + t * (v - c₁)) -
      affineOption tc (χb * (⌊β / χb⌋ : ℝ)) (χv * (⌊v / χv⌋ : ℝ)) c₁ 0 -
      affineOption tc (χb * (⌊β / χb⌋ : ℝ)) (χv * (⌊v / χv⌋ : ℝ)) c₁ 1 * t =
        tc 2 * ((β - (⌊β / χb⌋ : ℝ) * χb) + t * (v - (⌊v / χv⌋ : ℝ) * χv)) := by
    simp only [affineOption, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hid, abs_mul]
  apply mul_le_mul htc ?_ (abs_nonneg _) hH
  calc _ ≤ |β - (⌊β / χb⌋ : ℝ) * χb| + |t| * |v - (⌊v / χv⌋ : ℝ) * χv| := by
        simpa only [abs_mul] using abs_add_le (β - (⌊β / χb⌋ : ℝ) * χb)
          (t * (v - (⌊v / χv⌋ : ℝ) * χv))
    _ ≤ χb + 1 * χv := by gcongr
    _ = χb + χv := by ring

/-- An occupied bounded occurrence contributes its affine line option to the
normalized chart menu. -/
theorem mem_affineMenu {Γ : Type*} [DecidableEq Γ]
    (G : (ℤ × ℤ) → Finset Γ) (tc : Γ → Fin 4 → ℝ)
    {t₀ q c₀ c₁ χ H K b v : ℝ} {γ : Γ}
    (hq : 0 < q) (hχ : 0 < χ) (ht₀ : |t₀| ≤ 1)
    (hH : 0 ≤ H) (hK : 1 ≤ K) (htc : ∀ e, |tc γ e| ≤ H)
    (hβ : |normalizedIntercept t₀ q c₀ c₁ b v| ≤ K)
    (hv : |v| ≤ K) (hc₁ : |c₁| ≤ K) (hχb1 : χ / q ≤ 1) (hχv1 : χ ≤ 1)
    (hγ : γ ∈ G (⌊v / χ⌋, ⌊b / χ⌋)) :
    let β := normalizedIntercept t₀ q c₀ c₁ b v
    affineOption (tc γ) ((χ / q) * (⌊β / (χ / q)⌋ : ℝ)) (χ * (⌊v / χ⌋ : ℝ)) c₁ ∈
      affineMenu G tc t₀ q c₀ c₁ χ H K (⌊β / (χ / q)⌋, ⌊v / χ⌋) := by
  dsimp only
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_image.mpr ⟨γ, mem_normalizedChartMenu G hq hχ ht₀ rfl rfl hγ, rfl⟩
  · exact affineOption_bound hH hK htc hβ hv hc₁ (div_pos hχ hq) hχb1 hχ hχv1

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Field
