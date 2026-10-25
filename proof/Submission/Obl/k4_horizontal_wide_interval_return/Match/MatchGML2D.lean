/- Adapted within this LOT tree (g-oai-074) from o227 `k4_horizontal_three_projection_wide_return`,
session x0788, branch x0788, commit d1137a70, file
Submission/Obl/k4_horizontal_three_projection_wide_return/MatchGML2D.lean (namespace renamed into o250's). -/
import Mathlib
import Submission.Obl.k4_horizontal_wide_interval_return.Match.MatchQuad
import Submission.Obl.k4_horizontal_wide_interval_return.Match.MatchCor
import Submission.Obl.k4_horizontal_wide_interval_return.Match.MatchGMLN

/-!
# The matching lemma for quadratics of two variables

`quad2 F t y = F0 + F1 t + F2 y + F3 t² + F4 t y + F5 y²`. Members are close along the
whole segment `t ∈ [0,1]` at the paired value of `y`; jet counts are in all six
coefficients. The time slices `t = 0, 1/2, 1` feed `gmlN`.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.MatchGML2D

open MeasureTheory MatchQuad MatchCor MatchGMLN

/-- A quadratic in two variables. -/
def quad2 (F : Fin 6 → ℝ) (t y : ℝ) : ℝ :=
  F 0 + F 1 * t + F 2 * y + F 3 * t ^ 2 + F 4 * (t * y) + F 5 * y ^ 2

/-- The slice times. -/
noncomputable def tk : Fin 3 → ℝ := ![0, 1/2, 1]

lemma tk_mem (j : Fin 3) : tk j ∈ Set.Icc (0:ℝ) 1 := by
  fin_cases j <;> simp [tk] <;> norm_num

/-- The time slice at `tk j` as a linear map. -/
noncomputable def sliceL (j : Fin 3) : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun F := ![F 0 + F 1 * tk j + F 3 * tk j ^ 2, F 2 + F 4 * tk j, F 5]
  map_add' F G := by
    funext k; fin_cases k <;> simp <;> ring
  map_smul' c F := by
    funext k; fin_cases k <;> simp <;> ring

lemma quad_sliceL (j : Fin 3) (F : Fin 6 → ℝ) (y : ℝ) :
    quad (sliceL j F) y = quad2 F (tk j) y := by
  simp [quad, quad2, sliceL]; ring

lemma sliceL_op (j : Fin 3) (F : Fin 6 → ℝ) (X : ℝ) (hF : ∀ k, |F k| ≤ X) (k : Fin 3) :
    |sliceL j F k| ≤ 3 * X := by
  have ht := tk_mem j
  obtain ⟨h0, h1⟩ := ht
  have hX : 0 ≤ X := le_trans (abs_nonneg _) (hF 0)
  have ht2 : tk j ^ 2 ≤ 1 := by nlinarith
  have ht2' : 0 ≤ tk j ^ 2 := by positivity
  fin_cases k
  · simp only [sliceL, LinearMap.coe_mk, AddHom.coe_mk, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero]
    calc |F 0 + F 1 * tk j + F 3 * tk j ^ 2| ≤ |F 0| + |F 1 * tk j| + |F 3 * tk j ^ 2| :=
          abs_add_three _ _ _
      _ = |F 0| + |F 1| * tk j + |F 3| * tk j ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg ht2']
      _ ≤ X + X * 1 + X * 1 := by
          gcongr
          · exact hF 0
          · exact hF 1
          · exact hF 3
      _ = 3 * X := by ring
  · simp only [sliceL, LinearMap.coe_mk, AddHom.coe_mk, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    calc |F 2 + F 4 * tk j| ≤ |F 2| + |F 4 * tk j| := abs_add_le _ _
      _ = |F 2| + |F 4| * tk j := by rw [abs_mul, abs_of_nonneg h0]
      _ ≤ X + X * 1 := by
          gcongr
          · exact hF 2
          · exact hF 4
      _ ≤ 3 * X := by linarith
  · simp only [sliceL, LinearMap.coe_mk, AddHom.coe_mk, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.tail_cons,
      Matrix.head_cons]
    linarith [hF 5]

/-- Every coefficient is recovered from the three slices with constant `8`. -/
lemma sliceL_rec (F : Fin 6 → ℝ) (X : ℝ) (h : ∃ k, X ≤ |F k|) :
    ∃ j, X / 8 ≤ cnorm (sliceL j F) := by
  obtain ⟨k, hk⟩ := h
  by_contra hcon
  push Not at hcon
  have hs : ∀ j i, |sliceL j F i| < X / 8 := fun j i => lt_of_le_of_lt (abs_le_cnorm _ i) (hcon j)
  have e0 := hs 0 0; have e1 := hs 1 0; have e2 := hs 2 0
  have f0 := hs 0 1; have f2 := hs 2 1; have g0 := hs 0 2
  have hX : 0 < X := by
    have := hcon 0
    have h0 : 0 ≤ cnorm (sliceL 0 F) := le_trans (abs_nonneg _) (abs_le_cnorm _ 0)
    linarith
  simp [sliceL, tk] at e0 e1 e2 f0 f2 g0
  rw [abs_lt] at e0 e1 e2 f0 f2 g0
  have hk' : X ≤ |F k| := hk
  fin_cases k <;> simp at hk' <;> rw [le_abs] at hk' <;> rcases hk' with hk' | hk' <;>
    norm_num at e1 <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, f0.1, f0.2, f2.1, f2.2, g0.1, g0.2]

/-- **The matching lemma for two-variable quadratics.** -/
theorem gml2D (hM : MatchHyp) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]
      (F₁ : ι₁ → Fin 6 → ℝ) (F₂ : ι₂ → Fin 6 → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
      (P : Measure ((ι₁ × ι₂) × ℝ)) [IsFiniteMeasure P] (δ Mst A B w : ℝ),
      0 < δ → R₀ * δ ≤ Mst → 1 ≤ A → A ≤ (Mst / δ) ^ η →
      0 < w → w ≤ 1 / 4 → 18 * B * w ≤ δ →
      (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
      (∀ i k, |F₁ i k| ≤ B) → (∀ j k, |F₂ j k| ≤ B) →
      (∀ i (x : ℝ), P {p | p.1.1 = i ∧ p.2 ∈ Set.Icc (x - w) x} ≤ ENNReal.ofReal (A * T₁ i * w)) →
      (∀ j (x : ℝ), P {p | p.1.2 = j ∧ p.2 ∈ Set.Icc (x - w) x} ≤ ENNReal.ofReal (A * T₂ j * w)) →
      (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun i => ∀ k, |F₁ i k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d) →
      (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun j => ∀ k, |F₂ j k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d) →
      (∀ᵐ p ∂P, p.2 ∈ Set.Icc (1/4 : ℝ) (3/4) ∧ ∀ t ∈ Set.Icc (0:ℝ) 1,
        |quad2 (F₁ p.1.1) t p.2 - quad2 (F₂ p.1.2) t p.2| ≤ δ) →
      P {p | ∃ k, Mst ≤ |F₁ p.1.1 k - F₂ p.1.2 k|} ≤
        ENNReal.ofReal (A * (Mst / δ) ^ (-η) * (∑ i, T₁ i + ∑ j, T₂ j)) := by
  obtain ⟨η, hη, R₀, hR₀, H⟩ := gmlN hM hd0 hd1 (n := 6) (m := 3) sliceL (Lop := 3) (Crec := 8)
    (by norm_num) (by norm_num) (fun j F X hF k => sliceL_op j F X hF k) sliceL_rec
  refine ⟨η, hη, R₀, hR₀, ?_⟩
  intro ι₁ ι₂ _ _ _ _ _ _ F₁ F₂ T₁ T₂ P _ δ Mst A B w hδ hMst hA1 hA hw hw4 hwδ hT₁ hT₂
    hB₁ hB₂ hi₁ hi₂ hc₁ hc₂ hae
  refine H ι₁ ι₂ F₁ F₂ T₁ T₂ P δ Mst A (3 * B) w hδ hMst hA1 hA hw hw4 (by linarith) hT₁ hT₂
    (fun j' i k => sliceL_op j' (F₁ i) B (hB₁ i) k) (fun j' i k => sliceL_op j' (F₂ i) B (hB₂ i) k)
    hi₁ hi₂ hc₁ hc₂ ?_
  filter_upwards [hae] with p hp
  refine ⟨hp.1, fun j' => ?_⟩
  rw [quad_sliceL, quad_sliceL]
  exact hp.2 _ (tk_mem j')

end Submission.Obl.k4_horizontal_wide_interval_return.MatchGML2D
