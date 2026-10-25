import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Prune
import Submission.Lib.K4MovingMeshBoxes.Geometry
import Submission.Obl.k4_scalar_guarded_tangent_preparation.CodeVelocity

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MeasureTheory Finset
open Inherited.Native
open Submission.Lib.K4MovingMeshBoxes
open Submission.Obl.k4_scalar_guarded_tangent_preparation

noncomputable section

/-- A true block has bounded intercept and transverse menus in each
velocity bin. The number of velocity bins never enters either bound. -/
theorem true_key_menus {K q g χ m t₀ : ℝ} (hK : 0 ≤ K)
    (hq : 0 < q) (hg : 0 < g) (hχ : 0 < χ) (hm : 0 < m)
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (c : Fin 5 → ℝ) (hc : |c 4| ≤ K)
    (V : Finset ℤ) :
    ∃ (F₁ : ℤ → Finset ℤ) (F₂ : ℤ → ℤ → Finset ℤ),
      (∀ v, ((F₁ v).card : ℝ) ≤ 4 * (K * q + χ) / χ + 2) ∧
      (∀ v z, ((F₂ v z).card : ℝ) ≤ 4 * (K * q * g + 2 * K * χ) / m + 2) ∧
      ∀ b : Fin 6 → ℝ, ⌊b 3 / χ⌋ ∈ V →
        |b 0 + t₀ * b 3 - c 0 - t₀ * c 1| ≤ K * q →
        |b 1 + t₀ * b 4 - c 2 - t₀ * c 3 - c 4 * (b 0 + t₀ * b 3)| ≤ K * q * g →
        (![⌊b 3 / χ⌋, ⌊b 0 / χ⌋, ⌊(b 1 + t₀ * b 4) / m⌋] : Fin 3 → ℤ) ∈
          keyBox V F₁ F₂ := by
  choose F₁ hF₁ hF₁cover using fun v : ℤ =>
    interval_mesh_cover hχ (show 0 ≤ K * q + χ by positivity)
      (c 0 + t₀ * c 1 - t₀ * ((v : ℝ) * χ))
  choose F₂ hF₂ hF₂cover using fun v z : ℤ =>
    interval_mesh_cover hm (show 0 ≤ K * q * g + 2 * K * χ by positivity)
      (c 2 + t₀ * c 3 + c 4 * ((z : ℝ) * χ + t₀ * ((v : ℝ) * χ)))
  refine ⟨F₁, F₂, hF₁, hF₂, ?_⟩
  intro b hV hZ hY
  let v : ℤ := ⌊b 3 / χ⌋
  let z : ℤ := ⌊b 0 / χ⌋
  have hv : |b 3 - (v : ℝ) * χ| ≤ χ := floor_center_error hχ v rfl
  have hz : |b 0 - (z : ℝ) * χ| ≤ χ := floor_center_error hχ z rfl
  have ht : |t₀| ≤ 1 := abs_le.mpr ⟨by linarith [ht₀.1], ht₀.2⟩
  have hfirst : |b 0 - (c 0 + t₀ * c 1 - t₀ * ((v : ℝ) * χ))| ≤ K * q + χ := by
    have hid : b 0 - (c 0 + t₀ * c 1 - t₀ * ((v : ℝ) * χ)) =
        (b 0 + t₀ * b 3 - c 0 - t₀ * c 1) - t₀ * (b 3 - (v : ℝ) * χ) := by ring
    rw [hid]
    calc
      _ ≤ |b 0 + t₀ * b 3 - c 0 - t₀ * c 1| + |t₀ * (b 3 - (v : ℝ) * χ)| := abs_sub _ _
      _ ≤ K * q + 1 * χ := by rw [abs_mul]; gcongr
      _ = _ := by ring
  have hcloseZ : |(b 0 + t₀ * b 3) - ((z : ℝ) * χ + t₀ * ((v : ℝ) * χ))| ≤ 2 * χ := by
    have hid : (b 0 + t₀ * b 3) - ((z : ℝ) * χ + t₀ * ((v : ℝ) * χ)) =
        (b 0 - (z : ℝ) * χ) + t₀ * (b 3 - (v : ℝ) * χ) := by ring
    rw [hid]
    calc
      _ ≤ |b 0 - (z : ℝ) * χ| + |t₀ * (b 3 - (v : ℝ) * χ)| := abs_add_le _ _
      _ ≤ χ + 1 * χ := by rw [abs_mul]; gcongr
      _ = _ := by ring
  have hsecond : |b 1 + t₀ * b 4 -
      (c 2 + t₀ * c 3 + c 4 * ((z : ℝ) * χ + t₀ * ((v : ℝ) * χ)))| ≤
        K * q * g + 2 * K * χ := by
    have hid : b 1 + t₀ * b 4 -
        (c 2 + t₀ * c 3 + c 4 * ((z : ℝ) * χ + t₀ * ((v : ℝ) * χ))) =
        (b 1 + t₀ * b 4 - c 2 - t₀ * c 3 - c 4 * (b 0 + t₀ * b 3)) +
          c 4 * ((b 0 + t₀ * b 3) - ((z : ℝ) * χ + t₀ * ((v : ℝ) * χ))) := by ring
    rw [hid]
    calc
      _ ≤ |b 1 + t₀ * b 4 - c 2 - t₀ * c 3 - c 4 * (b 0 + t₀ * b 3)| +
          |c 4 * ((b 0 + t₀ * b 3) - ((z : ℝ) * χ + t₀ * ((v : ℝ) * χ)))| := abs_add_le _ _
      _ ≤ K * q * g + K * (2 * χ) := by rw [abs_mul]; gcongr
      _ = _ := by ring
  apply mem_keyBox hV
  · exact hF₁cover v (b 0) hfirst
  · exact hF₂cover v z (b 1 + t₀ * b 4) hsecond

/-- The original reference sum of all key refinements of a true block
costs only a fixed power of its geometric slack. -/
theorem true_key_reference_budget {K q g χ m a d : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (hg : 0 < g) (hχ : 0 < χ) (hm : 0 < m) (ha : 0 < a)
    (hχq : χ ≤ q) (hχg : χ ≤ q * g) (hmg : m ≤ q * g)
    (V : Finset ℤ) (F₁ : ℤ → Finset ℤ) (F₂ : ℤ → ℤ → Finset ℤ)
    (hF₁ : ∀ v, ((F₁ v).card : ℝ) ≤ 4 * (K * q + χ) / χ + 2)
    (hF₂ : ∀ v z, ((F₂ v z).card : ℝ) ≤ 4 * (K * q * g + 2 * K * χ) / m + 2)
    (w : ℤ → ℝ) (hw : ∀ v, 0 ≤ w v) (hwsum : ∑ v ∈ V, w v ≤ 1) :
    ∑ key ∈ keyBox V F₁ F₂, (q * χ * m * a ^ d) * w (key 0) ≤
      140 * K ^ 2 * a ^ d * q ^ 3 * g := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hc₁ (v : ℤ) : ((F₁ v).card : ℝ) ≤ 10 * K * q / χ := by
    apply (hF₁ v).trans
    apply (le_div_iff₀ hχ).mpr
    rw [add_mul, div_mul_cancel₀ _ hχ.ne']
    nlinarith [mul_le_mul_of_nonneg_right hK hq.le]
  have hc₂ (v z : ℤ) : ((F₂ v z).card : ℝ) ≤ 14 * K * q * g / m := by
    apply (hF₂ v z).trans
    apply (le_div_iff₀ hm).mpr
    rw [add_mul, div_mul_cancel₀ _ hm.ne']
    have hmK : m ≤ K * q * g := hmg.trans (by nlinarith [mul_le_mul_of_nonneg_right hK (mul_pos hq hg).le])
    have hχK : K * χ ≤ K * q * g := by nlinarith [mul_le_mul_of_nonneg_left hχg hK0]
    nlinarith
  have hcount := keyBox_sum_le V F₁ F₂ w hw hc₁ hc₂ (by positivity)
  have hsum : (∑ key ∈ keyBox V F₁ F₂, w (key 0)) ≤
      (10 * K * q / χ) * (14 * K * q * g / m) := by
    apply hcount.trans
    nlinarith [mul_le_mul_of_nonneg_right hwsum
      (show 0 ≤ (10 * K * q / χ) * (14 * K * q * g / m) by positivity)]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (q * χ * m * a ^ d) * ((10 * K * q / χ) * (14 * K * q * g / m)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp; ring

/-- All true labels are summed against their full original assignment
weights before any current intersections are selected. -/
theorem sum_true_key_references {ι : Type*} [Fintype ι]
    {K q g χ m a d : ℝ} (hK : 1 ≤ K) (hq : 0 < q) (hg : 0 < g)
    (hχ : 0 < χ) (hm : 0 < m) (ha : 0 < a)
    (hχq : χ ≤ q) (hχg : χ ≤ q * g) (hmg : m ≤ q * g)
    (V : Finset ℤ) (F₁ : ι → ℤ → Finset ℤ) (F₂ : ι → ℤ → ℤ → Finset ℤ)
    (hF₁ : ∀ i v, ((F₁ i v).card : ℝ) ≤ 4 * (K * q + χ) / χ + 2)
    (hF₂ : ∀ i v z, ((F₂ i v z).card : ℝ) ≤ 4 * (K * q * g + 2 * K * χ) / m + 2)
    (w : ℤ → ℝ) (hw : ∀ v, 0 ≤ w v) (hwsum : ∑ v ∈ V, w v ≤ 1)
    (reference : ι → ℝ) (hreference : ∑ i, reference i ≤ 1)
    (hprior : ∀ i, a ^ d * q ^ 3 * g ≤ K * reference i) :
    ∑ i, ∑ key ∈ keyBox V (F₁ i) (F₂ i), (q * χ * m * a ^ d) * w (key 0) ≤
      140 * K ^ 3 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  calc
    _ ≤ ∑ i, 140 * K ^ 2 * a ^ d * q ^ 3 * g := by
      apply Finset.sum_le_sum
      intro i _
      exact true_key_reference_budget hK hq hg hχ hm ha hχq hχg hmg
        V (F₁ i) (F₂ i) (hF₁ i) (hF₂ i) w hw hwsum
    _ ≤ ∑ i, (140 * K ^ 3) * reference i := by
      apply Finset.sum_le_sum
      intro i _
      have hh := mul_le_mul_of_nonneg_left (hprior i)
        (show 0 ≤ 140 * K ^ 2 by positivity)
      nlinarith only [hh]
    _ = (140 * K ^ 3) * ∑ i, reference i := (Finset.mul_sum ..).symm
    _ ≤ (140 * K ^ 3) * 1 := mul_le_mul_of_nonneg_left hreference (by positivity)
    _ = _ := mul_one _

/-- A projected slice refines into short key domains at a total cost
proportional to its earlier full-strip reference weight. -/
theorem projected_key_reference_budget {H q D χ m a d : ℝ}
    (hH : 1 ≤ H) (hq : 0 < q) (hD : 0 < D) (hχ : 0 < χ) (hm : 0 < m)
    (ha : 0 < a) (hmD : m ≤ D)
    (v z : ℤ) (J : Finset ℤ) (hJ : (J.card : ℝ) ≤ 4 * (H * D) / m + 2)
    (w : ℤ → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∑ key ∈ keyBox {v} (fun _ => {z}) (fun _ _ => J),
      (q * χ * m * a ^ d) * w (key 0) ≤ 6 * H * q * χ * D * a ^ d * w v := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hwv := hw v
  have hcount : (∑ key ∈ keyBox {v} (fun _ => {z}) (fun _ _ => J), w (key 0)) ≤
      w v * (4 * (H * D) / m + 2) := by
    have hh := keyBox_sum_le {v} (fun _ => {z}) (fun _ _ => J) w hw
      (c₁ := 1) (c₂ := 4 * (H * D) / m + 2)
      (by intro r; simp) (by intro r s; exact hJ) (by positivity)
    simpa using hh
  have hwidth : m * (4 * (H * D) / m + 2) ≤ 6 * H * D := by
    rw [mul_add, mul_div_cancel₀ _ hm.ne']
    have hd : D ≤ H * D := by nlinarith
    nlinarith
  rw [← Finset.mul_sum]
  calc
    _ ≤ (q * χ * m * a ^ d) * (w v * (4 * (H * D) / m + 2)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (q * χ * a ^ d * w v) * (m * (4 * (H * D) / m + 2)) := by ring
    _ ≤ (q * χ * a ^ d * w v) * (6 * H * D) :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = _ := by ring

/-- Summing all short time slots restores the original full projected
reference, with no time-bin count left in the budget. -/
theorem sum_projected_key_references {ι : Type*} [Fintype ι]
    {H q D χ m a d : ℝ} (hH : 1 ≤ H) (hD : 0 < D) (hχ : 0 < χ)
    (hm : 0 < m) (ha : 0 < a) (hmD : m ≤ D) (T : ℕ)
    (hq : q = ((2 : ℝ) ^ T)⁻¹) (v z : ι → ℤ)
    (J : Fin (2 ^ T) → ι → Finset ℤ)
    (hJ : ∀ t i, ((J t i).card : ℝ) ≤ 4 * (H * D) / m + 2)
    (w : ℤ → ℝ) (hw : ∀ v, 0 ≤ w v) :
    (∑ t : Fin (2 ^ T), ∑ i, ∑ key ∈ keyBox {v i} (fun _ => {z i}) (fun _ _ => J t i),
      (q * χ * m * a ^ d) * w (key 0)) ≤
        6 * H * ∑ i, (χ * D * a ^ d) * w (v i) := by
  have hqpos : 0 < q := by rw [hq]; positivity
  calc
    _ ≤ ∑ _t : Fin (2 ^ T), ∑ i, 6 * H * q * χ * D * a ^ d * w (v i) := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro i _
      exact projected_key_reference_budget hH hqpos hD hχ hm ha hmD
        (v i) (z i) (J t i) (hJ t i) w hw
    _ = ∑ _t : Fin (2 ^ T), (6 * H * q) * ∑ i, (χ * D * a ^ d) * w (v i) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      rw [hq]
      field_simp

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
