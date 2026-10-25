import Submission.Obl.k4_matching_palette_likelihood.Basic

open scoped BigOperators

namespace Submission.Obl.k4_matching_palette_likelihood

variable {α : Type*} [Fintype α]

/-- Sum the masses of any collection of distinct palette fibers. -/
lemma sum_colorMass_le (p : α → ℝ) (f Z : α → ℕ) (hp : ∀ x, 0 ≤ p x)
    (b : ℕ) (t : Finset ℕ) :
    ∑ z ∈ t, colorMass p f Z b z ≤ fiberMass p f b := by
  classical
  let s := Finset.univ.filter (fun x => f x = b)
  have h (z : ℕ) : colorMass p f Z b z = ∑ x ∈ s.filter (fun x => Z x = z), p x := by
    simp [colorMass, s, Finset.filter_filter]
  simp_rw [h]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun x _ _ => hp x)

/-- On one finer-record cell, the old/new posterior ratio has mean at most one. -/
lemma ratio_cell_le (p : α → ℝ) (f g Z : α → ℕ) (hp : ∀ x, 0 ≤ p x)
    (hfg : ∀ x y, g x = g y → f x = f y) (r : ℕ) :
    ∑ x ∈ Finset.univ.filter (fun x => g x = r),
      p x * (posterior p f Z x / posterior p g Z x) ≤ fiberMass p g r := by
  classical
  let s := Finset.univ.filter (fun x => g x = r)
  by_cases hs : s.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hs
    have hx₀r : g x₀ = r := (Finset.mem_filter.mp hx₀).2
    let b := f x₀
    let d := fiberMass p g r
    let B := fiberMass p f b
    let A := colorMass p f Z b
    let J := fun z => colorMass p g Z r z
    have hd : 0 ≤ d := fiberMass_nonneg p g hp r
    have hB : 0 ≤ B := fiberMass_nonneg p f hp b
    have hA (z : ℕ) : 0 ≤ A z := colorMass_nonneg p f Z hp b z
    have hf (x : α) (hx : x ∈ s) : f x = b := by
      exact hfg x x₀ ((Finset.mem_filter.mp hx).2.trans hx₀r.symm)
    have hq (x : α) (hx : x ∈ s) :
        posterior p f Z x / posterior p g Z x = (A (Z x) / B) / (J (Z x) / d) := by
      simp only [posterior, hf x hx, (Finset.mem_filter.mp hx).2]
      rfl
    have hJ (z : ℕ) : J z = ∑ x ∈ s.filter (fun x => Z x = z), p x := by
      simp [J, colorMass, s, Finset.filter_filter]
    have heq : (∑ x ∈ s, p x * (posterior p f Z x / posterior p g Z x)) =
        ∑ z ∈ s.image Z, J z * ((A z / B) / (J z / d)) := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image Z)
        (g := Z) (fun x hx => Finset.mem_image_of_mem Z hx)
        (fun x => p x * (posterior p f Z x / posterior p g Z x))]
      apply Finset.sum_congr rfl
      intro z hz
      rw [hJ, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hq x ((Finset.mem_filter.mp hx).1), (Finset.mem_filter.mp hx).2, ← hJ]
    have hterm (z : ℕ) : J z * ((A z / B) / (J z / d)) ≤ d * (A z / B) := by
      by_cases hz : J z = 0
      · simp [hz, mul_nonneg hd (div_nonneg (hA z) hB)]
      · calc
          J z * ((A z / B) / (J z / d)) = d * (A z / B) := by
            calc
              _ = (J z / J z) * (d * (A z / B)) := by
                simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
                ring
              _ = _ := by rw [div_self hz, one_mul]
          _ ≤ _ := le_rfl
    calc
      (∑ x ∈ Finset.univ.filter (fun x => g x = r),
        p x * (posterior p f Z x / posterior p g Z x)) =
          ∑ z ∈ s.image Z, J z * ((A z / B) / (J z / d)) := heq
      _ ≤ ∑ z ∈ s.image Z, d * (A z / B) := Finset.sum_le_sum (fun z _ => hterm z)
      _ = d * ((∑ z ∈ s.image Z, A z) / B) := by
        rw [← Finset.mul_sum, ← Finset.sum_div]
      _ ≤ d * 1 := by
        apply mul_le_mul_of_nonneg_left _ hd
        by_cases hB0 : B = 0
        · simp [hB0]
        · apply (div_le_one (lt_of_le_of_ne hB (Ne.symm hB0))).2
          exact sum_colorMass_le p f Z hp b _
      _ = fiberMass p g r := mul_one _
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (∑ x ∈ s, _) ≤ ∑ x ∈ s, p x
    simp [he]

lemma expected_ratio_le (p : α → ℝ) (f g Z : α → ℕ) (hp : ∀ x, 0 ≤ p x)
    (hfg : ∀ x y, g x = g y → f x = f y) :
    ∑ x, p x * (posterior p f Z x / posterior p g Z x) ≤ ∑ x, p x := by
  classical
  calc
    (∑ x, p x * (posterior p f Z x / posterior p g Z x)) =
        ∑ r ∈ Finset.univ.image g, ∑ x ∈ Finset.univ.filter (fun x => g x = r),
          p x * (posterior p f Z x / posterior p g Z x) :=
      (Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_image_of_mem g (Finset.mem_univ x)) _).symm
    _ ≤ ∑ r ∈ Finset.univ.image g, fiberMass p g r :=
      Finset.sum_le_sum (fun r _ => ratio_cell_le p f g Z hp hfg r)
    _ = ∑ x, p x :=
      Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_image_of_mem g (Finset.mem_univ x)) _

lemma max_log_ratio_le (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    max 0 (Real.log (v / u)) ≤ Real.log v - Real.log u + u / v := by
  rw [Real.log_div (ne_of_gt hv) (ne_of_gt hu)]
  apply max_le
  · have h := Real.log_le_sub_one_of_pos (div_pos hu hv)
    rw [Real.log_div (ne_of_gt hu) (ne_of_gt hv)] at h
    linarith
  · linarith [div_pos hu hv]

lemma positive_log_window_le (p : α → ℝ) (f g Z : α → ℕ) (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (hfg : ∀ x y, g x = g y → f x = f y) :
    ∑ x, p x * max 0 (Real.log (posterior p g Z x / posterior p f Z x)) ≤
      entropy p f Z - entropy p g Z + 1 := by
  have hpoint (x : α) :
      p x * max 0 (Real.log (posterior p g Z x / posterior p f Z x)) ≤
        p x * (Real.log (posterior p g Z x) - Real.log (posterior p f Z x) +
          posterior p f Z x / posterior p g Z x) := by
    by_cases hx : p x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_left
        (max_log_ratio_le _ _ (posterior_pos p f Z hp x (lt_of_le_of_ne (hp x) (Ne.symm hx)))
          (posterior_pos p g Z hp x (lt_of_le_of_ne (hp x) (Ne.symm hx)))) (hp x)
  calc
    (∑ x, p x * max 0 (Real.log (posterior p g Z x / posterior p f Z x))) ≤
        ∑ x, p x * (Real.log (posterior p g Z x) - Real.log (posterior p f Z x) +
          posterior p f Z x / posterior p g Z x) := Finset.sum_le_sum (fun x _ => hpoint x)
    _ = entropy p f Z - entropy p g Z +
        ∑ x, p x * (posterior p f Z x / posterior p g Z x) := by
      simp only [entropy, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
    _ ≤ entropy p f Z - entropy p g Z + 1 := by
      have h := expected_ratio_le p f g Z hp hfg
      rw [hp1] at h
      linarith

end Submission.Obl.k4_matching_palette_likelihood
