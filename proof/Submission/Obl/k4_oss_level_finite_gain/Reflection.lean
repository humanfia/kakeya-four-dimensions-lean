import Mathlib

namespace Submission.Obl.k4_oss_level_finite_gain

theorem reflection_injective : Function.Injective (fun x : ℝ => -2 * x) := by
  intro x y h
  linarith

theorem reflected_separated {δ : ℝ} (hδ : 0 ≤ δ) (C : Finset ℝ)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → δ ≤ dist x y) :
    ∀ x ∈ C.image (fun c => -2 * c), ∀ y ∈ C.image (fun c => -2 * c),
      x ≠ y → δ ≤ dist x y := by
  classical
  intro x hx y hy hxy
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hy
  have hh := hsep c hc c' hc' (fun hh => hxy (congrArg (fun c : ℝ => -2 * c) hh))
  have he : dist (-2 * c) (-2 * c') = 2 * dist c c' := by
    simp only [Real.dist_eq]
    rw [show -2 * c - -2 * c' = -2 * (c - c') by ring, abs_mul]
    norm_num
  rw [he]
  linarith

/-- Reflection and dilation by two do not worsen a uniform ball-counting cap. -/
theorem reflected_filter_card_le (C : Finset ℝ) (x u : ℝ) (hu : 0 ≤ u) :
    ((C.image (fun c => -2 * c)).filter (fun b => dist b x ≤ u)).card ≤
      (C.filter (fun c => dist c (-x / 2) ≤ u)).card := by
  classical
  rw [Finset.filter_image, Finset.card_image_of_injective _ reflection_injective]
  apply Finset.card_le_card
  intro c hc
  obtain ⟨hc, hh⟩ := Finset.mem_filter.mp hc
  refine Finset.mem_filter.mpr ⟨hc, ?_⟩
  rw [Real.dist_eq] at hh ⊢
  obtain ⟨hl, hr⟩ := abs_le.mp hh
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The reflected product is in bijection with the original mixed-energy count. -/
theorem reflected_energy_card (A C : Finset ℝ) (δ t : ℝ) :
    ((((A.product (C.image (fun c => -2 * c))).product
        (A.product (C.image (fun c => -2 * c)))).filter
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card) =
    ((((A.product C).product (A.product C)).filter
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        |(q.1.1 - 2 * t * q.1.2) - (q.2.1 - 2 * t * q.2.2)| ≤ 16 * δ)).card) := by
  classical
  symm
  apply Finset.card_bij
    (fun q _ => ((q.1.1, -2 * q.1.2), (q.2.1, -2 * q.2.2)))
  · rintro ⟨⟨x, y⟩, ⟨z, w⟩⟩ hq
    obtain ⟨hm, hh⟩ := Finset.mem_filter.mp hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hm
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp h1
    obtain ⟨hz, hw⟩ := Finset.mem_product.mp h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_image_of_mem _ hy⟩,
       Finset.mem_product.mpr ⟨hz, Finset.mem_image_of_mem _ hw⟩⟩, ?_⟩
    convert hh using 1
    congr 1
    ring
  · rintro ⟨⟨x, y⟩, ⟨z, w⟩⟩ hq ⟨⟨x', y'⟩, ⟨z', w'⟩⟩ hq' he
    have hh := Prod.mk.inj he
    have hh1 := Prod.mk.inj hh.1
    have hh2 := Prod.mk.inj hh.2
    have hy : y = y' := reflection_injective hh1.2
    have hw : w = w' := reflection_injective hh2.2
    exact Prod.ext (Prod.ext hh1.1 hy) (Prod.ext hh2.1 hw)
  · rintro ⟨⟨x, y⟩, ⟨z, w⟩⟩ hq
    obtain ⟨hm, hh⟩ := Finset.mem_filter.mp hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hm
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp h1
    obtain ⟨hz, hw⟩ := Finset.mem_product.mp h2
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    refine ⟨((x, y'), (z, w')), ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hx, hy'⟩, Finset.mem_product.mpr ⟨hz, hw'⟩⟩, ?_⟩
    convert hh using 1
    congr 1
    ring

end Submission.Obl.k4_oss_level_finite_gain
