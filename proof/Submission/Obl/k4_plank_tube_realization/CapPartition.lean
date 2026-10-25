import Submission.Obl.k4_plank_tube_realization.ConvexVolume

namespace Submission.Obl.k4_plank_tube_realization.ConvexGeometry

open Set MeasureTheory

noncomputable section

/-- Interpolation preserves an absolute-value bound. -/
theorem abs_interpolation_le {x y R t : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R)
    (ht : t ∈ Icc (0 : ℝ) 1) : |(1 - t) * x + t * y| ≤ R := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  calc
    |(1 - t) * x + t * y| ≤ |(1 - t) * x| + |t * y| := abs_add_le _ _
    _ = (1 - t) * |x| + t * |y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg ht1]
    _ ≤ (1 - t) * R + t * R := add_le_add
      (mul_le_mul_of_nonneg_left hx ht1) (mul_le_mul_of_nonneg_left hy ht0)
    _ = R := by ring

/-- Endpoint bin agreement bounds a whole affine trace difference. -/
theorem trace_bound_of_bins (b u b' u' e : Plane)
    (h0 : ⌊inner ℝ b e⌋ = ⌊inner ℝ b' e⌋)
    (h1 : ⌊inner ℝ (b + u) e⌋ = ⌊inner ℝ (b' + u') e⌋)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |inner ℝ (b + t • u - b' - t • u') e| ≤ 1 := by
  have hz : b + t • u - b' - t • u' =
      (1 - t) • (b - b') + t • ((b + u) - (b' + u')) := by module
  rw [hz, inner_add_left, inner_smul_left, inner_smul_left]
  apply abs_interpolation_le _ _ ht
  · simpa only [inner_sub_left] using (Int.abs_sub_lt_one_of_floor_eq_floor h0).le
  · simpa only [inner_sub_left] using (Int.abs_sub_lt_one_of_floor_eq_floor h1).le

/-- Two traces in the same centered rectangle differ by twice its width. -/
theorem trace_bound_of_rectangle (b u b' u' c w e : Plane) {a t : ℝ}
    (h : |inner ℝ (b + t • u - c - t • w) e| ≤ a)
    (h' : |inner ℝ (b' + t • u' - c - t • w) e| ≤ a) :
    |inner ℝ (b + t • u - b' - t • u') e| ≤ 2 * a := by
  have hz : b + t • u - b' - t • u' =
      (b + t • u - c - t • w) - (b' + t • u' - c - t • w) := by module
  rw [hz, inner_sub_left]
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  obtain ⟨hlo', hhi'⟩ := abs_le.mp h'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem floor_mem_five {z : ℝ} (hz : |z| ≤ 2) : ⌊z⌋ ∈ Finset.Icc (-2 : ℤ) 2 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hz
  apply Finset.mem_Icc.mpr
  constructor
  · exact Int.le_floor.mpr (by norm_num; exact hlo)
  · have h := Int.floor_mono hhi
    norm_num at h
    exact h

/-- A bounded affine family in a full-time rectangle obeys its area cap,
including widths outside the cap's permitted range. -/
theorem plank_bound_of_rectangle {D n : ℕ} (hD : 1 ≤ D)
    (b u : Fin n → Plane) (ω : Fin n → ℝ) {A : ℝ} (hA : 0 < A)
    (hbu : ∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1)
    (hcap : ∀ (c w e₁ e₂ : Plane) (a β : ℝ),
      ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 →
      1 ≤ a → a ≤ β → β ≤ (D : ℝ) → ∀ S : Finset (Fin n),
      (∀ i ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
        |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a / (D : ℝ) ∧
        |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ)) →
      ∑ i ∈ S, ω i ≤ A * a * β)
    (S : Finset (Fin n)) (c w e₁ e₂ : Plane) {a β : ℝ}
    (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1) (he12 : inner ℝ e₁ e₂ = 0)
    (ha : 1 / (2 * (D : ℝ)) ≤ a) (hab : a ≤ β)
    (hrect : ∀ i ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a ∧
      |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β) :
    ∑ i ∈ S, ω i ≤ 2500 * A * (D : ℝ)^2 * a * β := by
  classical
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hbpos : 0 < β := hapos.trans_le hab
  have hDa : 1 ≤ 2 * (D : ℝ) * a := by
    have hh := (div_le_iff₀ (show 0 < 2 * (D : ℝ) by positivity)).mp ha
    nlinarith
  let α : ℝ := min (D : ℝ) (2 * (D : ℝ) * a)
  let γ : ℝ := min (D : ℝ) (2 * (D : ℝ) * β)
  have hα : 1 ≤ α := le_min hD' hDa
  have hαγ : α ≤ γ := min_le_min le_rfl (by nlinarith)
  have hγD : γ ≤ D := min_le_left _ _
  let bins : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-2 : ℤ) 2
  let tag : Fin n → Fin 4 → ℤ := fun i =>
    ![⌊inner ℝ (b i) e₁⌋, ⌊inner ℝ (b i + u i) e₁⌋,
      ⌊inner ℝ (b i) e₂⌋, ⌊inner ℝ (b i + u i) e₂⌋]
  have hend : ∀ i (e : Plane), ‖e‖ = 1 →
      |inner ℝ (b i) e| ≤ 2 ∧ |inner ℝ (b i + u i) e| ≤ 2 := by
    intro i e he
    have h0 := abs_real_inner_le_norm (b i) e
    have h1 := abs_real_inner_le_norm (b i + u i) e
    rw [he, mul_one] at h0 h1
    exact ⟨h0.trans (by linarith [(hbu i).1]),
      h1.trans (by linarith [norm_add_le (b i) (u i), (hbu i).1, (hbu i).2])⟩
  have htag : ∀ i, tag i ∈ bins := by
    intro i
    apply Fintype.mem_piFinset.mpr
    intro k
    fin_cases k <;> dsimp [tag] <;> apply floor_mem_five
    · exact (hend i e₁ he₁).1
    · exact (hend i e₁ he₁).2
    · exact (hend i e₂ he₂).1
    · exact (hend i e₂ he₂).2
  have hgroup : ∀ z ∈ bins, ∑ i ∈ S with tag i = z, ω i ≤ A * α * γ := by
    intro z hz
    by_cases hne : (S.filter fun i => tag i = z).Nonempty
    · obtain ⟨j, hj⟩ := hne
      obtain ⟨hjS, hjtag⟩ := Finset.mem_filter.mp hj
      apply hcap (b j) (u j) e₁ e₂ α γ he₁ he₂ he12 hα hαγ hγD
      intro i hi t ht
      obtain ⟨hiS, hitag⟩ := Finset.mem_filter.mp hi
      have heq : tag i = tag j := hitag.trans hjtag.symm
      have hbins₁ : |inner ℝ (b i + t • u i - b j - t • u j) e₁| ≤ 1 :=
        trace_bound_of_bins _ _ _ _ _ (by simpa [tag] using congrFun heq 0)
          (by simpa [tag] using congrFun heq 1) ht
      have hbins₂ : |inner ℝ (b i + t • u i - b j - t • u j) e₂| ≤ 1 :=
        trace_bound_of_bins _ _ _ _ _ (by simpa [tag] using congrFun heq 2)
          (by simpa [tag] using congrFun heq 3) ht
      have hsmall₁ := trace_bound_of_rectangle (b i) (u i) (b j) (u j) c w e₁
        (hrect i hiS t ht).1 (hrect j hjS t ht).1
      have hsmall₂ := trace_bound_of_rectangle (b i) (u i) (b j) (u j) c w e₂
        (hrect i hiS t ht).2 (hrect j hjS t ht).2
      constructor
      · apply (le_div_iff₀ hDpos).mpr
        apply le_min
        · nlinarith
        · nlinarith
      · apply (le_div_iff₀ hDpos).mpr
        apply le_min
        · nlinarith
        · nlinarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      exact le_of_lt (mul_pos (mul_pos hA (by linarith)) (by linarith))
  have hcard : bins.card = 625 := by
    simp [bins, Fintype.card_piFinset]
  calc
    ∑ i ∈ S, ω i = ∑ z ∈ bins, ∑ i ∈ S with tag i = z, ω i :=
      (Finset.sum_fiberwise_of_maps_to (fun i _ => htag i) ω).symm
    _ ≤ ∑ _z ∈ bins, A * α * γ := Finset.sum_le_sum hgroup
    _ = 625 * (A * α * γ) := by simp [hcard]
    _ ≤ 2500 * A * (D : ℝ)^2 * a * β := by
      have hαle : α ≤ 2 * (D : ℝ) * a := min_le_right _ _
      have hγle : γ ≤ 2 * (D : ℝ) * β := min_le_right _ _
      have hprod := mul_le_mul hαle hγle (by linarith : 0 ≤ γ)
        (by positivity : 0 ≤ 2 * (D : ℝ) * a)
      calc
        625 * (A * α * γ) = (625 * A) * (α * γ) := by ring
        _ ≤ (625 * A) * ((2 * (D : ℝ) * a) * (2 * (D : ℝ) * β)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = 2500 * A * (D : ℝ)^2 * a * β := by ring


end
end Submission.Obl.k4_plank_tube_realization.ConvexGeometry
