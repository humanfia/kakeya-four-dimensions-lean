import Mathlib

/-!
# Fourfold projected-collision transfer for `k4_oss_grid_rounding`

Generic in a measurable rounding map `R` with `|R x - x| ≤ δ / 2`, a finset `F` holding
`R x` for `α`-almost every `x`, and the cell weights `p y = α.real (R ⁻¹' {y})`: the averaged
radius-`4δ` projected collision of `α` is at most the averaged radius-`7δ` weighted count.
-/

open MeasureTheory

namespace Submission.Obl.k4_oss_grid_rounding

/-- Rounding of a quadruple `((x₁, x₂), (x₃, x₄))`, coordinatewise by `R`, reordered to
`((R x₁, R x₃), (R x₂, R x₄))`: the order of the finite count in `k4_oss_grid_rounding`. -/
def quadRound (R : ℝ → ℝ) (x : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((R x.1.1, R x.2.1), (R x.1.2, R x.2.2))

theorem measurable_quadRound {R : ℝ → ℝ} (hR : Measurable R) : Measurable (quadRound R) := by
  unfold quadRound
  fun_prop

theorem quadRound_preimage_singleton (R : ℝ → ℝ) (y : (ℝ × ℝ) × (ℝ × ℝ)) :
    quadRound R ⁻¹' {y} =
      ((R ⁻¹' {y.1.1}) ×ˢ (R ⁻¹' {y.2.1})) ×ˢ ((R ⁻¹' {y.1.2}) ×ˢ (R ⁻¹' {y.2.2})) := by
  ext x
  simp only [quadRound, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Prod.ext_iff]
  tauto

/-- The rounding of a point of the `4δ` event lies in the `7δ` event, when `|t| ≤ 1`. -/
theorem round_event {δ t : ℝ} (R : ℝ → ℝ) (hdist : ∀ x, |R x - x| ≤ δ / 2) (ht : |t| ≤ 1)
    (x : (ℝ × ℝ) × (ℝ × ℝ)) (hx : |(x.1.1 - x.1.2) - 2 * t * (x.2.1 - x.2.2)| ≤ 4 * δ) :
    |((quadRound R x).1.1 - 2 * t * (quadRound R x).1.2) -
        ((quadRound R x).2.1 - 2 * t * (quadRound R x).2.2)| ≤ 7 * δ := by
  simp only [quadRound]
  have hmul : ∀ y, |t * (R y - y)| ≤ δ / 2 := fun y => by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht).trans (hdist y)
  have k1 := abs_le.mp (hdist x.1.1)
  have k2 := abs_le.mp (hdist x.1.2)
  have k3 := abs_le.mp (hmul x.2.1)
  have k4 := abs_le.mp (hmul x.2.2)
  have k0 := abs_le.mp hx
  rw [abs_le]
  constructor <;> nlinarith [k1.1, k1.2, k2.1, k2.2, k3.1, k3.2, k4.1, k4.2, k0.1, k0.2]

/-- Pointwise transfer of the projected collision at a fixed slope `t` with `|t| ≤ 1`. -/
theorem fourfold_transfer_pt (α : Measure ℝ) [IsFiniteMeasure α] {δ : ℝ} (R : ℝ → ℝ)
    (hR : Measurable R) (F : Finset ℝ) (hRF : ∀ᵐ x ∂α, R x ∈ F)
    (hdist : ∀ x, |R x - x| ≤ δ / 2) (p : ℝ → ℝ) (hp : ∀ y ∈ F, p y = α.real (R ⁻¹' {y}))
    {t : ℝ} (ht : |t| ≤ 1) :
    ((α.prod α).prod (α.prod α))
        {q : (ℝ × ℝ) × (ℝ × ℝ) | |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ} ≤
      Finset.sum (((F.product F).product (F.product F)).filter
          (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |(q.1.1 - 2 * t * q.1.2) - (q.2.1 - 2 * t * q.2.2)| ≤ 7 * δ))
        (fun q => ENNReal.ofReal (p q.1.1 * p q.1.2 * p q.2.1 * p q.2.2)) := by
  set S := ((F.product F).product (F.product F)).filter
    (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |(q.1.1 - 2 * t * q.1.2) - (q.2.1 - 2 * t * q.2.2)| ≤ 7 * δ)
    with hS
  set μ := (α.prod α).prod (α.prod α) with hμ
  have h1 : ∀ᵐ x ∂(α.prod α), R x.1 ∈ F := Measure.quasiMeasurePreserving_fst.ae hRF
  have h2 : ∀ᵐ x ∂(α.prod α), R x.2 ∈ F := Measure.quasiMeasurePreserving_snd.ae hRF
  have hae : ∀ᵐ x ∂μ, R x.1.1 ∈ F ∧ R x.1.2 ∈ F ∧ R x.2.1 ∈ F ∧ R x.2.2 ∈ F := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1,
      Measure.quasiMeasurePreserving_fst.ae h2, Measure.quasiMeasurePreserving_snd.ae h1,
      Measure.quasiMeasurePreserving_snd.ae h2] with x a b c d
    exact ⟨a, b, c, d⟩
  have hsub : {q : (ℝ × ℝ) × (ℝ × ℝ) | |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ}
      ≤ᵐ[μ] quadRound R ⁻¹' (S : Set ((ℝ × ℝ) × (ℝ × ℝ))) := by
    filter_upwards [hae] with x hx hxE
    have hxE' : |(x.1.1 - x.1.2) - 2 * t * (x.2.1 - x.2.2)| ≤ 4 * δ := hxE
    show quadRound R x ∈ S
    rw [hS, Finset.mem_filter]
    refine ⟨?_, round_event R hdist ht x hxE'⟩
    simp only [quadRound, Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨⟨hx.1, hx.2.2.1⟩, hx.2.1, hx.2.2.2⟩
  calc μ {q : (ℝ × ℝ) × (ℝ × ℝ) | |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ}
      ≤ μ (quadRound R ⁻¹' (S : Set ((ℝ × ℝ) × (ℝ × ℝ)))) := measure_mono_ae hsub
    _ = ∑ y ∈ S, μ (quadRound R ⁻¹' {y}) :=
        (sum_measure_preimage_singleton S
          (fun y _ => measurable_quadRound hR (measurableSet_singleton y))).symm
    _ = ∑ y ∈ S, ENNReal.ofReal (p y.1.1 * p y.1.2 * p y.2.1 * p y.2.2) := by
        refine Finset.sum_congr rfl (fun y hy => ?_)
        have hyF : (y.1.1 ∈ F ∧ y.1.2 ∈ F) ∧ y.2.1 ∈ F ∧ y.2.2 ∈ F := by
          have := (Finset.mem_filter.mp hy).1
          simpa only [Finset.product_eq_sprod, Finset.mem_product] using this
        rw [quadRound_preimage_singleton, hμ, Measure.prod_prod, Measure.prod_prod,
          Measure.prod_prod, hp _ hyF.1.1, hp _ hyF.1.2, hp _ hyF.2.1, hp _ hyF.2.2]
        simp only [measureReal_def]
        rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul, ← ENNReal.toReal_mul,
          ENNReal.ofReal_toReal (by finiteness)]
        ring

/-- The projected collision of `α` at radius `4δ`, averaged over a direction law `ν`
supported in `[1/4, 1]`, is at most the averaged radius-`7δ` weighted count of the
rounded weights. -/
theorem fourfold_transfer (α : Measure ℝ) [IsFiniteMeasure α] {δ : ℝ} (R : ℝ → ℝ)
    (hR : Measurable R) (F : Finset ℝ) (hRF : ∀ᵐ x ∂α, R x ∈ F)
    (hdist : ∀ x, |R x - x| ≤ δ / 2) (p : ℝ → ℝ) (hp : ∀ y ∈ F, p y = α.real (R ⁻¹' {y}))
    (ν : Measure ℝ) (hν : ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0) :
    MeasureTheory.lintegral ν (fun t : ℝ => ((α.prod α).prod (α.prod α)) {q : (ℝ × ℝ) × (ℝ × ℝ) | |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ}) ≤ MeasureTheory.lintegral ν (fun t : ℝ => Finset.sum (((F.product F).product (F.product F)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |(q.1.1 - 2 * t * q.1.2) - (q.2.1 - 2 * t * q.2.2)| ≤ 7 * δ)) (fun q => ENNReal.ofReal (p q.1.1 * p q.1.2 * p q.2.1 * p q.2.2))) := by
  apply lintegral_mono_ae
  have hν' : ∀ᵐ t ∂ν, t ∈ Set.Icc (1 / 4 : ℝ) 1 := ae_iff.mpr hν
  filter_upwards [hν'] with t ht
  exact fourfold_transfer_pt α R hR F hRF hdist p hp
    (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)

end Submission.Obl.k4_oss_grid_rounding
