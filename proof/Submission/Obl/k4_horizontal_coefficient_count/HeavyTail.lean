import Submission.Obl.k4_horizontal_coefficient_count.Sequence
import Submission.Obl.k4_horizontal_coefficient_count.FiniteCode
import Submission.Obl.k4_horizontal_coefficient_count.GoodSupport
import Submission.Obl.k4_horizontal_coefficient_count.CellsBridge

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set Filter
open scoped ENNReal

/-- A power-decaying light-cell tail gives the analytic heavy-cover input
used by the simultaneous finite-depth selector. -/
theorem heavyCoverAt_of_light_tail {α : Type} [MeasurableSpace α]
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (d e₀ s ε : ℝ) (hε : 0 < ε)
    (ρ : ℕ → Measure (α × ℝ)) (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ)
    (hb : ∀ k, Measurable (b k))
    (htime : ∀ k, ρ k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hgood : ∀ᶠ k in atTop,
      ρ k (Prod.fst ⁻¹' goodSet (b k) (K k) (N k ^ (-e₀)))ᶜ = 0)
    (hlight : ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ρ k (lmLight (ρ k) (π k) (b k) (N k ^ (-e₀)) (N k ^ (-s)) d
        (N k ^ (ε / 2)) (goodSet (b k) (K k) (N k ^ (-e₀))) ×ˢ univ) ≤
          ENNReal.ofReal (N k ^ (-c))) :
    HeavyCoverAt N d e₀ 1 2 s ε ρ π b := by
  have hN1 : ∀ k, 1 ≤ N k := fun k => by linarith [hN k]
  have hC := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hNt hK hsub 1 (a := 0) (b := 2) (by norm_num) (A := 2) (by norm_num)
  have hM := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hNt hK hsub 1 (a := 0) (b := ε) hε (A := 4) (by norm_num)
  obtain ⟨c, hc, hlight⟩ := hlight
  refine ⟨c, hc, ?_⟩
  filter_upwards [hC, hM, hgood, hlight] with k hC hM hgood hlight
  simp only [pow_one, Real.rpow_zero, mul_one] at hC hM
  have hNk : 0 < N k := by linarith [hN k]
  have hKk : 0 ≤ K k := by linarith [hK k]
  let G := goodSet (b k) (K k) (N k ^ (-e₀))
  have hG : MeasurableSet G := measurableSet_goodSet (hb k) _ _
  have hbound := fun l (hl : l ∈ G) => goodSet_coefficient_bound (b k) hKk hl
  have hfinite := finite_horizontalCode (b k) G (χ := N k ^ (-e₀)) (a := N k ^ (-s))
    (Real.rpow_pos_of_pos hNk _) (Real.rpow_pos_of_pos hNk _)
    (by positivity : 0 ≤ 2 * K k) hbound
  obtain ⟨f, hf, herr⟩ := heavy_binned_family (ρ k) (π k) (b k) (hb k) G hG
    (d := d) (Z := N k ^ (ε / 2))
    (Real.rpow_pos_of_pos hNk _) (by positivity : 0 ≤ 2 * K k) hC.le
    (by linarith : 2 * (2 * K k) ≤ N k ^ ε) (by linarith [hK k] : 2 ≤ N k ^ ε)
    (fun l hl => ⟨hbound l hl 2, hbound l hl 5⟩) hfinite (htime k) hgood
  have herr' := herr.trans (by simpa only [lightCells_eq_lmLight, G] using hlight)
  change ∃ f : PredictorFamily (b k) (N k ^ (-e₀)) (N k ^ (-(1 : ℝ) * s))
    (N k ^ (-s)) (N k ^ (2 : ℝ)) (N k ^ ε),
    f.Floors (π k) d (N k ^ (ε / 2)) (ρ k) ∧
      ρ k {p | ∃ i, p.1 ∈ f.A i}ᶜ ≤ ENNReal.ofReal (N k ^ (-c))
  rw [neg_one_mul]
  exact ⟨f, hf, herr'⟩

end Submission.Obl.k4_horizontal_coefficient_count
