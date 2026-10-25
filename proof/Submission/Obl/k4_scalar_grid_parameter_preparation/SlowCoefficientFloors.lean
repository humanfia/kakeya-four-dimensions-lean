import Submission.Obl.k4_scalar_grid_parameter_preparation.SequenceDeficiency
import Submission.Obl.k4_scalar_grid_parameter_preparation.FiniteScaleGrid
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

/-! One slowly relaxed deletion gives stable coefficient floors on the original grid. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped Classical BigOperators ENNReal

theorem exists_slow_coefficient_floors {X : Type*} [MeasurableSpace X]
    (N K L : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hL : (∀ k, 1 ≤ L k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, L k ≤ N k ^ ε)
    (W : ℕ → ℕ) (a : X → Fin 5 → ℝ) (ha : Measurable a)
    (θ : (k : ℕ) → Fin (W k) → Measure X)
    (μ : (k : ℕ) → Fin (W k) → Measure (X × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ)
    (A : (k : ℕ) → Fin (W k) → Set (X × ℝ)) (hA : ∀ k g, MeasurableSet (A k g))
    (Γ : ℕ → Finset ℝ) (hΓ : ∀ᶠ k in atTop, ((Γ k).card : ℝ) ≤ L k) (d : ℝ)
    (hpower : ∀ ε R : ℝ, 0 < ε → 1 < R → ∃ κ : ℝ, 0 < κ ∧
      ∀ᶠ k in atTop, ∀ (g : Fin (W k)) (r : ℝ), R⁻¹ ≤ r → r ≤ R → r ∈ Γ k →
        μ k g {z | z ∈ A k g ∧
          z.1 ∈ scalarLightCoefficientSet (θ k g) a (π k g) (N k ^ (-r)) d (N k ^ (-ε))} ≤
            ENNReal.ofReal (N k ^ (-κ))) :
    ∃ (H : ℕ → ℝ) (J : ℕ → ℕ) (Ξ : ℕ → Finset ℝ)
      (B : (k : ℕ) → Fin (W k) → Set (X × ℝ)),
      ((∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      (∀ k, 2 ≤ J k) ∧ Tendsto J atTop atTop ∧
      (∀ k, Ξ k = (Γ k).filter (fun r => ((J k : ℝ)⁻¹ ≤ r ∧ r ≤ J k))) ∧
      (∀ k g, MeasurableSet (B k g) ∧ B k g ⊆ A k g) ∧
      (∀ᶠ k in atTop, ∀ g, μ k g (A k g \ B k g) ≤ ENNReal.ofReal (1 / (100 * K k))) ∧
      (∀ k g, ∀ r ∈ Ξ k, ∀ z ∈ B k g,
        ENNReal.ofReal (N k ^ (-((1 + d) * r)) / H k) *
          π k g (scalarVelocityBin (N k ^ (-r)) ⌊a z.1 1 / N k ^ (-r)⌋) ≤
          θ k g {l | scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a l) =
            scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a z.1)}) ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ r : ℝ,
        R⁻¹ ≤ r → r ≤ R → r ∈ Γ k → r ∈ Ξ k := by
  classical
  let Q := fun k => max (K k) (L k)
  have hQ := Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hK hL
  have hN₁ (k) : 1 ≤ N k := by linarith [hN k]
  have hNp (k) : 0 < N k := by linarith [hN k]
  have hKp (k) : 0 < K k := zero_lt_one.trans_le (hK.1 k)
  have hLp (k) : 0 < L k := zero_lt_one.trans_le (hL.1 k)
  let stage := fun j : ℕ => j + 2
  let P : ℕ → ℕ → Prop := fun j k =>
    ∀ (g : Fin (W k)) (r : ℝ), ((stage j : ℝ)⁻¹) ≤ r → r ≤ stage j → r ∈ Γ k →
      μ k g {z | z ∈ A k g ∧ z.1 ∈ scalarLightCoefficientSet (θ k g) a (π k g)
        (N k ^ (-r)) d (N k ^ (-(1 / (stage j : ℝ))))} ≤
          ENNReal.ofReal (1 / (100 * K k * L k))
  have hP (j : ℕ) : ∀ᶠ k in atTop, P j k := by
    have hj : (1 : ℝ) < stage j := by dsimp only [stage]; exact_mod_cast (by omega : 1 < j + 2)
    obtain ⟨κ,hκ,hsmall⟩ := hpower (1 / (stage j : ℝ)) (stage j) (by positivity) hj
    have hc := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN₁ hNt hQ.1 hQ.2 2 (a := 0) (b := κ) hκ (A := 100) (by norm_num)
    filter_upwards [hsmall,hc] with k hk hc
    have hprod : 100 * K k * L k ≤ N k ^ κ := by
      calc
        _ = 100 * (K k * L k) := by ring
        _ ≤ 100 * (Q k * Q k) := mul_le_mul_of_nonneg_left
          (mul_le_mul (le_max_left _ _) (le_max_right _ _) (hLp k).le
            (zero_le_one.trans (hQ.1 k))) (by norm_num)
        _ = 100 * Q k ^ 2 := by ring
        _ ≤ N k ^ κ := by simpa only [Real.rpow_zero,mul_one] using hc.le
    have hcost : N k ^ (-κ) ≤ 1 / (100 * K k * L k) := by
      rw [Real.rpow_neg (hNp k).le,← one_div]
      exact one_div_le_one_div_of_le (by
        have hKk := hKp k
        have hLk := hLp k
        positivity) hprod
    intro g r hr hr' hrΓ
    exact (hk g r hr hr' hrΓ).trans (ENNReal.ofReal_le_ofReal hcost)
  obtain ⟨m,hm,hmt,hmn,hdiag⟩ := Submission.Lib.K4ModelReduction.exists_slow_diagonal P hP
  let J := fun k => stage (m k)
  let H := fun k => N k ^ (1 / (J k : ℝ))
  let Ξ := fun k => (Γ k).filter (fun r => (J k : ℝ)⁻¹ ≤ r ∧ r ≤ J k)
  let bad : (k : ℕ) → Fin (W k) → ℝ → Set (X × ℝ) := fun k g r => {z : X × ℝ | z.1 ∈
    scalarLightCoefficientSet (θ k g) a (π k g) (N k ^ (-r)) d (N k ^ (-(1 / (J k : ℝ))))}
  let B := fun k g => A k g \ ⋃ r ∈ Ξ k, bad k g r
  have hJ₂ (k) : 2 ≤ J k := by dsimp only [J,stage]; omega
  have hJp (k) : (0 : ℝ) < J k := by exact_mod_cast (by have hh := hJ₂ k; omega : 0 < J k)
  have hJt : Tendsto J atTop atTop := (tendsto_add_atTop_nat 2).comp hmt
  have hJrt : Tendsto (fun k => (J k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hJt
  have hB (k) (g : Fin (W k)) : MeasurableSet (B k g) ∧ B k g ⊆ A k g := by
    refine ⟨(hA k g).diff ?_,Set.sdiff_subset⟩
    exact MeasurableSet.biUnion (Ξ k).countable_toSet (fun r _ =>
      (measurableSet_scalarLightCoefficientSet (θ k g) a ha (π k g) _ d _).preimage measurable_fst)
  refine ⟨H,J,Ξ,B,⟨fun k => Real.one_le_rpow (hN₁ k) (by positivity),?_⟩,
    hJ₂,hJt,fun _ => rfl,hB,?_,?_,?_⟩
  · exact fun ε hε => eventually_scale_rounding_loss_le N J hN₁ hJt hε
  · filter_upwards [hΓ,hdiag] with k hcard hk
    intro g
    have hcost (r) (hr : r ∈ Ξ k) :
        μ k g {z | z ∈ A k g ∧ z ∈ bad k g r} ≤ ENNReal.ofReal (1 / (100 * K k * L k)) := by
      obtain ⟨hrΓ,hr,hr'⟩ := Finset.mem_filter.mp hr
      exact hk (m k) le_rfl g r hr hr' hrΓ
    have hcover : A k g \ B k g ⊆ ⋃ r ∈ Ξ k, {z | z ∈ A k g ∧ z ∈ bad k g r} := by
      intro z hz
      have hzbad : z ∈ ⋃ r ∈ Ξ k, bad k g r := by
        by_contra hh
        exact hz.2 ⟨hz.1,hh⟩
      obtain ⟨r,hr,hzr⟩ := Set.mem_iUnion₂.mp hzbad
      exact Set.mem_iUnion₂.mpr ⟨r,hr,hz.1,hzr⟩
    have hnum : ((Ξ k).card : ℝ) ≤ L k :=
      (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans hcard
    calc
      _ ≤ ∑ r ∈ Ξ k, μ k g {z | z ∈ A k g ∧ z ∈ bad k g r} :=
        (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
      _ ≤ ∑ _r ∈ Ξ k, ENNReal.ofReal (1 / (100 * K k * L k)) := Finset.sum_le_sum hcost
      _ = ENNReal.ofReal (((Ξ k).card : ℝ) * (1 / (100 * K k * L k))) := by
        simp only [Finset.sum_const,nsmul_eq_mul,← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg (Ξ k).card)]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ L k * (1 / (100 * K k * L k)) :=
            mul_le_mul_of_nonneg_right hnum (by
              have hKk := hKp k
              have hLk := hLp k
              positivity)
          _ = _ := by field_simp [(hKp k).ne',(hLp k).ne']
  · intro k g r hr z hz
    have hnot : z.1 ∉ scalarLightCoefficientSet (θ k g) a (π k g) (N k ^ (-r)) d
        (N k ^ (-(1 / (J k : ℝ)))) := by
      intro hh
      exact hz.2 (Set.mem_iUnion₂.mpr ⟨r,hr,hh⟩)
    have hh : ENNReal.ofReal ((N k ^ (-r)) ^ (1 + d) * N k ^ (-(1 / (J k : ℝ)))) *
        π k g (scalarVelocityBin (N k ^ (-r)) ⌊a z.1 1 / N k ^ (-r)⌋) ≤
        θ k g {l | scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a l) =
          scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a z.1)} := by
      apply le_of_not_gt
      intro hlt
      exact hnot hlt
    have heq : (N k ^ (-r)) ^ (1 + d) = N k ^ (-((1 + d) * r)) := by
      rw [← Real.rpow_mul (hNp k).le]
      congr 1
      ring
    rw [heq] at hh
    simpa only [Real.rpow_neg (hNp k).le,H,div_eq_mul_inv] using hh
  · intro R hR
    filter_upwards [hJrt.eventually_ge_atTop R] with k hk r hr hr' hrΓ
    apply Finset.mem_filter.mpr
    refine ⟨hrΓ,?_,hr'.trans hk⟩
    exact (show (J k : ℝ)⁻¹ ≤ R⁻¹ by
      simpa only [one_div] using one_div_le_one_div_of_le (by linarith : 0 < R) hk).trans hr

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
