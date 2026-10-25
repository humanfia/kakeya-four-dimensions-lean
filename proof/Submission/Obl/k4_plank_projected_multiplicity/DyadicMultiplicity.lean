import Submission.Obl.k4_plank_projected_multiplicity.ContinuousMultiplicity
import Submission.Obl.k4_plank_projected_multiplicity.ProjectionNormalization

namespace Submission.Obl.k4_plank_projected_multiplicity

open Set Finset MeasureTheory Filter

noncomputable section

/-- The projected crowding estimate in the original graph coordinates and dyadic scale. -/
theorem dyadic_projected_multiplicity_tail (hplank : PlankEstimate) {R α : ℝ}
    (hR : 1 ≤ R) (hα : 0 < α) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ (n : ℕ) (x v : Fin n → E4),
      (∀ i, v i 0 = 1 ∧ ‖v i‖ ≤ 2) →
      (∀ i j, i ≠ j → (2 : ℝ) ^ (-(k : ℤ)) ≤ ‖v i - v j‖) →
      (∀ i, ‖x i‖ ≤ R) →
      (∑ i : Fin n, volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        (2 : ℝ) ^ ((1 + α) * (k : ℝ)) ≤
          (((univ : Finset (Fin n)).filter (fun j =>
            |(x j 1 + t * v j 1) - (x i 1 + t * v i 1)| ≤ (2 : ℝ) ^ (-(k : ℤ)) ∧
            |(x j 2 + t * v j 2) - (x i 2 + t * v i 2)| ≤
              (2 : ℝ) ^ (-(k : ℤ)))).card : ℝ)}) ≤
          ENNReal.ofReal ((n : ℝ) * (2 : ℝ) ^ (-(θ * (k : ℝ)))) := by
  classical
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * R + 4)
  have hLp : 0 < (L : ℝ) := by linarith
  have hLx : 2 * R ≤ (L : ℝ) := by linarith
  have hLv : 4 ≤ (L : ℝ) := by linarith
  have hL₁ : 1 ≤ L := by exact_mod_cast (show (1 : ℝ) ≤ (L : ℝ) by linarith)
  obtain ⟨τ, hτ, D₀, htail⟩ :=
    continuous_projected_multiplicity_tail hplank (a := α / 2) (R := 1) (by positivity) le_rfl
  have hlarge : ∀ᶠ k : ℕ in atTop,
      (L : ℝ) ^ (1 + α / 2) ≤ ((2 : ℝ) ^ k) ^ (α / 2) :=
    ((tendsto_rpow_atTop (show 0 < α / 2 by positivity)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) one_lt_two)).eventually
        (eventually_ge_atTop _)
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp hlarge
  refine ⟨τ, hτ, max k₁ D₀, ?_⟩
  intro k hk n x v hv hsep hx
  let D : ℕ := L * 2 ^ k
  let b : Fin n → E2 := fun i => (L : ℝ)⁻¹ • projectedPart (x i)
  let s : Fin n → E3 := fun i => (L : ℝ)⁻¹ • spatialPart (v i)
  have hDreal : (D : ℝ) = (L : ℝ) * (2 : ℝ) ^ k := by simp [D]
  have hDp : 0 < (D : ℝ) := by rw [hDreal]; positivity
  have hDinv : (D : ℝ)⁻¹ = (L : ℝ)⁻¹ * (2 : ℝ) ^ (-(k : ℤ)) := by
    simp [hDreal, zpow_neg, mul_comm]
  have hkpow : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
  have hDnat : D₀ ≤ D := by
    have hbase : 2 ^ k ≤ D := by
      dsimp [D]
      simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ k) hL₁
    exact ((le_max_right k₁ D₀).trans hk).trans (hkpow.trans hbase)
  have hbase : (2 : ℝ) ^ k ≤ (D : ℝ) := by
    rw [hDreal]
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) k,
      (show (1 : ℝ) ≤ (L : ℝ) by exact_mod_cast hL₁)]
  obtain ⟨hbu, hs⟩ := scaled_family_normalized x v hLp hLx hLv hx (fun i => (hv i).2)
  have hsep' : ∀ i j, i ≠ j → (D : ℝ)⁻¹ ≤ ‖s i - s j‖ := by
    rw [hDinv]
    exact scaled_family_separated v hLp (fun i => (hv i).1) hsep
  have hthreshold : (D : ℝ) ^ (1 + α / 2) ≤
      (2 : ℝ) ^ ((1 + α) * (k : ℝ)) := by
    calc
      (D : ℝ) ^ (1 + α / 2) =
          (L : ℝ) ^ (1 + α / 2) * ((2 : ℝ) ^ k) ^ (1 + α / 2) := by
        rw [hDreal, Real.mul_rpow hLp.le (by positivity)]
      _ ≤ ((2 : ℝ) ^ k) ^ (α / 2) * ((2 : ℝ) ^ k) ^ (1 + α / 2) :=
        mul_le_mul_of_nonneg_right (hk₁ k ((le_max_left k₁ D₀).trans hk)) (by positivity)
      _ = ((2 : ℝ) ^ k) ^ (1 + α) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < 2 ^ k)]
        congr 1
        ring
      _ = (2 : ℝ) ^ ((1 + α) * (k : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  have hcount (i : Fin n) (t : ℝ) :
      (((univ : Finset (Fin n)).filter (fun j =>
        |(x j 1 + t * v j 1) - (x i 1 + t * v i 1)| ≤ (2 : ℝ) ^ (-(k : ℤ)) ∧
        |(x j 2 + t * v j 2) - (x i 2 + t * v i 2)| ≤
          (2 : ℝ) ^ (-(k : ℤ)))).card : ℝ) ≤
        ((nearTraces D b (fun l => planarPart (s l)) i t).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (show
      (univ.filter (fun j =>
        |(x j 1 + t * v j 1) - (x i 1 + t * v i 1)| ≤ (2 : ℝ) ^ (-(k : ℤ)) ∧
        |(x j 2 + t * v j 2) - (x i 2 + t * v i 2)| ≤
          (2 : ℝ) ^ (-(k : ℤ)))) ⊆ nearTraces D b (fun l => planarPart (s l)) i t from by
      intro j hj
      obtain ⟨hj₁, hj₂⟩ := (Finset.mem_filter.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hh := scaled_projected_proximity (x j) (v j) (x i) (v i) hLp hj₁ hj₂
      change ‖(b j + t • planarPart (s j)) - (b i + t • planarPart (s i))‖ ≤ _ at hh
      simpa only [div_eq_mul_inv, hDinv, mul_assoc] using hh)
  have hpower : (D : ℝ) ^ (-τ) ≤ (2 : ℝ) ^ (-(τ * (k : ℝ))) := by
    calc
      (D : ℝ) ^ (-τ) ≤ ((2 : ℝ) ^ k) ^ (-τ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
      _ = (2 : ℝ) ^ (-(τ * (k : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  calc
    _ ≤ ∑ i : Fin n, volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        (D : ℝ) ^ (1 + α / 2) ≤
          ((nearTraces D b (fun l => planarPart (s l)) i t).card : ℝ)} := by
      apply Finset.sum_le_sum
      intro i hi
      exact measure_mono (fun t ht => ⟨ht.1, hthreshold.trans (ht.2.trans (hcount i t))⟩)
    _ ≤ ENNReal.ofReal ((Fintype.card (Fin n) : ℝ) * (D : ℝ) ^ (-τ)) :=
      htail D hDnat b s hbu hs hsep'
    _ ≤ ENNReal.ofReal ((n : ℝ) * (2 : ℝ) ^ (-(τ * (k : ℝ)))) := by
      simp only [Fintype.card_fin]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg _))

end

end Submission.Obl.k4_plank_projected_multiplicity
