import Submission.Obl.k4_scalar_coefficient_clustering.LiftCells
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

namespace Submission.Obl.k4_scalar_coefficient_clustering

open MeasureTheory

noncomputable section

/-- An explicit quantitative form of the lifted-plank argument. -/
theorem clustering_mass_bound {τ η C d p K R H Λ : ℝ}
    (hinput : PlankEstimate τ η C) (hC : 0 < C) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hp : 0 < p) (hK : 2 ≤ K) (hR : 3 * K ≤ R) (hH : 0 ≤ H) (hΛ : 1 ≤ Λ)
    {D : ℕ} (hD : 1 ≤ D) (hlo : R ≤ (D : ℝ) * p) (hhi : (D : ℝ) * p ≤ 2 * R)
    (hdense : (D : ℝ) ^ (1 - η) ≤ (D : ℝ) / K ^ 3)
    {α : Type*} [MeasurableSpace α] (ν : Measure α) {a : α → Coeff} (ha : Measurable a)
    {E : Set (α × ℝ)} (hE : MeasurableSet E) (hunit : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (hB : ∀ l, ‖a l‖ ≤ K) (hν : ν Set.univ ≤ ENNReal.ofReal K)
    (hinc : ENNReal.ofReal (1 / K) ≤ (ν.prod volume) E)
    (F : Finset (ℤ × ℤ))
    (hF : ∀ l t, (l, t) ∈ E → (⌊t / p⌋, ⌊quadratic (a l) t / p⌋) ∈ F)
    (hcap : ∀ b r, p ≤ r → ν {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (K * r ^ d))
    (hbin : ∀ q : Fin 3 → ℤ,
      ν {l | coefficientCode p (a l) = q ∧
        ENNReal.ofReal (1 / K ^ 3) ≤ volume {t : ℝ | (l, t) ∈ E}} ≤ ENNReal.ofReal H) :
    1 / (2 * K ^ 4) ≤ 500000000000 * C * R ^ 3 / (D : ℝ) ^ 2 * (D : ℝ) ^ τ *
      (F.card : ℝ) * (K * (p * Λ) ^ (d - 1) + Λ ^ 3 * H / p) := by
  classical
  have hKpos : 0 < K := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  letI : IsFiniteMeasure ν := ⟨hν.trans_lt ENNReal.ofReal_lt_top⟩
  let δ : ℝ := 1 / K ^ 3
  let G : Set α := {l | ENNReal.ofReal δ ≤ volume {t : ℝ | (l, t) ∈ E}}
  have hG : MeasurableSet G := measurableSet_le measurable_const (measurable_measure_prodMk_left hE)
  have hdiscard : ENNReal.ofReal δ * ν Set.univ ≤ ENNReal.ofReal (1 / (2 * K)) := by
    have hh : δ * K ≤ 1 / (2 * K) := by
      have hrat : 1 / K ^ 2 ≤ 1 / (2 * K) := by
        apply (div_le_div_iff₀ (by positivity : 0 < K ^ 2) (by positivity : 0 < 2 * K)).mpr
        nlinarith
      convert hrat using 1 <;> dsimp [δ] <;> field_simp <;> ring
    calc
      _ ≤ ENNReal.ofReal δ * ENNReal.ofReal K := by gcongr
      _ = ENNReal.ofReal (δ * K) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hh
  have hmass : 1 / (2 * K) ≤ (ν G).toReal := by
    have hh := hinc.trans (incidence_mass_le_long_mass_add ν hE hunit (ENNReal.ofReal δ))
    have hh' : ENNReal.ofReal (1 / (2 * K)) + ENNReal.ofReal (1 / (2 * K)) ≤
        ν G + ENNReal.ofReal (1 / (2 * K)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      have heq : 1 / (2 * K) + 1 / (2 * K) = 1 / K := by ring
      rw [heq]
      exact hh.trans (add_le_add le_rfl hdiscard)
    have hg := ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hh'
    have hreal := ENNReal.toReal_mono (measure_ne_top ν G) hg
    rwa [ENNReal.toReal_ofReal (by positivity)] at hreal
  obtain ⟨n, rep, ω, hrep, hinj, hωpos, hωeq, htotal⟩ :=
    exists_binned_prior ν ha hG hp (fun l _ => hB l)
  let a₀ : Fin n → Coeff := fun i => a (rep i)
  let J₀ : Fin n → Finset (Fin D) := fun i =>
    labeledTimeMarks D a G E p (coefficientCode p (a₀ i))
  have hω : ∀ i, 0 ≤ ω i := fun i => (hωpos i).le
  have hsmall : ∀ i, ω i ≤ H := by
    intro i
    rw [hωeq i]
    have heq : {l | l ∈ G ∧ coefficientCode p (a l) = coefficientCode p (a (rep i))} =
        {l | coefficientCode p (a l) = coefficientCode p (a (rep i)) ∧
          ENNReal.ofReal (1 / K ^ 3) ≤ volume {t : ℝ | (l, t) ∈ E}} := by
      ext l
      exact and_comm
    rw [heq]
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbin (coefficientCode p (a (rep i))))
    simpa only [ENNReal.toReal_ofReal hH] using hh
  have hcluster : ∀ v : ℝ, p ≤ 2 * v → ∀ T : Finset (Fin n),
      (∀ i ∈ T, ∀ j ∈ T, ‖a₀ i - a₀ j‖ ≤ 24 * v) → ∑ i ∈ T, ω i ≤ 32 * K * v ^ d := by
    intro v hv T hT
    have hv0 : 0 < v := by linarith
    have hh := binned_ball_cap ν ha hG hp hKpos.le hv rep ω hinj hωeq hcap T hT
    have hpw : (32 : ℝ) ^ d ≤ 32 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 32) hd1.le
      simpa only [Real.rpow_one] using hh
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) hv0.le] at hh
    nlinarith [mul_le_mul_of_nonneg_right hpw (by positivity : 0 ≤ K * v ^ d)]
  let b : Fin n × Fin D → Plane := fun q => normalizedBase R (a₀ q.1) (((q.2 : ℕ) : ℝ) / (D : ℝ))
  let u : Fin n × Fin D → Plane := fun q => normalizedSlope R (a₀ q.1) (((q.2 : ℕ) : ℝ) / (D : ℝ))
  let w : Fin n × Fin D → ℝ := fun q => ω q.1 / (D : ℝ)
  let J : Fin n × Fin D → Finset (Fin D) := fun q => J₀ q.1
  let A : ℝ := 5000000 * (R / (D : ℝ)) ^ 2 * (K * (p * Λ) ^ (d - 1) + Λ ^ 3 * H / p)
  have hA : 0 < A := by dsimp [A]; positivity
  have hbu : ∀ q, ‖b q‖ ≤ 1 ∧ ‖u q‖ ≤ 1 := by
    intro q
    apply normalized_lift_bounds (hB (rep q.1)) (by linarith) hR
    exact ⟨by positivity, (div_le_one hDpos).mpr (by exact_mod_cast (Nat.le_of_lt q.2.isLt))⟩
  have hJcard : ∀ i, (D : ℝ) * δ ≤ ((J₀ i).card : ℝ) := by
    intro i
    have hl : ENNReal.ofReal δ ≤ volume {t : ℝ | (rep i, t) ∈ E} := hrep i
    have hv := volume_fiber_le_marks hD a G E p hunit (hrep i)
    have hh := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ ((J₀ i).card : ℝ) / (D : ℝ))).mp (hl.trans hv)
    have hh' := (le_div_iff₀ hDpos).mp hh
    nlinarith
  have hcaplift : PlankCap D b u w A := by
    apply lifted_plank_cap hD hR1 hp hKpos.le hH hΛ hd1
    · apply (le_div_iff₀ hDpos).mpr
      linarith
    · exact hω
    · exact hsmall
    · exact hinj
    · exact hcluster
  have hplank := plankEstimate_fintype hinput D hD b u w A J hbu
    (fun q => div_pos (hωpos q.1) hDpos) hA hcaplift (by
      intro q
      exact hdense.trans (by simpa [J, δ, div_eq_mul_inv] using hJcard q.1))
  have hcells : ((markedCells b u J).card : ℝ) ≤ 100000 * R * (D : ℝ) * (F.card : ℝ) := by
    apply marked_normalized_cells_bound hD hp hR1 hhi
      (fun q : Fin n × Fin D => a₀ q.1) (fun q => (((q.2 : ℕ) : ℝ) / (D : ℝ))) J F hbu
    intro q j hj
    exact marked_scalar_support hD hp hR1 hR hlo a G E F hunit (fun l _ => hB l) hF (hrep q.1) hj
  have hsum : (∑ q, w q * ((J q).card : ℝ)) = ∑ i, ω i * ((J₀ i).card : ℝ) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [w, J, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    field_simp
  have hsumlow : (D : ℝ) * δ * (ν G).toReal ≤ ∑ q, w q * ((J q).card : ℝ) := by
    rw [hsum, ← htotal, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [mul_le_mul_of_nonneg_left (hJcard i) (hω i)]
  have hh := hsumlow.trans (hplank.trans (mul_le_mul_of_nonneg_left hcells (by positivity : 0 ≤ C * A * (D : ℝ) ^ τ)))
  have hlower : (D : ℝ) * (1 / (2 * K ^ 4)) ≤ (D : ℝ) * δ * (ν G).toReal := by
    have hm := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ (D : ℝ) * δ)
    convert hm using 1 <;> dsimp [δ] <;> field_simp <;> ring
  have hfinal := hlower.trans hh
  apply (mul_le_mul_iff_right₀ hDpos).mp
  convert hfinal using 1 <;> dsimp [A] <;> field_simp <;> ring

end
end Submission.Obl.k4_scalar_coefficient_clustering
