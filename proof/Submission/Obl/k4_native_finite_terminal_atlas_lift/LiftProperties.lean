/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/LiftProperties.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftAtlas
import Submission.Obl.k4_native_finite_terminal_atlas_lift.AssignmentComposition
import Submission.Obl.k4_native_finite_terminal_atlas_lift.MassCalibration

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

open MeasureTheory Set

/-- Probability of each original world is part of the literal frozen problem. -/
theorem Data.Valid.probability {p : Data} (hp : p.Valid) (k : ℕ) (γ : Fin (p.W k)) :
    IsProbabilityMeasure (p.ν k γ) := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, hfmt, _⟩
  obtain ⟨M, D, hfmt⟩ := hfmt
  exact ((hfmt k).2.2.2.1 γ).1

theorem Data.Valid.weight_nonneg {p : Data} (hp : p.Valid) (k : ℕ) (γ : Fin (p.W k)) :
    0 ≤ p.ω k γ := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, hfmt, _⟩
  obtain ⟨M, D, hfmt⟩ := hfmt
  exact (hfmt k).2.1 γ

theorem Data.Valid.derivative_unit_pos {p : Data} (hp : p.Valid) (k : ℕ) (γ : Fin (p.W k)) :
    0 < p.B k γ := by
  rcases hp with ⟨_, _, _, _, _, _, _, _, hfmt, _⟩
  obtain ⟨M, D, hfmt⟩ := hfmt
  exact ((hfmt k).2.2.2.1 γ).2.1

namespace Remainder

variable {p q : Data} {r h w : ℝ} (rem : Remainder p q r h w)

theorem liftAtlas_separated {k : ℕ} {a : Atlas q k} (ha : a.Separated) :
    (rem.liftAtlas k a).Separated := by
  apply composite_assignments_separated
    (fun b => (rem.parent k).γ (rem.parentIndex k b))
    (fun b => (rem.parent k).j (rem.parentIndex k b))
    (fun b => (rem.parent k).A (rem.parentIndex k b))
    (fun b => rem.coefficient_map k b) a.γ a.j a.A
  · intro b b' hbb hγ hj
    apply (rem.parent_valid k).2.1 _ _ _ hγ hj
    exact fun he => hbb ((rem.worlds k).injective he)
  · exact ha

/-- Each composed incidence still lies in its actual retained parent set. -/
theorem liftAtlas_F_subset_parent {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (b : Fin a.C) :
    (rem.liftAtlas k a).F b ⊆ (rem.parent k).F (rem.parentIndex k (a.γ b)) := by
  intro z hz
  let e := normalizedIncidenceEquiv (rem.coefficient_map k (a.γ b))
    (rem.initialTime k (a.γ b)) (rem.timeLength k) (rem.timeLength_pos k).ne'
  have hz' : e z ∈ a.F b := hz
  have hc := ha.2.2.1 b
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, hinc, _⟩
  have hnew : e z ∈ q.E k (a.γ b) := (hinc _ hz').1
  have hold := rem.selected_pullback_equiv k (a.γ b) hnew
  change e.symm (e z) ∈ _ at hold
  simpa only [MeasurableEquiv.symm_apply_apply] using hold

theorem liftAtlas_F_subset_assignment {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (b : Fin a.C) :
    (rem.liftAtlas k a).F b ⊆
      (rem.parent k).A (rem.parentIndex k (a.γ b)) ×ˢ (univ : Set ℝ) := by
  intro z hz
  have hp := (rem.parent_valid k).2.2 (rem.parentIndex k (a.γ b))
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, hinc, _⟩
  exact ⟨(hinc z (rem.liftAtlas_F_subset_parent ha b hz)).2.1, Set.mem_univ _⟩

theorem liftAtlas_F_measurable {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (b : Fin a.C) : MeasurableSet ((rem.liftAtlas k a).F b) := by
  have hc := ha.2.2.1 b
  rcases hc with ⟨_, _, _, _, _, _, _, hF, _⟩
  exact (normalizedIncidenceEquiv (rem.coefficient_map k (a.γ b))
    (rem.initialTime k (a.γ b)) (rem.timeLength k) (rem.timeLength_pos k).ne').measurable hF

/-- Exact original within-world product mass of a composed child. -/
theorem liftAtlas_chart_mass (hp : p.Valid) {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (b : Fin a.C) :
    ((p.ν (rem.φ k) ((rem.liftAtlas k a).γ b)).prod volume) ((rem.liftAtlas k a).F b) =
      (ENNReal.ofReal (rem.timeLength k) *
        p.ν (rem.φ k) ((rem.parent k).γ (rem.parentIndex k (a.γ b)))
          ((rem.parent k).A (rem.parentIndex k (a.γ b)))) *
        ((q.ν k (a.γ b)).prod volume) (a.F b) := by
  let i := rem.parentIndex k (a.γ b)
  let ν := p.ν (rem.φ k) ((rem.parent k).γ i)
  let A := (rem.parent k).A i
  letI : IsProbabilityMeasure ν := hp.probability _ _
  have hparent := (rem.parent_valid k).2.2 i
  rcases hparent with ⟨_, _, _, _, _, _, hA, _⟩
  have hchild := ha.2.2.1 b
  rcases hchild with ⟨_, _, _, _, _, _, _, hF, _⟩
  have h := assigned_product_pullback ν A hA (ne_of_gt (rem.prior_pos k (a.γ b)))
    (measure_ne_top ν A) (rem.coefficient_map k (a.γ b)) (rem.initialTime k (a.γ b))
    (rem.timeLength k) (rem.timeLength_pos k) (a.F b) hF
  have hνnew : q.ν k (a.γ b) =
      Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior ν A
        (rem.coefficient_map k (a.γ b)) := rem.conditioned_prior k (a.γ b)
  rw [← hνnew] at h
  have hsub := rem.liftAtlas_F_subset_assignment ha b
  have heq : (A ×ˢ (univ : Set ℝ)) ∩ (rem.liftAtlas k a).F b =
      (rem.liftAtlas k a).F b := inter_eq_right.mpr hsub
  change (ν.prod volume) ((A ×ˢ univ) ∩ (rem.liftAtlas k a).F b) = _ at h
  rw [heq] at h
  exact h

/-- The ordinary prior mass is finite, so its ENNReal factor can be written
as the `ofReal` scalar appearing in the terminal calibration. -/
theorem liftAtlas_chart_mass_real (hp : p.Valid) {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (b : Fin a.C) :
    ((p.ν (rem.φ k) ((rem.liftAtlas k a).γ b)).prod volume) ((rem.liftAtlas k a).F b) =
      ENNReal.ofReal ((rem.timeLength k) *
        (p.ν (rem.φ k) ((rem.parent k).γ (rem.parentIndex k (a.γ b)))
          ((rem.parent k).A (rem.parentIndex k (a.γ b)))).toReal) *
        ((q.ν k (a.γ b)).prod volume) (a.F b) := by
  rw [rem.liftAtlas_chart_mass hp ha b, ENNReal.ofReal_mul (rem.timeLength_pos k).le]
  let ν := p.ν (rem.φ k) ((rem.parent k).γ (rem.parentIndex k (a.γ b)))
  letI : IsProbabilityMeasure ν := hp.probability _ _
  rw [ENNReal.ofReal_toReal (measure_ne_top ν _)]

/-- Restoring the original world weight leaves exactly the common mixture
normalizer, regardless of the individual full assignment prior mass. -/
theorem liftAtlas_weighted_chart_mass (hp : p.Valid) {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (b : Fin a.C) :
    ENNReal.ofReal (p.ω (rem.φ k) ((rem.liftAtlas k a).γ b)) *
      ((p.ν (rem.φ k) ((rem.liftAtlas k a).γ b)).prod volume) ((rem.liftAtlas k a).F b) =
      ENNReal.ofReal (rem.Z k) * (ENNReal.ofReal (q.ω k (a.γ b)) *
        ((q.ν k (a.γ b)).prod volume) (a.F b)) := by
  rw [rem.liftAtlas_chart_mass_real hp ha b]
  apply weighted_conditional_mass (hp.weight_nonneg _ _) (rem.normalizer_pos k)
  simpa only [timeLength, parentIndex, liftAtlas, div_eq_mul_inv, mul_assoc] using rem.world_weights k (a.γ b)

theorem liftAtlas_mass (hp : p.Valid) {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) :
    (rem.liftAtlas k a).mass = ENNReal.ofReal (rem.Z k) * a.mass := by
  unfold Atlas.mass
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => rem.liftAtlas_weighted_chart_mass hp ha b

theorem liftAtlas_coverage (hp : p.Valid) {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (hκ : 1 ≤ a.κ) :
    ENNReal.ofReal (rem.liftAtlas k a).κ⁻¹ ≤ (rem.liftAtlas k a).mass := by
  have hκp : 0 < (rem.parent k).κ := lt_of_lt_of_le zero_lt_one (rem.slack_one k)
  have hκa : 0 < a.κ := lt_of_lt_of_le zero_lt_one hκ
  have hm := retained_mass_lift hκp hκa (rem.normalizer_lower k) ha.2.2.2
  rw [← rem.liftAtlas_mass hp ha] at hm
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hm
  change (2 * (rem.parent k).κ * a.κ)⁻¹ ≤ ((rem.parent k).κ * a.κ)⁻¹
  apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- Every lifted label carries its true terminal floor against the original
unconditioned product prior. -/
theorem liftAtlas_floor (hp : p.Valid) {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (hκ : 1 ≤ a.κ) (b : Fin a.C) :
    ENNReal.ofReal (p.N (rem.φ k) ^ (-p.f p.L) * |Matrix.det ((rem.liftAtlas k a).Q b)| /
      ((2 : ℝ) ^ (rem.liftAtlas k a).T * (rem.liftAtlas k a).κ)) ≤
      ((p.ν (rem.φ k) ((rem.liftAtlas k a).γ b)).prod volume) ((rem.liftAtlas k a).F b) := by
  have hκp : 0 < (rem.parent k).κ := lt_of_lt_of_le zero_lt_one (rem.slack_one k)
  have hκa : 0 < a.κ := lt_of_lt_of_le zero_lt_one hκ
  have hN : 0 < p.N (rem.φ k) := lt_of_lt_of_le (by norm_num) (hp.1 _)
  have hchild := ha.2.2.1 b
  rcases hchild with ⟨_, _, _, _, _, _, _, _, _, _, _, hfloor⟩
  have hstrong := floor_calibration
    (a := (2 : ℝ) ^ (rem.parent k).T) (b := (2 : ℝ) ^ a.T)
    (by positivity) (by positivity) hκp hκa ENNReal.toReal_nonneg (abs_nonneg (Matrix.det (a.Q b)))
    (rem.terminal_calibration k (a.γ b)) hfloor
  rw [rem.liftAtlas_chart_mass_real hp ha b]
  have hfactor : rem.timeLength k *
      (p.ν (rem.φ k) ((rem.parent k).γ (rem.parentIndex k (a.γ b)))
        ((rem.parent k).A (rem.parentIndex k (a.γ b)))).toReal =
      (p.ν (rem.φ k) ((rem.parent k).γ (rem.parentIndex k (a.γ b)))
        ((rem.parent k).A (rem.parentIndex k (a.γ b)))).toReal / (2 : ℝ) ^ (rem.parent k).T := by
    simp only [timeLength, div_eq_mul_inv, mul_comm]
  rw [hfactor]
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hstrong
  change p.N (rem.φ k) ^ (-p.f p.L) *
      |Matrix.det ((rem.parent k).Q (rem.parentIndex k (a.γ b)) * a.Q b)| /
      ((2 : ℝ) ^ ((rem.parent k).T + a.T) * (2 * (rem.parent k).κ * a.κ)) ≤ _
  rw [Matrix.det_mul, abs_mul, pow_add]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [mul_pos hκp hκa]

theorem liftAtlas_determinant_ne_zero {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (b : Fin a.C) : Matrix.det ((rem.liftAtlas k a).Q b) ≠ 0 := by
  change Matrix.det ((rem.parent k).Q (rem.parentIndex k (a.γ b)) * a.Q b) ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero ((rem.parent_valid k).2.2 (rem.parentIndex k (a.γ b))).1
    (ha.2.2.1 b).1

end Remainder

end Submission.Obl.k4_native_finite_terminal_atlas_lift
