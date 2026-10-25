-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/ModelBounds.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open MeasureTheory Set Filter

variable {α : Type*} [MeasurableSpace α] (p : Model α)

theorem q_pos (k : ℕ) (s : ℝ) : 0 < p.q k s := by
  unfold q
  positivity

theorem q_eq_inv (k : ℕ) (s : ℝ) : p.q k s = ((2 : ℝ) ^ p.T k s)⁻¹ := by
  simp [q, zpow_neg]

theorem timeBlock_subset_unit (T : ℕ) (j : Fin (2 ^ T)) : timeBlock T j ⊆ Icc (0 : ℝ) 1 := by
  have hpow : 0 < (2 : ℝ) ^ T := by positivity
  intro t ht
  have ht := ht
  change (j : ℕ) / (2 : ℝ) ^ T ≤ t ∧ t ≤ ((j : ℕ) + 1) / (2 : ℝ) ^ T at ht
  refine ⟨le_trans (by positivity) ht.1, ht.2.trans ?_⟩
  apply (div_le_one hpow).mpr
  exact_mod_cast Nat.succ_le_of_lt j.isLt

theorem volume_I (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) :
    volume (p.I k s i) = ENNReal.ofReal (p.q k s) := by
  rw [I, timeBlock, Real.volume_Icc, p.q_eq_inv]
  congr 1
  ring

theorem Valid.N_pos (hp : p.Valid) (k : ℕ) : 0 < p.N k := by linarith [hp.N_ge k]

theorem Valid.K_pos (hp : p.Valid) (k : ℕ) : 0 < p.K k := by linarith [hp.K_ge k]

theorem Valid.a_pos (hp : p.Valid) (k : ℕ) (s : ℝ) : 0 < p.a k s :=
  Real.rpow_pos_of_pos (Valid.N_pos p hp k) _

theorem Valid.μ_univ_le (hp : p.Valid) (k : ℕ) :
    p.μ k univ ≤ ENNReal.ofReal (p.K k) := by
  obtain ⟨_, hν, _, hdom, _, hsupp, _⟩ := hp.basic k
  have : IsProbabilityMeasure (p.ν k) := hν
  have hmeas : MeasurableSet (univ ×ˢ Icc (0 : ℝ) 1 : Set (α × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Icc
  calc
    p.μ k univ = p.μ k (univ ×ˢ Icc (0 : ℝ) 1) +
        p.μ k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := (measure_add_measure_compl hmeas).symm
    _ = p.μ k (univ ×ˢ Icc (0 : ℝ) 1) := by rw [hsupp, add_zero]
    _ ≤ (ENNReal.ofReal (p.K k) • ((p.ν k).prod volume)) (univ ×ˢ Icc (0 : ℝ) 1) := hdom _
    _ = ENNReal.ofReal (p.K k) := by
      simp [Measure.smul_apply, Measure.prod_prod, Real.volume_Icc]

/-- Full original assignment weights, multiplied by block length, have a
single probability budget independently of the number of labels. -/
theorem original_assignment_budget (k : ℕ) (s : ℝ)
    (hν : IsProbabilityMeasure (p.ν k))
    (hA : ∀ i, MeasurableSet (p.A k s i))
    (hdisj : ∀ i i', i ≠ i' → p.j k s i = p.j k s i' →
      Disjoint (p.A k s i) (p.A k s i')) :
    (∑ i, ENNReal.ofReal (p.q k s) * p.ν k (p.A k s i)) ≤ 1 := by
  have : IsProbabilityMeasure (p.ν k) := hν
  have h := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget
    (fun _ : Unit => p.ν k) (fun _ => (1 : ENNReal)) (fun _ => ())
    (p.j k s) (p.A k s) (fun _ => measure_univ) (by simp) hA
    (fun i i' hne _ hj => hdisj i i' hne hj)
  simp only [one_mul, Fintype.card_fin] at h
  calc
    _ = ENNReal.ofReal (p.q k s) * ∑ i, p.ν k (p.A k s i) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal (p.q k s) * (2 ^ p.T k s : ℕ) :=
      mul_le_mul le_rfl h bot_le bot_le
    _ = 1 := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (p.q_pos k s).le]
      simp only [Nat.cast_pow, Nat.cast_ofNat, p.q_eq_inv]
      rw [inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ p.T k s ≠ 0)]
      simp

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
