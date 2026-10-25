/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/LiftFit.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftGeometry
import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftProperties

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

namespace Remainder

variable {p q : Data} {r h w : ℝ} (rem : Remainder p q r h w)

theorem liftAtlas_slack_large {k : ℕ} {a : Atlas q k} (hκ : 1 ≤ a.κ) :
    2 * a.κ ≤ (rem.liftAtlas k a).κ ∧ a.κ ≤ (rem.liftAtlas k a).κ := by
  have hκ0 : 0 ≤ a.κ := le_trans zero_le_one hκ
  have hm := mul_le_mul_of_nonneg_right (rem.slack_one k) hκ0
  change 2 * a.κ ≤ 2 * (rem.parent k).κ * a.κ ∧ a.κ ≤ 2 * (rem.parent k).κ * a.κ
  simp only [one_mul] at hm
  constructor <;> nlinarith

/-- The full native fit bounds on every assigned trajectory and every time
in the concatenated block. No later successful-incidence restriction is used. -/
theorem liftAtlas_fit (hp : p.Valid) (hr : 0 ≤ r) (hrL : r < p.L)
    {k M D : ℕ} {a : Atlas q k} (ha : a.TrueAt M D q.L) (hκ : 1 ≤ a.κ)
    (b : Fin a.C) (l : Trajectory) (hl : l ∈ (rem.liftAtlas k a).A b) (t : ℝ)
    (ht : t ∈ Set.Icc (((rem.liftAtlas k a).j b : ℝ) / (2 : ℝ) ^ (rem.liftAtlas k a).T)
      ((((rem.liftAtlas k a).j b : ℝ) + 1) / (2 : ℝ) ^ (rem.liftAtlas k a).T)) :
    ‖Matrix.toEuclideanLin ((rem.liftAtlas k a).Q b)⁻¹
      (y l t - (rem.liftAtlas k a).c b - t • (rem.liftAtlas k a).u b)‖ ≤ (rem.liftAtlas k a).κ ∧
    |MvPolynomial.eval (x l t) ((rem.liftAtlas k a).R b)| ≤ (rem.liftAtlas k a).κ * δ (p.N (rem.φ k)) p.L ∧
    |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) ((rem.liftAtlas k a).R b))| ≤
      (rem.liftAtlas k a).κ * p.B (rem.φ k) ((rem.liftAtlas k a).γ b) ∧
    |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4)
      (MvPolynomial.pderiv (3 : Fin 4) ((rem.liftAtlas k a).R b)))| ≤
      (rem.liftAtlas k a).κ * (p.B (rem.φ k) ((rem.liftAtlas k a).γ b)) ^ 2 /
        δ (p.N (rem.φ k)) p.L := by
  have hc := ha.2.2.1 b
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, hfit, _⟩
  have hh := (hfit (rem.coefficient_map k (a.γ b) l) hl.2).2.2
    ((t - rem.initialTime k (a.γ b)) / rem.timeLength k) (rem.liftAtlas_time a b ht)
  obtain ⟨hspace, hz, hz₁, hz₂⟩ := hh
  simp only [rem.same_base k, rem.length, rem.derivative_unit k (a.γ b)] at hz hz₁ hz₂
  have hN1 : 1 ≤ p.N (rem.φ k) := le_trans (by norm_num) (hp.1 _)
  have hcarr := thickness_product_bounds hN1 hr (sub_nonneg.mpr hrL.le)
  rw [show r + (p.L - r) = p.L by ring] at hcarr
  have hscalar := native_scalar_bounds
    (a := δ (p.N (rem.φ k)) r) (b := δ (p.N (rem.φ k)) (p.L - r))
    (c := δ (p.N (rem.φ k)) p.L) (κ := a.κ)
    (B := p.B (rem.φ k) ((rem.liftAtlas k a).γ b))
    (by unfold δ; positivity) (by unfold δ; positivity) (by unfold δ; positivity)
    (le_trans zero_le_one hκ) hcarr.1 hcarr.2 hz hz₁ hz₂
  have hlarge := rem.liftAtlas_slack_large hκ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rem.liftAtlas_spatial_residual ha b l t]
    exact hspace.trans hlarge.2
  · rw [rem.liftAtlas_test_evaluation a b l t]
    exact hscalar.1.trans (mul_le_mul_of_nonneg_right hlarge.1 (by unfold δ; positivity))
  · rw [rem.liftAtlas_test_pderiv_evaluation a b l t]
    exact hscalar.2.1.trans (mul_le_mul_of_nonneg_right hlarge.2
      (hp.derivative_unit_pos _ _).le)
  · rw [rem.liftAtlas_test_pderiv_pderiv_evaluation a b l t]
    apply hscalar.2.2.trans
    apply div_le_div_of_nonneg_right _ (by unfold δ; positivity)
    exact mul_le_mul_of_nonneg_right hlarge.2 (sq_nonneg _)

/-- Original support, assignment, dyadic time and derivative lower bound of
all incidences in the composed chart. -/
theorem liftAtlas_incidence (hp : p.Valid) {k M D : ℕ} {a : Atlas q k}
    (ha : a.TrueAt M D q.L) (hκ : 1 ≤ a.κ) (b : Fin a.C)
    (z : Incidence) (hz : z ∈ (rem.liftAtlas k a).F b) :
    z ∈ p.E (rem.φ k) ((rem.liftAtlas k a).γ b) ∧ z.1 ∈ (rem.liftAtlas k a).A b ∧
    z.2 ∈ Set.Icc (((rem.liftAtlas k a).j b : ℝ) / (2 : ℝ) ^ (rem.liftAtlas k a).T)
      ((((rem.liftAtlas k a).j b : ℝ) + 1) / (2 : ℝ) ^ (rem.liftAtlas k a).T) ∧
    p.B (rem.φ k) ((rem.liftAtlas k a).γ b) / (rem.liftAtlas k a).κ ≤
      |MvPolynomial.eval (x z.1 z.2) (MvPolynomial.pderiv (3 : Fin 4) ((rem.liftAtlas k a).R b))| := by
  let e := normalizedIncidenceEquiv (rem.coefficient_map k (a.γ b))
    (rem.initialTime k (a.γ b)) (rem.timeLength k) (rem.timeLength_pos k).ne'
  have hc := ha.2.2.1 b
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, hinc, _⟩
  obtain ⟨hE₁, hA₁, hI₁, hfloor⟩ := hinc (e z) hz
  have hpchart := (rem.parent_valid k).2.2 (rem.parentIndex k (a.γ b))
  rcases hpchart with ⟨_, _, _, _, _, _, _, _, _, _, hpinc, _⟩
  have hparent := hpinc z (rem.liftAtlas_F_subset_parent ha b hz)
  refine ⟨hparent.1, ⟨hparent.2.1, hA₁⟩, ?_, ?_⟩
  · have hi := (compositeBlock_interval ((rem.parent k).j (rem.parentIndex k (a.γ b))) (a.j b)
      ((e z).2)).mpr hI₁
    have heq : rem.initialTime k (a.γ b) + (e z).2 / (2 : ℝ) ^ (rem.parent k).T = z.2 := by
      simpa only [e, normalizedIncidenceEquiv_apply, timeLength, div_eq_mul_inv, mul_comm] using
        rem.time_roundtrip k (a.γ b) z.2
    change rem.initialTime k (a.γ b) + (e z).2 / (2 : ℝ) ^ (rem.parent k).T ∈ _ at hi
    rwa [heq] at hi
  · change q.B k (a.γ b) / a.κ ≤ |MvPolynomial.eval
      (x (rem.coefficient_map k (a.γ b) z.1)
        ((z.2 - rem.initialTime k (a.γ b)) / rem.timeLength k))
      (MvPolynomial.pderiv (3 : Fin 4) (a.R b))| at hfloor
    rw [rem.derivative_unit k (a.γ b)] at hfloor
    have hscaled := native_scalar_floor (by unfold δ; positivity) hfloor
    rw [rem.liftAtlas_test_pderiv_evaluation a b z.1 z.2]
    apply le_trans _ hscaled
    apply div_le_div_of_nonneg_left (hp.derivative_unit_pos _ _).le
      (lt_of_lt_of_le zero_lt_one hκ) (rem.liftAtlas_slack_large hκ).2

end Remainder

end Submission.Obl.k4_native_finite_terminal_atlas_lift
