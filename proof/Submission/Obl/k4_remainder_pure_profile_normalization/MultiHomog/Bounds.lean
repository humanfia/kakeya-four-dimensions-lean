import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Encoded

/-!
# Pointwise bounds for the encoding

Almost every trajectory of a tempered world has bounded planar part and polynomially
bounded coefficients; its encoding has all coefficients at most one, and slow encoded
planar velocities.
-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set Filter
open scoped ENNReal

theorem norm_toLp_two_le (u w : ℝ) :
    ‖(WithLp.toLp 2 ![u, w] : EuclideanSpace ℝ (Fin 2))‖ ≤ |u| + |w| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity)]
  simp [Fin.sum_univ_two]
  nlinarith [abs_nonneg u, abs_nonneg w, sq_abs u, sq_abs w]

/-- A prior given by pieces bounded by `R` is carried by trajectories with coefficients
bounded by `R`. -/
theorem ae_coeff_le_of_pieces {m : ℕ} {R : ℝ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (hA : ∀ j, ∀ x ∈ A j, ∀ b, |x b| ≤ R) :
    ∀ᵐ l ∂(∑ j, ENNReal.ofReal (c j) • Measure.map (fun x => (i j, x)) (volume.restrict (A j))),
      ∀ e, |l.2 e| ≤ R := by
  have hS : MeasurableSet {l : Trajectory | ¬ ∀ e, |l.2 e| ≤ R} := by
    have : {l : Trajectory | ¬ ∀ e, |l.2 e| ≤ R} = ⋃ e : Fin 6, {l : Trajectory | R < |l.2 e|} := by
      ext l; simp [not_forall, not_le]
    rw [this]
    refine MeasurableSet.iUnion fun e => measurableSet_lt measurable_const ?_
    exact (continuous_abs.measurable.comp ((measurable_pi_apply e).comp measurable_snd))
  rw [ae_iff, Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Measure.smul_apply, Measure.map_apply (measurable_pair_left (i j)) hS,
    Measure.restrict_apply (hS.preimage (measurable_pair_left (i j)))]
  have : (fun x => (i j, x)) ⁻¹' {l : Trajectory | ¬ ∀ e, |l.2 e| ≤ R} ∩ A j = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false,
      not_and]
    intro hx hxA
    exact hx (hA j x hxA)
  rw [this, measure_empty, smul_zero]

namespace Sample

variable {S : Sample}

/-- The almost-sure good set of trajectories of a world. -/
def GoodLine (S : Sample) (l : Trajectory) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, ‖y l t‖ + ‖v l‖ ≤ S.K) ∧ ∀ e, |l.2 e| ≤ S.N ^ S.M

theorem ae_goodLine {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B) (γ : Fin S.W) :
    ∀ᵐ l ∂S.ν γ, S.GoodLine l := by
  obtain ⟨m, -, c, i, A, hA, hν⟩ := hT.prior γ
  have h2 := ae_coeff_le_of_pieces c i A (fun j => (hA j).2.2.2.2)
  rw [← hν] at h2
  filter_upwards [hT.native γ, h2] with l h1 h2
  exact ⟨h1, h2⟩

theorem GoodLine.y_le {l : Trajectory} (hl : S.GoodLine l) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖y l t‖ ≤ S.K := by
  have := hl.1 t ht
  linarith [norm_nonneg (v l)]

theorem GoodLine.v_le {l : Trajectory} (hl : S.GoodLine l) : ‖v l‖ ≤ S.K := by
  have := hl.1 0 ⟨le_rfl, zero_le_one⟩
  linarith [norm_nonneg (y l 0)]

theorem GoodLine.coord_le {l : Trajectory} (hl : S.GoodLine l) :
    |l.2 0| ≤ S.K ∧ |l.2 1| ≤ S.K ∧ |l.2 3| ≤ S.K ∧ |l.2 4| ≤ S.K := by
  have hy := hl.y_le (t := 0) ⟨le_rfl, zero_le_one⟩
  have hv := hl.v_le
  have e0 : (y l 0) 0 = l.2 0 := by simp [y, x]
  have e1 : (y l 0) 1 = l.2 1 := by simp [y, x]
  have e3 : (v l) 0 = l.2 3 := by simp [v]
  have e4 : (v l) 1 = l.2 4 := by simp [v]
  have n0 := PiLp.norm_apply_le (y l 0) 0
  have n1 := PiLp.norm_apply_le (y l 0) 1
  have n3 := PiLp.norm_apply_le (v l) 0
  have n4 := PiLp.norm_apply_le (v l) 1
  rw [e0, Real.norm_eq_abs] at n0
  rw [e1, Real.norm_eq_abs] at n1
  rw [e3, Real.norm_eq_abs] at n3
  rw [e4, Real.norm_eq_abs] at n4
  exact ⟨n0.trans hy, n1.trans hy, n3.trans hv, n4.trans hv⟩

namespace Hyp

variable (h : S.Hyp)
include h

/-- The encoding of a good trajectory has all coefficients at most one. -/
theorem enc_coeff_le_one (γ : Fin S.W) {l : Trajectory} (hl : S.GoodLine l) (e : Fin 6) :
    |(S.enc γ l).2 e| ≤ 1 := by
  obtain ⟨h0, h1, h3, h4⟩ := hl.coord_le
  have h2 := hl.2 2
  have h5 := hl.2 5
  have ha := h.a_pos
  have hb := h.b_pos γ
  have hθ := h.θ_pos γ
  have haK := h.aK_le
  have hbK := h.bK_le γ
  have hθN := h.θN_le γ
  have ho := h.o_le γ
  have ho0 := h.o_nonneg γ
  have key : ∀ (c z R : ℝ), 0 < c → |z| ≤ R → |c * z| ≤ c * R := by
    intro c z R hc hz
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hz hc.le
  have hK := h.K_pos
  have hNM := h.pow_pos' S.M
  simp only [Sample.enc, encLine, encCoeff]
  fin_cases e
  · simp
    have := key _ _ _ ha h0
    calc |S.a * l.2 0 + S.o γ| ≤ |S.a * l.2 0| + |S.o γ| := abs_add_le _ _
      _ ≤ S.a * S.K + S.o γ := by rw [abs_of_nonneg ho0]; linarith
      _ ≤ 1 := by linarith
  · simp
    rw [abs_of_pos hb]
    have := mul_le_mul_of_nonneg_left h1 hb.le
    linarith
  · simp
    rw [abs_of_pos hθ]
    have := mul_le_mul_of_nonneg_left h2 hθ.le
    linarith
  · simp
    have := key _ _ _ ha h3
    calc |S.a * l.2 3 + 2⁻¹| ≤ |S.a * l.2 3| + |(2⁻¹ : ℝ)| := abs_add_le _ _
      _ ≤ 1 := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]; linarith
  · simp
    have := key _ _ _ hb h4
    calc |S.b γ * l.2 4 + 2⁻¹| ≤ |S.b γ * l.2 4| + |(2⁻¹ : ℝ)| := abs_add_le _ _
      _ ≤ 1 := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]; linarith
  · simp
    rw [abs_of_pos hθ]
    have := mul_le_mul_of_nonneg_left h5 hθ.le
    linarith

/-- The encoded planar velocities of a good trajectory are slow. -/
theorem enc_velocity_small (γ : Fin S.W) {l : Trajectory} (hl : S.GoodLine l) :
    |S.a * l.2 3| < 1 / 2 ∧ |S.b γ * l.2 4| < 1 / 2 := by
  obtain ⟨-, -, h3, h4⟩ := hl.coord_le
  have ha := h.a_pos
  have hb := h.b_pos γ
  have haK := h.aK_le
  have hbK := h.bK_le γ
  constructor
  · rw [abs_mul, abs_of_pos ha]
    have := mul_le_mul_of_nonneg_left h3 ha.le
    linarith
  · rw [abs_mul, abs_of_pos hb]
    have := mul_le_mul_of_nonneg_left h4 hb.le
    linarith

/-- Coefficients of an encoded point are bounded by those of its decoding plus one. -/
theorem abs_encCoeff_le (γ : Fin S.W) (z : Fin 6 → ℝ) (e : Fin 6) :
    |encCoeff S.a (S.b γ) (S.θ γ) (S.o γ) z e| ≤ |z e| + 1 := by
  have ha := h.a_pos
  have hb := h.b_pos γ
  have hθ := h.θ_pos γ
  have ha1 := h.a_le
  have hb1 := h.b_le γ
  have hθ1 := h.θ_le γ
  have ho := h.o_le γ
  have ho0 := h.o_nonneg γ
  have key : ∀ (c w : ℝ), 0 < c → c ≤ 1 / 2 → |c * w| ≤ |w| := by
    intro c w hc hc1
    rw [abs_mul, abs_of_pos hc]
    nlinarith [abs_nonneg w]
  simp only [encCoeff]
  fin_cases e
  · simp
    have := key S.a (z 0) ha (by linarith)
    calc |S.a * z 0 + S.o γ| ≤ |S.a * z 0| + |S.o γ| := abs_add_le _ _
      _ ≤ |z 0| + 1 := by rw [abs_of_nonneg ho0]; linarith
  · simp
    have := key (S.b γ) (z 1) hb (by linarith)
    rw [abs_mul] at this
    linarith
  · simp
    have := key (S.θ γ) (z 2) hθ hθ1
    rw [abs_mul] at this
    linarith
  · simp
    have := key S.a (z 3) ha (by linarith)
    calc |S.a * z 3 + 2⁻¹| ≤ |S.a * z 3| + |(2⁻¹ : ℝ)| := abs_add_le _ _
      _ ≤ |z 3| + 1 := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]; linarith
  · simp
    have := key (S.b γ) (z 4) hb (by linarith)
    calc |S.b γ * z 4 + 2⁻¹| ≤ |S.b γ * z 4| + |(2⁻¹ : ℝ)| := abs_add_le _ _
      _ ≤ |z 4| + 1 := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]; linarith
  · simp
    have := key (S.θ γ) (z 5) hθ hθ1
    rw [abs_mul] at this
    linarith

end Hyp

end Sample

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
