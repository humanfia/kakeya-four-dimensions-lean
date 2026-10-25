-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/NativeCalibration.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.NativeBaseCaps
import Submission.Obl.k4_quadratic_mesh_coefficient_calibration
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.CalibrationLoss
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelBase
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelDiscriminant

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Set MeasureTheory Filter MvPolynomial

/-- The original discrete quadratic calibration principle. Its argument is
supplied by the accepted mesh-calibration theorem. -/
def MeshCalibration (C : ℝ) : Prop :=
  ∀ K β m E δ : ℝ, 1 ≤ K → 0 < β → 0 < m → 0 ≤ E → 0 < δ →
    C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * δ ≤ (1 : ℝ) / 2 →
    ∀ μ : Measure (Fin 3 → ℝ), IsFiniteMeasure μ → ENNReal.ofReal m ≤ μ univ →
    (∀ q : Fin 3 → ℤ, μ {z | (fun i : Fin 3 => ⌊z i / δ⌋) = q} ≤
      ENNReal.ofReal (β * δ ^ (3 : ℕ))) →
    ∀ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 →
      (∀ᵐ z ∂μ, (∀ i, |z i| ≤ K) ∧ |eval z G| ≤ E) →
      ∀ e, |G.coeff e| ≤ C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * E

theorem exists_mesh_calibration : ∃ C : ℝ, 1 ≤ C ∧ MeshCalibration C :=
  Submission.k4_quadratic_mesh_coefficient_calibration

/-- Apply mesh calibration after restricting the ORIGINAL incidence law.
The base cell ceilings are still charged to the unreduced law. -/
theorem calibrate_original_sublaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 3 → ℝ) (hZ : Measurable Z)
    {C K β m E δ : ℝ} (hcal : MeshCalibration C)
    (hK : 1 ≤ K) (hβ : 0 < β) (hm : 0 < m) (hE : 0 ≤ E) (hδ : 0 < δ)
    (hsmall : C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * δ ≤ (1 : ℝ) / 2)
    (hbound : ∀ᵐ u ∂μ, ∀ i, |Z u i| ≤ K)
    (hcap : ∀ q : Fin 3 → ℤ, μ {u | (fun i : Fin 3 => ⌊Z u i / δ⌋) = q} ≤
      ENNReal.ofReal (β * δ ^ (3 : ℕ)))
    (τ : Measure Ω) (hτ : τ ≤ μ) (hfloor : ENNReal.ofReal m ≤ τ univ)
    (G : MvPolynomial (Fin 3) ℝ) (hG : G.totalDegree ≤ 2)
    (hval : ∀ᵐ u ∂τ, |eval (Z u) G| ≤ E) :
    ∀ e, |G.coeff e| ≤ C * (1 + K) ^ C * (1 + β / m) ^ (6 : ℕ) * E := by
  have : IsFiniteMeasure τ := isFiniteMeasure_of_le μ hτ
  let ν : Measure (Fin 3 → ℝ) := Measure.map Z τ
  have hmass : ENNReal.ofReal m ≤ ν univ := by
    simpa only [ν, Measure.map_apply hZ MeasurableSet.univ, preimage_univ] using hfloor
  have hcell (q : Fin 3 → ℤ) : ν {z | (fun i : Fin 3 => ⌊z i / δ⌋) = q} ≤
      ENNReal.ofReal (β * δ ^ (3 : ℕ)) := by
    have hcode : Measurable (fun z : Fin 3 → ℝ => fun i : Fin 3 => ⌊z i / δ⌋) := by
      apply measurable_pi_iff.mpr
      intro i
      exact ((measurable_pi_apply i : Measurable (fun z : Fin 3 → ℝ => z i)).div_const δ).floor
    dsimp only [ν]
    rw [Measure.map_apply hZ (measurableSet_eq_fun hcode measurable_const)]
    exact (hτ _).trans (hcap q)
  have hbounded : MeasurableSet {z : Fin 3 → ℝ | ∀ i : Fin 3, |z i| ≤ K} := by
    convert MeasurableSet.iInter (fun i : Fin 3 =>
      measurableSet_le (measurable_pi_apply i : Measurable (fun z : Fin 3 → ℝ => z i)).abs
        (measurable_const : Measurable (fun _ : Fin 3 → ℝ => K))) using 1
    ext z
    simp
  have hset : MeasurableSet {z : Fin 3 → ℝ | (∀ i, |z i| ≤ K) ∧ |eval z G| ≤ E} :=
    hbounded.inter (measurableSet_le G.continuous_eval.measurable.abs measurable_const)
  have hgood : ∀ᵐ z ∂ν, (∀ i, |z i| ≤ K) ∧ |eval z G| ≤ E := by
    apply (ae_map_iff hZ.aemeasurable hset).mpr
    exact (hbound.filter_mono (ae_mono hτ)).and hval
  exact hcal K β m E δ hK hβ hm hE hδ hsmall ν inferInstance hmass hcell G hG hgood

namespace Model

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- Uniform calibration for ALL quadratics tested on the original base law.
No coefficients of the tested equation are bounded in the hypotheses. -/
theorem eventually_native_calibration (hp : p.Valid)
    {C : ℝ} (hC : 1 ≤ C) (hcal : MeshCalibration C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 →
      ∀ E : ℝ, 0 ≤ E → (∀ᵐ u ∂p.μ k, |eval (p.base k u) G| ≤ E) →
        ∀ e, |G.coeff e| ≤ p.N k ^ ε * E := by
  have hmesh := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hp.N_lim (show (-1 / 2 : ℝ) < 0 by norm_num) (2 : ℝ)
  filter_upwards [eventually_base_cell_caps p hp 2 (by norm_num),
    eventually_calibration_loss_le p hp hC hε,
    eventually_calibration_loss_le p hp hC (show (0 : ℝ) < 1 / 2 by norm_num),
    hmesh] with k hcaps hloss hhalf hmesh
  intro G hG E hE hval e
  simp only [Real.rpow_zero] at hmesh
  have hK := Valid.K_pos p hp k
  have hN := Valid.N_pos p hp k
  have hβ : 0 < (2 * p.K k + 5) * p.K k := by positivity
  have hδ : 0 < p.N k ^ (-1 : ℝ) := Real.rpow_pos_of_pos hN _
  have hsmall : C * (1 + 2 * p.K k) ^ C *
      (1 + ((2 * p.K k + 5) * p.K k) / (p.K k)⁻¹) ^ (6 : ℕ) *
        p.N k ^ (-1 : ℝ) ≤ (1 : ℝ) / 2 := by
    calc
      _ ≤ p.N k ^ (1 / 2 : ℝ) * p.N k ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_right hhalf hδ.le
      _ = p.N k ^ (-1 / 2 : ℝ) := by rw [← Real.rpow_add hN]; norm_num
      _ ≤ 1 / 2 := by linarith
  have hcell (q : Fin 3 → ℤ) : p.baseLaw k
      {z | (fun i : Fin 3 => ⌊z i / (p.N k ^ (-1 : ℝ))⌋) = q} ≤
      ENNReal.ofReal (((2 * p.K k + 5) * p.K k) * (p.N k ^ (-1 : ℝ)) ^ (3 : ℕ)) := by
    rw [Valid.baseLaw_cell p hp]
    have hpow : (p.N k ^ (-1 : ℝ)) ^ (3 : ℕ) = p.N k ^ (-3 : ℝ) := by
      rw [← Real.rpow_mul_natCast hN.le]
      norm_num
    rw [hpow]
    simpa only [mul_one] using
      (hcaps 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1 q
  have hm : MeasurableSet {z : Fin 3 → ℝ | |eval z G| ≤ E} := by
    exact measurableSet_le G.continuous_eval.measurable.abs measurable_const
  have hmap : ∀ᵐ z ∂p.baseLaw k, |eval z G| ≤ E :=
    (ae_map_iff (Valid.measurable_base p hp k).aemeasurable hm).mpr hval
  have hgood : ∀ᵐ z ∂p.baseLaw k,
      (∀ i, |z i| ≤ 2 * p.K k) ∧ |eval z G| ≤ E :=
    (Valid.baseLaw_bounded p hp k).and hmap
  have h := hcal (2 * p.K k) ((2 * p.K k + 5) * p.K k) ((p.K k)⁻¹) E
    (p.N k ^ (-1 : ℝ)) (by linarith [hp.K_ge k]) hβ (inv_pos.mpr hK) hE hδ hsmall
    (p.baseLaw k) (Valid.baseLaw_finite p hp k) (Valid.baseLaw_mass p hp k) hcell G hG hgood e
  exact h.trans (mul_le_mul_of_nonneg_right hloss hE)

/-- A single subpower budget calibrates every tested quadratic at once. -/
theorem exists_native_calibration_envelope (hp : p.Valid)
    {C : ℝ} (hC : 1 ≤ C) (hcal : MeshCalibration C) :
    ∃ W : ℕ → ℝ, (∀ k, 1 ≤ W k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, W k ≤ p.N k ^ ε) ∧
      ∀ᶠ k in atTop, ∀ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 →
        ∀ E : ℝ, 0 ≤ E → (∀ᵐ u ∂p.μ k, |eval (p.base k u) G| ≤ E) →
          ∀ e, |G.coeff e| ≤ W k * E := by
  exact exists_subpower_envelope p.N
    (fun k => (by linarith [hp.N_ge k] : 1 ≤ p.N k))
    (fun k W => ∀ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 →
      ∀ E : ℝ, 0 ≤ E → (∀ᵐ u ∂p.μ k, |eval (p.base k u) G| ≤ E) →
        ∀ e, |G.coeff e| ≤ W * E)
    (fun ε hε => eventually_native_calibration p hp hC hcal hε)

theorem eventually_native_discriminant_coeff (hp : p.Valid)
    {C : ℝ} (hC : 1 ≤ C) (hcal : MeshCalibration C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ e,
      |(Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant (p.P k)).coeff e| ≤
        p.N k ^ ε := by
  have hhalf : 0 < ε / 2 := by linarith
  have hpoly := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => (by linarith [hp.N_ge k] : 1 ≤ p.N k)) hp.N_lim hp.K_ge hp.K_sub 2
    (show ε / 2 < ε by linarith) (show (0 : ℝ) ≤ 3 by norm_num)
  filter_upwards [eventually_native_calibration p hp hC hcal hhalf, hpoly] with k hk hpoly
  intro e
  have hval : ∀ᵐ u ∂p.μ k,
      |eval (p.base k u)
        (Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant (p.P k))| ≤
          3 * p.K k ^ 2 := by
    filter_upwards [Valid.ae_good p hp k] with u hu
    exact GoodPoint.discriminant_bound p hp hu
  have h := hk _
    (Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant_degree
      (p.P k) (hp.basic k).2.2.2.2.2.2.2.1)
    (3 * p.K k ^ 2) (by positivity) hval e
  apply h.trans
  have heq : p.N k ^ (ε / 2) * (3 * p.K k ^ 2) =
      3 * p.K k ^ 2 * p.N k ^ (ε / 2) := by ring
  rw [heq]
  exact hpoly.le

theorem exists_native_discriminant_budget (hp : p.Valid)
    {C : ℝ} (hC : 1 ≤ C) (hcal : MeshCalibration C) :
    ∃ W : ℕ → ℝ, (∀ k, 1 ≤ W k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, W k ≤ p.N k ^ ε) ∧
      ∀ᶠ k in atTop, ∀ e,
        |(Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant (p.P k)).coeff e| ≤
          W k := by
  exact exists_subpower_envelope p.N
    (fun k => (by linarith [hp.N_ge k] : 1 ≤ p.N k))
    (fun k W => ∀ e,
      |(Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant (p.P k)).coeff e| ≤ W)
    (fun ε hε => eventually_native_discriminant_coeff p hp hC hcal hε)

/-- The actual frozen-law discriminant budget, using accepted o242. -/
theorem Valid.native_discriminant_budget (hp : p.Valid) :
    ∃ W : ℕ → ℝ, (∀ k, 1 ≤ W k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, W k ≤ p.N k ^ ε) ∧
      ∀ᶠ k in atTop, ∀ e,
        |(Submission.Obl.k4_stable_native_signal_oscillation.baseDiscriminant (p.P k)).coeff e| ≤
          W k := by
  obtain ⟨C, hC, hcal⟩ := exists_mesh_calibration
  exact exists_native_discriminant_budget p hp hC hcal

end Model

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
