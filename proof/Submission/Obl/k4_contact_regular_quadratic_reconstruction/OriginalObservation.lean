import Submission.Obl.k4_contact_regular_quadratic_reconstruction.HomogeneousCalibration
import Submission.Obl.k4_scalar_grid_parameter_preparation.IncidenceFacts

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

/-- The bounded original base and bounded native signal pass from the frozen
prior and time support to every original incidence. -/
theorem original_native_observation_bounds
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (μ : Measure (α × ℝ))
    (b : α → Fin 6 → ℝ) (P : MvPolynomial (Fin 4) ℝ) {K : ℝ} (hK : 1 ≤ K)
    (hdom : μ ≤ ENNReal.ofReal K • ν.prod volume)
    (hprior : ∀ᵐ l ∂ν, |b l 0| + |b l 1| + |b l 3| + |b l 4| ≤ K)
    (hsupport : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hP : ∀ᵐ p ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |eval (point (b p.1) t) P| ≤ K) :
    ∀ᵐ p ∂μ, (∀ i : Fin 3, |point (b p.1) p.2 i.castSucc| ≤ K) ∧
      |eval (point (b p.1) p.2) P| ≤ K := by
  have hpriorμ := ae_original_incidence ν μ K hdom hprior
  have htime : ∀ᵐ p ∂μ, p.2 ∈ Icc (0 : ℝ) 1 := by
    have hh : ∀ᵐ p ∂μ, p ∈ univ ×ˢ Icc (0 : ℝ) 1 := (ae_iff).mpr hsupport
    exact hh.mono fun p hp => hp.2
  filter_upwards [hpriorμ, htime, hP] with p hp ht hpoly
  refine ⟨?_, hpoly p.2 ht⟩
  have htAbs : |p.2| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have hmul (i : Fin 6) : |p.2 * b p.1 i| ≤ |b p.1 i| := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right htAbs (abs_nonneg (b p.1 i))
  intro i
  fin_cases i
  · change |p.2| ≤ K
    exact htAbs.trans hK
  · have he := (abs_add_le (b p.1 0) (p.2 * b p.1 3)).trans
      (add_le_add le_rfl (hmul 3))
    change |b p.1 0 + p.2 * b p.1 3| ≤ K
    linarith [abs_nonneg (b p.1 1), abs_nonneg (b p.1 4)]
  · have he := (abs_add_le (b p.1 1) (p.2 * b p.1 4)).trans
      (add_le_add le_rfl (hmul 4))
    change |b p.1 1 + p.2 * b p.1 4| ≤ K
    linarith [abs_nonneg (b p.1 0), abs_nonneg (b p.1 3)]

/-- Summing the unit native-signal bins gives an original base-cell ceiling,
which is inherited by any retained law. -/
theorem original_base_cap_of_native_unit_caps
    {α : Type*} [MeasurableSpace α] (μ σ : Measure (α × ℝ)) (hσμ : σ ≤ μ)
    (b : α → Fin 6 → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    {K δ : ℝ} (hK : 1 ≤ K) (hδ : 0 < δ)
    (hbound : ∀ᵐ p ∂μ, |eval (point (b p.1) p.2) P| ≤ K)
    (hcap : ∀ (q : Fin 3 → ℤ) (a : ℤ),
      μ {p | (fun i : Fin 3 => ⌊point (b p.1) p.2 i.castSucc / δ⌋) = q ∧
        ⌊eval (point (b p.1) p.2) P⌋ = a} ≤ ENNReal.ofReal (K * δ ^ (3 : ℕ))) :
    ∀ q : Fin 3 → ℤ,
      σ {p | (fun i : Fin 3 => ⌊point (b p.1) p.2 i.castSucc / δ⌋) = q} ≤
        ENNReal.ofReal (((4 * K + 2) * K) * δ ^ (3 : ℕ)) := by
  intro q
  have hp := Submission.Lib.K4AffineMeshCaps.base_cell_cap_of_bounded_signal μ
    (fun p => point (b p.1) p.2 ∘ Fin.castSucc)
    (fun p => eval (point (b p.1) p.2) P) (fun _ => True)
    hδ (by norm_num : (0 : ℝ) < 1) (by linarith : 0 ≤ K) (by linarith : 0 ≤ K)
    (hbound.mono fun p hp _ => hp)
    (by
      intro q a
      change μ {p | (fun i : Fin 3 => ⌊point (b p.1) p.2 i.castSucc / δ⌋) = q ∧
        ⌊eval (point (b p.1) p.2) P / 1⌋ = a ∧ True} ≤ _
      simpa only [and_true, div_one] using hcap q a) q
  change μ {p | (fun i : Fin 3 => ⌊point (b p.1) p.2 i.castSucc / δ⌋) = q ∧ True} ≤ _ at hp
  exact (hσμ _).trans (by simpa only [and_true, div_one, mul_assoc] using hp)

/-- Original base ceilings fit one fixed power uniformly over all retained
laws; no conditional density is introduced. -/
theorem original_base_cap_le_power
    {α : Type*} [MeasurableSpace α] (μ σ : Measure (α × ℝ)) (hσμ : σ ≤ μ)
    (b : α → Fin 6 → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    {N K B δ : ℝ} (hN : 2 ≤ N) (hK : 1 ≤ K) (hKN : K ≤ N)
    (hB : 5 ≤ B) (hδ : 0 < δ)
    (hbound : ∀ᵐ p ∂μ, |eval (point (b p.1) p.2) P| ≤ K)
    (hcap : ∀ (q : Fin 3 → ℤ) (a : ℤ),
      μ {p | (fun i : Fin 3 => ⌊point (b p.1) p.2 i.castSucc / δ⌋) = q ∧
        ⌊eval (point (b p.1) p.2) P⌋ = a} ≤ ENNReal.ofReal (K * δ ^ (3 : ℕ))) :
    ∀ q : Fin 3 → ℤ,
      σ {p | (fun i : Fin 3 => ⌊point (b p.1) p.2 i.castSucc / δ⌋) = q} ≤
        ENNReal.ofReal (N ^ B * δ ^ (3 : ℕ)) := by
  have hN0 : 0 ≤ N := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hbudget : (4 * K + 2) * K ≤ N ^ B := by
    calc
      (4 * K + 2) * K ≤ (4 * N + 2) * N := by gcongr
      _ ≤ 6 * N ^ (2 : ℕ) := by nlinarith
      _ ≤ 8 * N ^ (2 : ℕ) := by gcongr; norm_num
      _ ≤ N ^ (3 : ℕ) * N ^ (2 : ℕ) := by
        gcongr
        exact (by norm_num : (8 : ℝ) = 2 ^ (3 : ℕ)).le.trans
          (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 3)
      _ = N ^ (5 : ℕ) := by ring
      _ ≤ N ^ B := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by simpa using hB)
  intro q
  exact (original_base_cap_of_native_unit_caps μ σ hσμ b P hK hδ hbound hcap q).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hbudget (by positivity)))

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction
