/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScalarPacketSteep.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.SteepPacketMass
import Submission.Obl.k4_scalar_grid_parameter_preparation.PacketGradient

/-! The steep-gradient estimate for an actual frozen scalar quadratic packet. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped ENNReal

theorem exists_scalar_steep_packet_mass_bound {X : Type*} [MeasurableSpace X] :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ (μ : Measure (X × ℝ)) (E : Set (X × ℝ)) (a : X → Fin 5 → ℝ) (A : Set X)
      (F : MvPolynomial (Fin 2) ℝ) (π : Measure ℝ)
      (K t₀ h u v δ ξ β M U W : ℝ) (P : ℝ≥0∞),
      F.totalDegree ≤ 2 → 1 ≤ K → t₀ ∈ Set.Icc (0 : ℝ) 1 → t₀ + h ≤ 1 →
      0 < h → 0 < δ → 0 < ξ → δ ≤ h → ξ ≤ K * h →
      0 < M → 0 < β → 0 ≤ U → 0 ≤ W → |u| + |v| ≤ K →
      C₀ * K ^ 2 + 1 + K ≤ M * β →
      162 * (1200 * K * (2 * K / h) ^ 4) * (2 * K) ^ 4 * δ ≤ 1 →
      162 * (1200 * K * (2 * K / h) ^ 4) * (2 * K) ^ 4 * δ ≤ ξ →
      (∀ p ∈ E, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a p.1 e| ≤ K) →
      (∀ t ∈ Set.Icc t₀ (t₀ + h), ∀ w ∈ Set.Icc (-1 : ℝ) 1,
        |eval ![t,u + t * v + h * w] F| ≤ K) →
      (∀ l ∈ A, ∀ t ∈ Set.Icc t₀ (t₀ + h),
        |scalarY (a l) t - u - t * v| ≤ K * h ∧
        |scalarX (a l) t - eval ![t,scalarY (a l) t] F| ≤ K * ξ) →
      (∀ i j b c : ℤ, μ {p | (⌊p.2 / δ⌋ : ℤ) = i ∧
        (⌊scalarY (a p.1) p.2 / δ⌋ : ℤ) = j ∧ (⌊scalarX (a p.1) p.2 / ξ⌋ : ℤ) = b ∧
        a p.1 1 ∈ scalarVelocityBin β c} ≤ ENNReal.ofReal (U * δ ^ 2 * W) * π (scalarVelocityBin β c)) →
      (∀ c : ℤ, π (scalarVelocityBin β c) ≤ P) →
      μ {p | p ∈ E ∧ p.1 ∈ A ∧ p.2 ∈ Set.Icc t₀ (t₀ + h) ∧
        M ≤ |eval ![p.2,scalarY (a p.1) p.2] (pderiv 1 F)|} ≤
          ENNReal.ofReal (1600 * (8 * K + 2) * (4 * K + 4) * U * h ^ 2 * W) * P := by
  obtain ⟨C₀, hC₀, hfield⟩ := exists_scalar_packet_field_bound
  refine ⟨C₀, hC₀, ?_⟩
  intro μ E a A F π K t₀ h u v δ ξ β M U W P hF hK ht₀ ht₁ hh hδ hξ hδh hrate
    hM hβ hU hW huv hforecast hfreeze hvalue hE hnorm hfit hjoint hangular
  let bad := {p : X × ℝ | p ∈ E ∧ p.1 ∈ A ∧ p.2 ∈ Set.Icc t₀ (t₀ + h) ∧
    M ≤ |eval ![p.2,scalarY (a p.1) p.2] (pderiv 1 F)|}
  let f : X × ℝ → Fin 3 → ℝ := fun p => ![p.2,scalarY (a p.1) p.2,scalarX (a p.1) p.2]
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hh₁ : h ≤ 1 := by linarith [ht₀.1]
  have hcoeff := packet_norm_polynomial_coefficients F hF K t₀ h u v hK ht₀ hh hh₁ huv hnorm
  have hY : ∀ p ∈ bad, |f p 1 - (u + t₀ * v)| ≤ (2 * K) * h := by
    intro p hp
    have ht : |p.2 - t₀| ≤ h := by
      rw [abs_of_nonneg (sub_nonneg.mpr hp.2.2.1.1)]
      linarith [hp.2.2.1.2]
    change |scalarY (a p.1) p.2 - (u + t₀ * v)| ≤ (2 * K) * h
    calc
      _ = |(scalarY (a p.1) p.2 - u - p.2 * v) + (p.2 - t₀) * v| := by congr 1; ring
      _ ≤ |scalarY (a p.1) p.2 - u - p.2 * v| + |p.2 - t₀| * |v| := by
        simpa only [abs_mul] using abs_add_le
          (scalarY (a p.1) p.2 - u - p.2 * v) ((p.2 - t₀) * v)
      _ ≤ K * h + h * K := add_le_add (hfit p.1 hp.2.1 p.2 hp.2.2.1).1
        (mul_le_mul ht (by linarith [abs_nonneg u] : |v| ≤ K) (abs_nonneg _) hh.le)
      _ = _ := by ring
  have hbox : ∀ p ∈ bad, ∀ i : Fin 2, |(![f p 0,f p 1] : Fin 2 → ℝ) i| ≤ 2 * K := by
    intro p hp i
    have ht := (hE p hp.1).1
    have ha := (hE p hp.1).2
    have ht' : |p.2| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    fin_cases i
    · exact ht'.trans (by linarith)
    · change |a p.1 0 + p.2 * a p.1 1| ≤ 2 * K
      calc
        _ ≤ |a p.1 0| + |p.2| * |a p.1 1| := by
          simpa only [abs_mul] using abs_add_le (a p.1 0) (p.2 * a p.1 1)
        _ ≤ K + 1 * K := add_le_add (ha 0) (mul_le_mul ht' (ha 1) (abs_nonneg _) (by norm_num))
        _ = _ := by ring
  have hdir : ∀ p ∈ bad, |eval ![f p 0,f p 1] (pderiv 0 F) +
      eval ![f p 0,f p 1] (pderiv 1 F) * a p.1 1| ≤ C₀ * K ^ 2 := by
    intro p hp
    have hd := hfield F (a p.1) K t₀ h ξ hF hK (hE p hp.1).2 ht₀.1 ht₁ hh hξ hrate
      (fun t ht => (hfit p.1 hp.2.1 t ht).2) p.2 hp.2.2.1
    simpa only [f, Matrix.cons_val_zero, Matrix.cons_val_one, scalarY, mul_comm] using hd
  have hm := steep_quadratic_packet_mass_le μ bad f (fun p => a p.1 1) F hF π
    δ ξ h (2 * K) K (C₀ * K ^ 2) M β U W (1200 * K * (2 * K / h) ^ 4) (2 * K)
    t₀ (u + t₀ * v) hδ hξ hδh (by positivity) hK₀ hU hW (by positivity)
    (by linarith) hM hβ hforecast hcoeff hfreeze hvalue
    (fun p hp => hp.2.2.1) hY hbox
    (fun p hp => (hfit p.1 hp.2.1 p.2 hp.2.2.1).2)
    (fun p hp => (hE p hp.1).2 1) hdir (fun p hp => hp.2.2.2) P hjoint hangular
  simpa only [show 4 * (2 * K) + 2 = 8 * K + 2 by ring] using hm

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
