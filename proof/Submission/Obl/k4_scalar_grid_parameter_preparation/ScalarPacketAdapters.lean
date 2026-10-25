/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScalarPacketAdapters.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarPhysicalSequenceData
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.TrueSystem

/-! Convert the frozen dyadic packet data into the physical preparation interface. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped Classical BigOperators ENNReal

theorem scalarPacketBlock_pow_two (T : ℕ) (j : Fin (2 ^ T)) :
    scalarPacketBlock (2 ^ T) j = Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block T j := by
  rw [Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block_eq]
  simp only [scalarPacketBlock,Nat.cast_pow,Nat.cast_ofNat,one_div]

theorem scalar_packet_family_of_dyadic {X G : Type*} [MeasurableSpace X] [DecidableEq G]
    (a : X → Fin 5 → ℝ) (K ξ w : ℝ) (T n : ℕ)
    (ν : G → Measure X) (ρ : G → Measure (X × ℝ))
    (γ : Fin n → G) (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set X)
    (u v : Fin n → ℝ) (F : Fin n → MvPolynomial (Fin 2) ℝ)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))
    (hfloor : ∀ i, ENNReal.ofReal (w / (K * (2 : ℝ) ^ T)) ≤ ν (γ i) (A i))
    (hcenter : ∀ i, |u i| + |v i| ≤ K)
    (hdegree : ∀ i, (F i).totalDegree ≤ 2)
    (hnorm : ∀ i, ∀ t ∈ Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block T (j i),
      ∀ z ∈ Set.Icc (-2 : ℝ) 2,
        |eval ![t,u i + t * v i + z / (2 : ℝ) ^ T] (F i)| ≤ K)
    (hfit : ∀ i, ∀ l ∈ A i, ∀ t ∈ Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block T (j i),
      |scalarY (a l) t - u i - t * v i| ≤ K / (2 : ℝ) ^ T ∧
      |scalarX (a l) t - eval ![t,scalarY (a l) t] (F i)| ≤ K * ξ)
    (hcovered : ∀ g, ρ g {p | ∃ i, γ i = g ∧ p.1 ∈ A i ∧
      p.2 ∈ Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block T (j i)}ᶜ = 0) :
    ∃ D : ScalarScalePackets X G a K ξ n (2 ^ T),
      (∀ i, ENNReal.ofReal (w / (K * ((2 ^ T : ℕ) : ℝ))) ≤ ν (D.world i) (D.labels i)) ∧
      ∀ g, ρ g (scalarScaleCovered D g)ᶜ = 0 := by
  let D : ScalarScalePackets X G a K ξ n (2 ^ T) := {
    world := γ
    block := j
    labels := A
    centerY := u
    centerV := v
    predictor := F
    labels_measurable := hA
    labels_disjoint := hdisj
    center_bound := hcenter
    predictor_degree := hdegree
    predictor_norm := by
      intro i t ht z hz
      rw [scalarPacketBlock_pow_two] at ht
      have h := hnorm i t ht z ⟨by linarith [hz.1],by linarith [hz.2]⟩
      simpa only [Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv,mul_comm] using h
    trajectory_fit := by
      intro i l hl t ht
      rw [scalarPacketBlock_pow_two] at ht
      simpa only [Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv] using hfit i l hl t ht }
  refine ⟨D,?_,?_⟩
  · intro i
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hfloor i
  · intro g
    have he : scalarScaleCovered D g = {p | ∃ i, γ i = g ∧ p.1 ∈ A i ∧
        p.2 ∈ Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block T (j i)} := by
      ext p
      simp only [scalarScaleCovered,Set.mem_iUnion,Finset.mem_filter,Finset.mem_univ,true_and,
        Set.mem_prod,D,scalarPacketBlock_pow_two,Set.mem_ofPred_eq]
      simp only [exists_prop]
    rw [he]
    exact hcovered g

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
