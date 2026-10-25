-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.NativeOscillation
import Submission.Obl.k4_finite_affine_parent_sources.PointStates

/-!
# Native-signal groups of a finite law, and short state lists of small pieces

`finite_native_groups` applies the accepted oscillation partition (o176, through
`exists_native_partition_pullback`) to any finite law with positive mass, after normalising it:
at most `K^C` disjoint measurable groups cover all but a `K^(-A)` fraction, and on each group the
native signal varies by at most `K^C (a + |Δ base|)`.

`piece_state_codes`: a piece whose points lie in the groups, whose base diameter is at most `d`
in the coordinates of the groups and at most `d'` in any other base coordinates, carries at most
`81 n` state codes of mesh `mesh` in those other coordinates, once
`K^C (a + d) + d' ≤ mesh` and `d' ≤ mesh`.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

/-- **Groups of a finite law.** -/
theorem finite_native_groups (A : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (lam : Measure Ω) [IsFiniteMeasure lam],
      lam univ ≠ 0 →
      ∀ (point : Ω → NativePoint), Measurable point →
      ∀ (K a : ℝ) (P S : MvPolynomial (Fin 4) ℝ),
      2 ≤ K → 0 < a → a ≤ 1 → P.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      lam.map (nativeBase ∘ point) ≤ (ENNReal.ofReal K * lam univ) • volume →
      (∀ᵐ x ∂lam, point x ∈ goodSet K a P S) →
      ∃ (n : ℕ) (E : Fin n → Set Ω), (n : ℝ) ≤ K ^ C ∧
        (∀ i, MeasurableSet (E i)) ∧
        (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        lam (⋃ i, E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹) * lam univ ∧
        ∀ i x, x ∈ E i → ∀ y, y ∈ E i →
          |value S (point x) - value S (point y)| ≤
            K ^ C * (a + ‖nativeBase (point x) - nativeBase (point y)‖) := by
  obtain ⟨C, hC, hpart⟩ := exists_native_partition_pullback A
  refine ⟨C, hC, ?_⟩
  intro Ω _ lam _ hlam point hpoint K a P S hK ha ha1 hP hS hbase hgood
  have hlamt : lam univ ≠ ⊤ := measure_ne_top _ _
  set μ := (lam univ)⁻¹ • lam with hμ
  haveI : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hlam hlamt]
  have hbase' : μ.map (nativeBase ∘ point) ≤ ENNReal.ofReal K • volume := by
    rw [hμ, Measure.map_smul _ (measurable_nativeBase.comp hpoint).aemeasurable]
    refine Measure.le_iff'.mpr fun U => ?_
    have h := Measure.le_iff'.mp hbase U
    simp only [Measure.smul_apply, smul_eq_mul] at h ⊢
    calc (lam univ)⁻¹ * (lam.map (nativeBase ∘ point)) U
        ≤ (lam univ)⁻¹ * (ENNReal.ofReal K * lam univ * volume U) := by gcongr
      _ = ENNReal.ofReal K * volume U := by
          rw [show ENNReal.ofReal K * lam univ * volume U =
            lam univ * (ENNReal.ofReal K * volume U) by ring, ← mul_assoc,
            ENNReal.inv_mul_cancel hlam hlamt, one_mul]
  have hgood' : ∀ᵐ x ∂μ, point x ∈ goodSet K a P S := by
    rw [hμ]
    exact Measure.ae_smul_measure hgood _
  obtain ⟨n, E, hn, hEm, hEd, hmass, hosc⟩ :=
    hpart Ω μ point hpoint K a P S hK ha ha1 hP hS hbase' hgood'
  refine ⟨n, E, hn, hEm, hEd, ?_, hosc⟩
  have h1 : μ (⋃ i, E i)ᶜ = (lam univ)⁻¹ * lam (⋃ i, E i)ᶜ := by
    rw [hμ, Measure.smul_apply, smul_eq_mul]
  rw [h1] at hmass
  calc lam (⋃ i, E i)ᶜ = lam univ * ((lam univ)⁻¹ * lam (⋃ i, E i)ᶜ) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hlam hlamt, one_mul]
    _ ≤ lam univ * ENNReal.ofReal ((K ^ A)⁻¹) := by gcongr
    _ = ENNReal.ofReal ((K ^ A)⁻¹) * lam univ := mul_comm _ _

/-- **Short state lists of a small piece.** -/
theorem piece_state_codes {Ω : Type} {n : ℕ}
    (baseG base : Ω → EuclideanSpace ℝ (Fin 3)) (signal : Ω → ℝ)
    (E : Fin n → Set Ω) (F : Set Ω) (mesh M a d d' : ℝ) (hmesh : 0 < mesh) (hM : 0 ≤ M)
    (hd : 0 ≤ d) (hd'mesh : d' ≤ mesh) (hsmall : M * (a + d) + d' ≤ mesh)
    (hbaseG : ∀ x ∈ F, ∀ y ∈ F, ‖baseG x - baseG y‖ ≤ d)
    (hbase : ∀ x ∈ F, ∀ y ∈ F, ‖base x - base y‖ ≤ d')
    (hsignal : ∀ i x, x ∈ E i → ∀ y, y ∈ E i →
      |signal x - signal y| ≤ M * (a + ‖baseG x - baseG y‖)) :
    ∃ V : Finset (Fin 4 → ℤ), V.card ≤ 81 * n ∧
      ∀ x ∈ F, (∃ i, x ∈ E i) → stateCode base signal mesh x ∈ V := by
  classical
  have hlocal (i : Fin n) := small_group_state_codes base signal (E i ∩ F) mesh 1
    (M * (a + d)) d' hmesh zero_le_one hd'mesh (by linarith)
    (fun x hx y hy => hbase x hx.2 y hy.2)
    (fun x hx y hy => by
      have h1 := hsignal i x hx.1 y hy.1
      have h2 : ‖baseG x - baseG y‖ ≤ d := hbaseG x hx.2 y hy.2
      have h3 : M * (a + ‖baseG x - baseG y‖) ≤ M * (a + d) :=
        mul_le_mul_of_nonneg_left (by linarith) hM
      have h4 : 0 ≤ ‖base x - base y‖ := norm_nonneg _
      linarith)
  choose V hVcard hVmem using hlocal
  refine ⟨Finset.univ.biUnion V, ?_, ?_⟩
  · calc (Finset.univ.biUnion V).card ≤ ∑ i : Fin n, (V i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin n, 81 := Finset.sum_le_sum fun i _ => hVcard i
      _ = 81 * n := by simp [Nat.mul_comm]
  · rintro x hx ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hVmem i x ⟨hi, hx⟩⟩

end

end Submission.Obl.k4_finite_affine_parent_sources
