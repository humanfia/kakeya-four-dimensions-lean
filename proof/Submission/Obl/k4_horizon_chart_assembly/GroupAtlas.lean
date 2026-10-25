import Submission.Obl.k4_horizon_chart_assembly.ChartCore
import Submission.Obl.k4_horizon_chart_assembly.Envelope
import Submission.Obl.k4_horizon_chart_assembly.GroupPreparation

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory MvPolynomial
open scoped ENNReal BigOperators
open Submission.Lib.K4FinitePlankAtlases (PhysicalPlank)

noncomputable section

/-- Full quantitative original-law chart construction in one native midpoint
group. The only remaining mass terms are exactly those of the supplied kernel. -/
theorem greedy_group_atlas (Hker : GreedyKernel) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (ν : Measure Trajectory) [IsProbabilityMeasure ν]
      (E : Set Incidence) (P : MvPolynomial (Fin 4) ℝ)
      (K H B n0 R t0 mid q a κ τ₀ σ j : ℝ) (D₀ T Dmesh : ℕ),
    1 ≤ K → 0 ≤ H → 0 < B → P.totalDegree ≤ 2 →
    MeasurableSet E →
    (∀ i, Fmt 7 H D₀ {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ E}) →
    (∀ e, |P.coeff e| ≤ H) →
    0 < q → 0 < a → a ≤ 1 → q ≤ a →
    q = ((2 : ℝ) ^ T)⁻¹ → t0 = j / (2 : ℝ) ^ T →
    2 * K + 2 ≤ R → mid ∈ Icc (0 : ℝ) 1 →
    Icc t0 (t0 + q) ⊆ Icc (0 : ℝ) 1 →
    (∀ t ∈ Icc t0 (t0 + q), |t - mid| ≤ q) →
    2 ≤ Dmesh → 0 < τ₀ → (Dmesh : ℝ) ^ (-η) ≤ σ →
    64 * R ≤ κ → K ≤ κ → 4 * n0 * (R * q) ^ 2 ≤ τ₀ * κ →
    ∀ (Γ : (Fin 2 → ℤ) × ℤ) (Gd : Set Incidence), MeasurableSet Gd →
    ∀ F : Finset (ℤ × (Fin 2 → ℤ)),
      (∀ p ∈ normalizedEvent (derivativeEvent E P (B / K)) t0 q ∩ Gd,
        p.1 ∈ nativeGroup P B K H mid q a Γ →
        (⌊p.2 * (Dmesh : ℝ)⌋, fun e : Fin 2 => ⌊(Dmesh : ℝ) *
          (groupIntercept q a t0 (R * q) Γ p.1 + p.2 • groupVelocity q (R * q) p.1) e⌋) ∈ F) →
    ∃ m : ℕ, ∃ ps : Fin m → PhysicalPlank Dmesh,
    ∃ (c w : Fin m → Plane) (Q : Fin m → Matrix (Fin 2) (Fin 2) ℝ),
      (m : ℝ) ≤ (Dmesh : ℝ) ^ 2 / (4 * τ₀) * ν.real (nativeGroup P B K H mid q a Γ) ∧
      (∀ i,
        let A := packetAssignment (nativeGroup P B K H mid q a Γ)
          (groupIntercept q a t0 (R * q) Γ) (groupVelocity q (R * q)) ps i
        RawChart (packetEnvelope H K R q τ₀ Dmesh) (max D₀ 4) κ T j a B E
          (liftedBlockCenter (midpointGroupCenter q Γ) (c i) (w i) t0 q (R * q))
          (liftedBlockSpeed (w i) q (R * q)) ((R * q) • Q i)
          (shiftedTest P (a * (Γ.2 : ℝ))) A (selectedEvent E A P (B / K) t0 q)
          (ENNReal.ofReal (n0 * |((R * q) • Q i).det| / ((2 : ℝ) ^ T * κ)) ≤
            (ν.prod volume) (selectedEvent E A P (B / K) t0 q))) ∧
      ((∑ i, (ν.prod volume) (selectedEvent E
        (packetAssignment (nativeGroup P B K H mid q a Γ)
          (groupIntercept q a t0 (R * q) Γ) (groupVelocity q (R * q)) ps i) P (B / K) t0 q)) +
        ENNReal.ofReal q * (ν.prod volume)
          (normalizedEvent (derivativeEvent E P (B / K)) t0 q ∩
            (packetResidual (nativeGroup P B K H mid q a Γ)
              (groupIntercept q a t0 (R * q) Γ) (groupVelocity q (R * q)) ps ×ˢ univ)) =
        (ν.prod volume) (selectedEvent E (nativeGroup P B K H mid q a Γ) P (B / K) t0 q)) ∧
      (ν.prod volume) (normalizedEvent (derivativeEvent E P (B / K)) t0 q ∩
        (packetResidual (nativeGroup P B K H mid q a Γ)
          (groupIntercept q a t0 (R * q) Γ) (groupVelocity q (R * q)) ps ×ˢ univ)) ≤
        (ν.prod volume) (normalizedEvent (derivativeEvent E P (B / K)) t0 q ∩ Gdᶜ ∩
          (packetResidual (nativeGroup P B K H mid q a Γ)
            (groupIntercept q a t0 (R * q) Γ) (groupVelocity q (R * q)) ps ×ˢ univ)) +
        ENNReal.ofReal σ * ν (packetResidual (nativeGroup P B K H mid q a Γ)
          (groupIntercept q a t0 (R * q) Γ) (groupVelocity q (R * q)) ps) +
        ENNReal.ofReal (C * τ₀ * (Dmesh : ℝ) ^ ζ / (σ * (Dmesh : ℝ) ^ 3) * (F.card : ℝ)) := by
  obtain ⟨η, C, hη, hC, hpack⟩ := greedy_packets Hker hζ
  refine ⟨η, C, hη, hC, ?_⟩
  intro ν _ E P K H B n0 R t0 mid q a κ τ₀ σ j D₀ T Dmesh
    hK hH hB hP hE hEf hPcoeff hq ha ha1 hqa hqT ht0 hR hmid hblock hnear
    hDmesh hτ hσ hκR hκK htrue Γ Gd hGd F hF
  let U := nativeGroup P B K H mid q a Γ
  let b := groupIntercept q a t0 (R * q) Γ
  let u := groupVelocity q (R * q)
  let E' := normalizedEvent (derivativeEvent E P (B / K)) t0 q
  have hU : MeasurableSet U := nativeGroup_measurable P hP B mid (by linarith) hH hq ha Γ
  have hb : Measurable b := groupIntercept_measurable q a t0 (R * q) Γ
  have hu : Measurable u := groupVelocity_measurable q (R * q)
  have hbu : ∀ l ∈ U, ‖b l‖ ≤ 1 ∧ ‖u l‖ ≤ 1 := by
    intro l hl
    exact nativeGroup_normalized_bounds P B H t0 mid hq (by linarith) hR
      (hnear t0 ⟨le_rfl, by linarith⟩) Γ hl
  have hEcut : MeasurableSet (derivativeEvent E P (B / K)) := hE.inter
    (Submission.Obl.k4_quadratic_atlas_normalization.measurableSet_derivativeFloorSet P (B / K))
  have hE' : MeasurableSet E' := normalizedEvent_measurable hEcut t0 q
  have hunit : E' ⊆ univ ×ˢ Icc (0 : ℝ) 1 := normalizedEvent_unit_time _ t0 q
  obtain ⟨m, ps, hwidth, hfloor, hres⟩ :=
    hpack Dmesh hDmesh Trajectory ν b u hb hu U hU hbu E' Gd hE' hGd hunit τ₀ σ hτ hσ F hF
  have hcount := packet_count_bound ν hDmesh E' hunit hU b u hb hu ps hτ hwidth hfloor
  have hcount' : (m : ℝ) ≤ (Dmesh : ℝ) ^ 2 / (4 * τ₀) := by
    apply hcount.trans
    have h : ν.real U ≤ 1 := measureReal_le_one
    nlinarith [div_nonneg (sq_nonneg (Dmesh : ℝ)) (show 0 ≤ 4 * τ₀ by positivity)]
  obtain ⟨c, w, Q, hmatrix⟩ := packet_matrix_charts ν hDmesh E' b u hbu ps hτ hwidth hfloor
  refine ⟨m, ps, c, w, Q, hcount, ?_, packet_physical_mass_identity ν E hE P (B / K) t0 hq hU b u hb hu ps, hres⟩
  intro i
  let A := packetAssignment U b u ps i
  have hAU : A ⊆ U := inter_subset_left
  have hi := hmatrix i
  have hA : A.Nonempty := by
    by_contra he
    have hf := hi.2.2.2.2.2
    change ENNReal.ofReal ((τ₀ / 4) * |(Q i).det|) ≤ (ν.prod volume) (E' ∩ (A ×ˢ univ)) at hf
    rw [Set.not_nonempty_iff_eq_empty.mp he] at hf
    simp only [empty_prod, inter_empty, measure_empty] at hf
    have hp : 0 < ENNReal.ofReal ((τ₀ / 4) * |(Q i).det|) :=
      ENNReal.ofReal_pos.mpr (mul_pos (div_pos hτ (by norm_num)) (abs_pos.mpr hi.1))
    exact (not_le_of_gt hp) hf
  have hs : t0 ∈ Icc (0 : ℝ) 1 := hblock ⟨le_rfl, by linarith⟩
  have he := uniform_packet_budgets P B H K R t0 mid q a τ₀ Dmesh m
    hH hK hR hq ha1 hqa ha hτ hcount' hPcoeff hs hmid Γ A hA hAU
    (c i) (w i) hi.2.1 (Q i) hi.1 hi.2.2.1
  exact packet_to_rawChart ν E P K H (packetEnvelope H K R q τ₀ Dmesh) B n0 R t0 mid q a κ τ₀ j
    (max D₀ 4) D₀ T Dmesh m hK hH hB hP hE hEf hq ha ha1 hqa hqT ht0 hR hmid hblock hnear
    Γ ps i A rfl (c i) (w i) (Q i) hi.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2
    hκR hκK htrue he.1 le_rfl he.2.1 he.2.2.1 he.2.2.2.1 he.2.2.2.2

end
end Submission.Obl.k4_horizon_chart_assembly
