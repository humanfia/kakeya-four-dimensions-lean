import Submission.Obl.k4_scalar_marked_coefficient_smoothing.RawWeights

/-!
# Density ceilings of the marked law

The observation at hidden scale `ρ` of the marked law (restricted to a set of noisy slopes)
is dominated by `(1/σ) κ W` times the reference measure `baseRef`; the augmented observation
with a noisy slope bin of width `ρu` by the same constant times `jointRef`.  Here `κ` bounds
the probability that a noisy slope falls into the allowed set and `W` bounds the tag weights
over every window.
-/

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw

open MeasureTheory Set
open scoped ENNReal

/-- The exact observation at hidden scale `ρ`. -/
noncomputable def obsAt (ρ : ℝ) (p : Traj × ℝ) : Obs :=
  (![p.2, curveY Prod.snd p.1 p.2], ⌊curveX Prod.snd p.1 p.2 / ρ⌋)

theorem observation_eq_obsAt (N r : ℝ) : observation N r = obsAt (N ^ (-r)) := rfl

theorem measurable_curveY_traj : Measurable (fun p : Traj × ℝ => curveY Prod.snd p.1 p.2) := by
  unfold curveY; fun_prop

theorem measurable_curveX_traj : Measurable (fun p : Traj × ℝ => curveX Prod.snd p.1 p.2) := by
  unfold curveX; fun_prop

theorem measurable_obsAt (ρ : ℝ) : Measurable (obsAt ρ) := by
  refine Measurable.prodMk ?_ ?_
  · rw [measurable_pi_iff, Fin.forall_fin_two]
    exact ⟨measurable_snd, measurable_curveY_traj⟩
  · exact Int.measurable_floor.comp (measurable_curveX_traj.div_const ρ)

theorem measurable_slopeBin (ρu : ℝ) : Measurable (fun p : Traj × ℝ => ⌊p.1.2 1 / ρu⌋) :=
  Int.measurable_floor.comp ((by fun_prop : Measurable fun p : Traj × ℝ => p.1.2 1).div_const ρu)

theorem sigmaFinite_baseRef : SigmaFinite baseRef := by
  unfold baseRef; infer_instance

theorem sigmaFinite_jointRef : SigmaFinite jointRef := by
  have := sigmaFinite_baseRef
  unfold jointRef; infer_instance

/-- The planar change of variables `(t, y) ↦ ![t, y]`. -/
theorem volume_preimage_vec {A : Set (Fin 2 → ℝ)} (hA : MeasurableSet A) :
    volume {q : ℝ × ℝ | (![q.1, q.2] : Fin 2 → ℝ) ∈ A} = volume A := by
  have hmp := (volume_preserving_finTwoArrow ℝ).symm
  have hset : {q : ℝ × ℝ | (![q.1, q.2] : Fin 2 → ℝ) ∈ A} =
      (MeasurableEquiv.finTwoArrow.symm : ℝ × ℝ → (Fin 2 → ℝ)) ⁻¹' A := by
    ext q
    simp [MeasurableEquiv.finTwoArrow_symm_apply]
  rw [hset, hmp.measure_preimage hA.nullMeasurableSet]

/-- The cell ceiling in the coordinates of the observation. -/
theorem cellObs_le {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) {H J : ℕ} (b₀ : Fin H → Coeff)
    (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) (i : ℤ) {Ksl : Set ℝ}
    (hK : MeasurableSet Ksl) {κ W : ℝ≥0∞} (hκ : ∀ j, noise1 σ {v | b₀ j 1 + v ∈ Ksl} ≤ κ)
    (hW : ∀ q : ℝ × ℝ,
      ∑ j, (tagWindow σ ρ b₀ mark j i Ksl).indicator (fun _ => ENNReal.ofReal (w j)) q ≤ W)
    {A : Set (Fin 2 → ℝ)} (hA : MeasurableSet A) :
    MarkedLaw σ H J b₀ w mark {p : Traj × ℝ | (![p.2, curveY Prod.snd p.1 p.2] : Fin 2 → ℝ) ∈ A ∧
        ⌊curveX Prod.snd p.1 p.2 / ρ⌋ = i ∧ p.1.2 1 ∈ Ksl} ≤
      ENNReal.ofReal (σ⁻¹) * κ * W * volume A := by
  have hA' : MeasurableSet {q : ℝ × ℝ | (![q.1, q.2] : Fin 2 → ℝ) ∈ A} := by
    have hm : Measurable (fun q : ℝ × ℝ => (![q.1, q.2] : Fin 2 → ℝ)) := by
      rw [measurable_pi_iff, Fin.forall_fin_two]
      exact ⟨measurable_fst, measurable_snd⟩
    exact hA.preimage hm
  have h := MarkedLaw_cell_le hσ hρ b₀ w mark i hK hκ hW hA'
  rw [volume_preimage_vec hA] at h
  exact h

/-- **Pure observation ceiling** (on a set of noisy slopes). -/
theorem map_obsAt_restrict_le {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) {H J : ℕ}
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) {Ksl : Set ℝ}
    (hK : MeasurableSet Ksl) {κ W : ℝ≥0∞} (hκ : ∀ j, noise1 σ {v | b₀ j 1 + v ∈ Ksl} ≤ κ)
    (hW : ∀ (i : ℤ) (q : ℝ × ℝ),
      ∑ j, (tagWindow σ ρ b₀ mark j i Ksl).indicator (fun _ => ENNReal.ofReal (w j)) q ≤ W) :
    ((MarkedLaw σ H J b₀ w mark).restrict {p : Traj × ℝ | p.1.2 1 ∈ Ksl}).map (obsAt ρ) ≤
      (ENNReal.ofReal (σ⁻¹) * κ * W) • baseRef := by
  have hS : MeasurableSet {p : Traj × ℝ | p.1.2 1 ∈ Ksl} :=
    hK.preimage (by fun_prop)
  refine le_smul_prod_count fun i A hA => ?_
  rw [Measure.map_apply (measurable_obsAt ρ) (hA.prod (measurableSet_singleton i)),
    Measure.restrict_apply ((hA.prod (measurableSet_singleton i)).preimage
      (measurable_obsAt ρ))]
  have hset : obsAt ρ ⁻¹' (A ×ˢ {i}) ∩ {p : Traj × ℝ | p.1.2 1 ∈ Ksl} =
      {p : Traj × ℝ | (![p.2, curveY Prod.snd p.1 p.2] : Fin 2 → ℝ) ∈ A ∧
        ⌊curveX Prod.snd p.1 p.2 / ρ⌋ = i ∧ p.1.2 1 ∈ Ksl} := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_singleton_iff, obsAt, mem_ofPred_eq]
    tauto
  rw [hset]
  exact cellObs_le hσ hρ b₀ w mark i hK hκ (hW i) hA

/-- **Augmented observation ceiling.** -/
theorem map_velocity_le {σ ρ ρu : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) {H J : ℕ}
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) {κ W : ℝ≥0∞}
    (hκ : ∀ (k : ℤ) j, noise1 σ {v | b₀ j 1 + v ∈ {v : ℝ | ⌊v / ρu⌋ = k}} ≤ κ)
    (hW : ∀ (k i : ℤ) (q : ℝ × ℝ),
      ∑ j, (tagWindow σ ρ b₀ mark j i {v : ℝ | ⌊v / ρu⌋ = k}).indicator
        (fun _ => ENNReal.ofReal (w j)) q ≤ W) :
    (MarkedLaw σ H J b₀ w mark).map (fun p => (obsAt ρ p, ⌊p.1.2 1 / ρu⌋)) ≤
      (ENNReal.ofReal (σ⁻¹) * κ * W) • jointRef := by
  have hmeas : Measurable (fun p : Traj × ℝ => (obsAt ρ p, ⌊p.1.2 1 / ρu⌋)) :=
    (measurable_obsAt ρ).prodMk (measurable_slopeBin ρu)
  have := sigmaFinite_baseRef
  refine le_smul_prod_count fun k B hB => ?_
  have hKk : MeasurableSet {v : ℝ | ⌊v / ρu⌋ = k} :=
    (measurableSet_singleton k).preimage (Int.measurable_floor.comp (measurable_id.div_const ρu))
  have h := map_obsAt_restrict_le hσ hρ b₀ w mark hKk (hκ k) (hW k)
  have hS : MeasurableSet {p : Traj × ℝ | p.1.2 1 ∈ {v : ℝ | ⌊v / ρu⌋ = k}} :=
    hKk.preimage (by fun_prop)
  calc (MarkedLaw σ H J b₀ w mark).map (fun p => (obsAt ρ p, ⌊p.1.2 1 / ρu⌋)) (B ×ˢ {k})
      = ((MarkedLaw σ H J b₀ w mark).restrict
          {p : Traj × ℝ | p.1.2 1 ∈ {v : ℝ | ⌊v / ρu⌋ = k}}).map (obsAt ρ) B := by
        rw [Measure.map_apply hmeas (hB.prod (measurableSet_singleton k)),
          Measure.map_apply (measurable_obsAt ρ) hB,
          Measure.restrict_apply (hB.preimage (measurable_obsAt ρ))]
        congr 1
    _ ≤ ((ENNReal.ofReal (σ⁻¹) * κ * W) • baseRef) B := h B
    _ = ENNReal.ofReal (σ⁻¹) * κ * W * baseRef B := by
        rw [Measure.smul_apply, smul_eq_mul]

end Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw
