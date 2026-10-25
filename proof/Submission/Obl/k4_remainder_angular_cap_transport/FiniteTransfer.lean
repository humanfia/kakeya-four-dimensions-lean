import Submission.Obl.k4_remainder_angular_cap_transport.ChartTail
import Submission.Obl.k4_remainder_angular_cap_transport.NormMass

namespace Submission.Obl.k4_remainder_angular_cap_transport
open MeasureTheory Set
open Geometry
open scoped ENNReal

/-- The summed normalized angular tail is charged to the original exceptional mass. -/
theorem finite_angular_tail {W T : ℕ} (s : Geometry.ChartSystem W T)
    (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory) [∀ γ, IsFiniteMeasure (ν γ)]
    (E : Fin W → Set Incidence) (B : Fin W → ℝ) (hω : ∀ γ, 0 ≤ ω γ)
    (hZ : 0 < s.normZ ω ν) (hE : ∀ γ, MeasurableSet (E γ))
    (hD : ∀ b, (s.frame b).det ≠ 0)
    (hA : ∀ b, MeasurableSet (s.assignment b)) (hF : ∀ b, MeasurableSet (s.event b))
    (hpos : ∀ b, 0 < (ν (s.world b) (s.assignment b)).toReal)
    (hdisj : ∀ b b', b ≠ b' → s.world b = s.world b' → s.block b = s.block b' →
      Disjoint (s.assignment b) (s.assignment b'))
    (hsub : ∀ b, ∀ p ∈ s.event b, p ∈ E (s.world b) ∧ p.1 ∈ s.assignment b ∧
      p.2 ∈ timeBlock T (s.block b))
    (κ δ a a₀ du : ℝ) (hκ : 1 ≤ κ) (hδ : δ ≠ 0) (hdu : 0 < du)
    (hDs : ∀ b, (∑ i : Fin 2, ∑ j : Fin 2, |s.frame b i j|) ≤ κ / (2 : ℝ) ^ T)
    {m : ℕ} (hm : 0 < m) (hm2 : m ≤ 2) (hwidth : δ * a = a₀ * (m : ℝ))
    (E₂ : Fin s.count → Set Incidence) (hE₂ : ∀ b, E₂ b ⊆ s.normEventOf b)
    (G : Fin W → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (G₂ : Fin s.count → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (hG : ∀ γ, Measurable (G γ)) (hG₂ : ∀ b, Measurable (G₂ b))
    (hlaw : ∀ γ, (((ν γ).prod volume).restrict (E γ)).map (jobs (B γ) a₀ du) =
      jointRef.withDensity (G γ))
    (hlaw₂ : ∀ b, (((s.normPrior ν b).prod volume).restrict (E₂ b)).map
      (jobs (B (s.world b) / δ) a du) = jointRef.withDensity (G₂ b))
    [∀ b, IsFiniteMeasure (((s.normPrior ν b).prod volume).restrict (E₂ b))]
    (θ target : ENNReal)
    (htarget : ∀ b, ENNReal.ofReal (100 * κ ^ 2) * θ *
      ENNReal.ofReal (|(s.frame b).det| / (ν (s.world b) (s.assignment b)).toReal) ≤ target) :
    (∑ b, ENNReal.ofReal (s.normWeight ω ν b) *
      (((s.normPrior ν b).prod volume).restrict (E₂ b))
        {p | target < G₂ b (jobs (B (s.world b) / δ) a du p)}) ≤
      4 * ENNReal.ofReal (s.normZ ω ν)⁻¹ *
        ∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume).restrict (E γ)
          {p | θ < G γ (jobs (B γ) a₀ du p)} := by
  let Y : Fin W → Set Incidence := fun γ => {p | θ < G γ (jobs (B γ) a₀ du p)}
  have hY : ∀ γ, MeasurableSet (Y γ) := fun γ =>
    measurableSet_lt measurable_const ((hG γ).comp (measurable_jobs _ _ _))
  have hchart (b : Fin s.count) :
      (((s.normPrior ν b).prod volume).restrict (E₂ b))
        {p | target < G₂ b (jobs (B (s.world b) / δ) a du p)} ≤
      2 * (ν (s.world b) (s.assignment b) * ENNReal.ofReal (s.frameOf b).q)⁻¹ *
        (((ν (s.world b)).prod volume).restrict (s.event b)) (Y (s.world b)) := by
    haveI := (inferInstance : IsFiniteMeasure (((s.normPrior ν b).prod volume).restrict (E₂ b)))
    calc
      _ ≤ (((s.normPrior ν b).prod volume).restrict (E₂ b))
          {p | ENNReal.ofReal (100 * κ ^ 2) * θ *
            ENNReal.ofReal (|(s.frame b).det| / (ν (s.world b) (s.assignment b)).toReal) <
              G₂ b (jobs (B (s.world b) / δ) a du p)} :=
        measure_mono (fun _ hp => (htarget b).trans_lt hp)
      _ ≤ _ := (s.frameOf b).selected_joint_tail
        (hfinite := by
          change IsFiniteMeasure (((s.normPrior ν b).prod volume).restrict (E₂ b))
          infer_instance) (s.frameOf_q_pos b)
        (isUnit_iff_ne_zero.mpr (hD b)) (ν (s.world b)) (s.assignment b) (s.event b)
        (E (s.world b)) (E₂ b) (hA b) (hF b) (fun p hp => (hsub b p hp).1)
        (fun p hp => ⟨(hsub b p hp).2.1, s.timeBlock_frameOf b ▸ (hsub b p hp).2.2⟩)
        (hE₂ b) (hpos b) (B (s.world b)) δ a a₀ du κ hδ hdu hκ
        (by simpa only [Geometry.ChartSystem.frameOf, div_eq_mul_inv, one_div, one_mul] using hDs b)
        hm hm2 hwidth (G (s.world b)) (G₂ b) (hG _) (hG₂ b) (hlaw _) (hlaw₂ b) θ
  have hworld : (∑ b, ENNReal.ofReal (ω (s.world b)) *
      (((ν (s.world b)).prod volume).restrict (s.event b)) (Y (s.world b))) ≤
      2 * ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ)) (Y γ) := by
    calc
      _ = ∑ γ, ∑ b ∈ Finset.univ.filter (fun b => s.world b = γ),
          ENNReal.ofReal (ω γ) * ((ν γ).prod volume) (s.event b ∩ Y γ) := by
        rw [← Finset.sum_fiberwise Finset.univ s.world]
        refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun b hb => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        rw [Measure.restrict_apply (hY _), Set.inter_comm, hb]
      _ ≤ ∑ γ, ENNReal.ofReal (ω γ) * (2 * ((ν γ).prod volume) (E γ ∩ Y γ)) := by
        gcongr with γ
        rw [← Finset.mul_sum]
        gcongr
        exact s.sum_world_event_le _ E γ hF hdisj hsub (Y γ) (hY γ) ((hE γ).inter (hY γ))
      _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [Measure.restrict_apply (hY γ), Set.inter_comm]
        ring
  calc
    _ ≤ ∑ b, ENNReal.ofReal (s.normWeight ω ν b) *
        (2 * (ν (s.world b) (s.assignment b) * ENNReal.ofReal (s.frameOf b).q)⁻¹ *
          (((ν (s.world b)).prod volume).restrict (s.event b)) (Y (s.world b))) := by
      gcongr with b
      exact hchart b
    _ = 2 * ENNReal.ofReal (s.normZ ω ν)⁻¹ *
        ∑ b, ENNReal.ofReal (ω (s.world b)) *
          (((ν (s.world b)).prod volume).restrict (s.event b)) (Y (s.world b)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      calc
        _ = 2 * (ENNReal.ofReal (s.normWeight ω ν b) *
          (ν (s.world b) (s.assignment b) * ENNReal.ofReal (s.frameOf b).q)⁻¹) *
          (((ν (s.world b)).prod volume).restrict (s.event b)) (Y (s.world b)) := by ring
        _ = _ := by rw [s.weight_conditioning ω ν hω hZ b (hpos b)]; ring
    _ ≤ 2 * ENNReal.ofReal (s.normZ ω ν)⁻¹ *
        (2 * ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ)) (Y γ)) := by
      gcongr
    _ = _ := by ring

end Submission.Obl.k4_remainder_angular_cap_transport
