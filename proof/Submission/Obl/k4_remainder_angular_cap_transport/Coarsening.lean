import Submission.Obl.k4_remainder_angular_cap_transport.Definitions
import Submission.Obl.k4_remainder_angular_cap_transport.NormAngular
import Submission.Obl.k4_native_grid_profile_extension.Labels
open MeasureTheory Set
open scoped ENNReal
namespace Submission.Obl.k4_remainder_angular_cap_transport

theorem map_ediv_count {m : ℕ} (hm : 0 < m) :
    (Measure.count : Measure ℤ).map (fun z => z / (m : ℤ)) =
      (m : ENNReal) • Measure.count := by
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  change Measure.count {z' : ℤ | z' / (m : ℤ) = z} = _
  simpa only [Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one] using
      Submission.Obl.k4_native_grid_profile_extension.count_ediv_fiber hm z

noncomputable def jointReference : Measure ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) :=
  (volume.prod Measure.count).prod Measure.count

def hiddenQuotient (m : ℕ) (z : (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) :=
  ((z.1.1, z.1.2 / (m : ℤ)), z.2)

theorem measurable_hiddenQuotient (m : ℕ) : Measurable (hiddenQuotient m) := by
  exact (measurable_fst.prodMk
    ((measurable_of_countable (fun z : ℤ => z / (m : ℤ))).comp measurable_snd)).prodMap
      measurable_id

theorem map_hiddenQuotient {m : ℕ} (hm : 0 < m) :
    jointReference.map (hiddenQuotient m) = (m : ENNReal) • jointReference := by
  unfold jointReference hiddenQuotient
  change ((volume.prod Measure.count).prod Measure.count).map
    (Prod.map (Prod.map id (fun z : ℤ => z / (m : ℤ))) id) = _
  rw [← Measure.map_prod_map _ _ (measurable_id.prodMap (measurable_of_countable _))
    measurable_id, ← Measure.map_prod_map _ _ measurable_id (measurable_of_countable _),
    Measure.map_id, Measure.map_id, map_ediv_count hm, Measure.prod_smul_right,
    Measure.prod_smul_left]


theorem terminal_width_ratio (N L r : ℝ) :
    ∃ m : ℕ, 0 < m ∧ m ≤ 2 ∧ δ N r * δ N (L - r) = δ N L * (m : ℝ) := by
  let a := r * Real.log N / Real.log 2
  let b := (L - r) * Real.log N / Real.log 2
  have hab : a + b = L * Real.log N / Real.log 2 := by dsimp [a, b]; ring
  have h0 := Int.le_floor_add a b
  have h1 := Int.le_floor_add_floor a b
  by_cases h : ⌊a + b⌋ = ⌊a⌋ + ⌊b⌋
  · refine ⟨1, by decide, by decide, ?_⟩
    simp only [Nat.cast_one, Nat.cast_ofNat, δ]
    change (2 : ℝ) ^ (-⌊a⌋) * (2 : ℝ) ^ (-⌊b⌋) =
      (2 : ℝ) ^ (-⌊L * Real.log N / Real.log 2⌋) * 1
    rw [← hab, h, mul_one, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  · have h' : -⌊a⌋ + -⌊b⌋ = -⌊a + b⌋ + 1 := by omega
    refine ⟨2, by decide, le_rfl, ?_⟩
    simp only [Nat.cast_one, Nat.cast_ofNat, δ]
    change (2 : ℝ) ^ (-⌊a⌋) * (2 : ℝ) ^ (-⌊b⌋) =
      (2 : ℝ) ^ (-⌊L * Real.log N / Real.log 2⌋) * 2
    rw [← hab, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), h',
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp


open Geometry

/-- Coarsening the original terminal hidden bin costs precisely its fiber size. -/
theorem coarsened_jobs_le (μ : Measure Incidence) (B a a' du : ℝ) {m : ℕ}
    (hm : 0 < m) (hwidth : a' = a * (m : ℝ)) (C : ENNReal)
    (hceil : μ.map (jobs B a du) ≤ C • jointRef) :
    μ.map (jobs B a' du) ≤ (C * (m : ENNReal)) • jointRef := by
  have hfac : jobs B a' du = hiddenQuotient m ∘ jobs B a du := by
    funext p
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · change ⌊B * graphPoint p.1 p.2 3 / a'⌋ =
        ⌊B * graphPoint p.1 p.2 3 / a⌋ / (m : ℤ)
        rw [hwidth, div_mul_eq_div_div, Int.floor_div_natCast]
    · rfl
  rw [hfac, ← Measure.map_map (measurable_hiddenQuotient m) (measurable_jobs _ _ _)]
  calc
    _ ≤ (C • jointRef).map (hiddenQuotient m) :=
      Measure.map_mono hceil (measurable_hiddenQuotient m)
    _ = C • jointRef.map (hiddenQuotient m) :=
      Measure.map_smul C (measurable_hiddenQuotient m).aemeasurable
    _ = _ := by
      change C • jointReference.map (hiddenQuotient m) = _
      rw [map_hiddenQuotient hm, smul_smul]
      rfl

end Submission.Obl.k4_remainder_angular_cap_transport
