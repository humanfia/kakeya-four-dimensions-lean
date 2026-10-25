/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/Inherited/CriticalEndpoint.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/CriticalEndpoint.lean.
   Original source attributions below are preserved. -/
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/CriticalEndpoint.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_matching_endpoint_volume.EndpointSlice

/-! The three horizontal traversals in the critical-rate argument.
The volume estimates reuse the accepted constant-control endpoint theorem.
-/

namespace Submission.Obl.k4_critical_switching_state_preparation.Inherited

noncomputable section

open Set MeasureTheory
open scoped ENNReal ContDiff

/-- Exact horizontal traversal from time t to time s with constant velocity c. -/
def horizontalTraverse (c t s : ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![z 0 + c * (s - t), z 1 + (-z 0 + t * c) * (s - t)]

/-- The spatial endpoint after three horizontal traversals. q is the start
(time, horizontal position, transverse position), and t are the two switches. -/
def criticalSpatialEndpoint (c q : Fin 3 → ℝ) (s : ℝ) (t : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![q 1 + c 0 * (s - q 0) + (c 1 - c 0) * (s - t 0) + (c 2 - c 1) * (s - t 1),
    q 2 + (-q 1 + q 0 * c 0) * (s - q 0) +
      (c 1 - c 0) * t 0 * (s - t 0) + (c 2 - c 1) * t 1 * (s - t 1)]

theorem criticalSpatialEndpoint_eq_traversals (c q : Fin 3 → ℝ) (s : ℝ) (t : Fin 2 → ℝ) :
    criticalSpatialEndpoint c q s t =
      horizontalTraverse (c 2) (t 1) s
        (horizontalTraverse (c 1) (t 0) (t 1)
          (horizontalTraverse (c 0) (q 0) (t 0) ![q 1, q 2])) := by
  ext i
  fin_cases i <;> simp [criticalSpatialEndpoint, horizontalTraverse] <;> ring

/-- The critical endpoint is an affine shear of the accepted low-jet endpoint. -/
theorem criticalSpatialEndpoint_eq_low (c q : Fin 3 → ℝ) (s : ℝ) (t : Fin 2 → ℝ) :
    criticalSpatialEndpoint c q s t =
      let z := Submission.Obl.k4_matching_endpoint_volume.endpointLow c (q 0) s t
      ![q 1 + z 0, q 2 - q 1 * (s - q 0) + s * z 0 - 2 * z 1] := by
  ext i
  fin_cases i <;>
    simp [criticalSpatialEndpoint, Submission.Obl.k4_matching_endpoint_volume.endpointLow,
      Fin.sum_univ_two] <;> ring

/-- A shear of slope at most one and transverse scale two pulls a square into
an axis-parallel square of the same radius, after moving its center. -/
theorem critical_shear_square_volume (s a b u v r : ℝ) (hs : |s| ≤ 1) (hr : 0 ≤ r) :
    volume {z : Fin 2 → ℝ | |a + z 0 - u| ≤ r ∧ |b + s * z 0 - 2 * z 1 - v| ≤ r} ≤
      ENNReal.ofReal (4 * r ^ 2) := by
  let zc : ℝ := u - a
  let yc : ℝ := (b + s * zc - v) / 2
  let lo : Fin 2 → ℝ := ![zc - r, yc - r]
  let hi : Fin 2 → ℝ := ![zc + r, yc + r]
  have hsub : {z : Fin 2 → ℝ | |a + z 0 - u| ≤ r ∧
        |b + s * z 0 - 2 * z 1 - v| ≤ r} ⊆ Set.Icc lo hi := by
    intro z hz
    have hz0 : |z 0 - zc| ≤ r := by
      convert hz.1 using 1 <;> dsimp [zc] <;> congr 1 <;> ring
    have hmul : |s * (z 0 - zc)| ≤ r := by
      rw [abs_mul]
      exact (mul_le_mul hs hz0 (abs_nonneg _) zero_le_one).trans_eq (one_mul r)
    have hz1 : |z 1 - yc| ≤ r := by
      have heq : 2 * (z 1 - yc) =
          s * (z 0 - zc) - (b + s * z 0 - 2 * z 1 - v) := by dsimp [yc]; ring
      have he : |2 * (z 1 - yc)| ≤ 2 * r := by
        rw [heq]
        exact (abs_sub _ _).trans (by linarith [hz.2])
      rw [abs_mul] at he
      norm_num at he
      linarith
    constructor <;> intro i <;> fin_cases i
    · have := (abs_le.mp hz0).1
      dsimp [lo]
      linarith
    · have := (abs_le.mp hz1).1
      dsimp [lo]
      linarith
    · have := (abs_le.mp hz0).2
      dsimp [hi]
      linarith
    · have := (abs_le.mp hz1).2
      dsimp [hi]
      linarith
  have hvol : volume (Set.Icc lo hi) = ENNReal.ofReal (4 * r ^ 2) := by
    rw [Real.volume_Icc_pi, Fin.prod_univ_two]
    simp only [lo, hi, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show zc + r - (zc - r) = 2 * r by ring,
      show yc + r - (yc - r) = 2 * r by ring,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  exact (measure_mono hsub).trans_eq hvol

/-- At each fixed final time the critical endpoint has a polynomial pullback
bound, uniform in the unrestricted starting point. -/
theorem critical_endpoint_slice_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 2 ≤ K → ∀ c : Fin 3 → ℝ,
      (∀ i, |c i| ≤ K) →
      (∀ i : Fin 2, K⁻¹ ≤ |c i.succ - c i.castSucc|) →
      ∀ (q : Fin 3 → ℝ) (s : ℝ), |s| ≤ 1 → ∀ (u : Fin 2 → ℝ) (r : ℝ), 0 ≤ r →
      volume {t : Fin 2 → ℝ |
        t ∈ Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 K⁻¹ ∧
        ∀ i, |criticalSpatialEndpoint c q s t i - u i| ≤ r} ≤
        ENNReal.ofReal (C * K ^ 24 * r ^ 2) := by
  obtain ⟨C, hC, hbound⟩ :=
    Submission.Obl.k4_matching_endpoint_volume.endpoint_slice_polynomial_bound 2 (by norm_num)
  refine ⟨4 * C, by positivity, ?_⟩
  intro K hK c hc hgap q s hs u r hr
  let A : Set (Fin 2 → ℝ) := {z | |q 1 + z 0 - u 0| ≤ r ∧
    |q 2 - q 1 * (s - q 0) + s * z 0 - 2 * z 1 - u 1| ≤ r}
  have hA : MeasurableSet A :=
    (measurableSet_le (by fun_prop : Measurable (fun z : Fin 2 → ℝ =>
      |q 1 + z 0 - u 0|)) measurable_const).inter
    (measurableSet_le (by fun_prop : Measurable (fun z : Fin 2 → ℝ =>
      |q 2 - q 1 * (s - q 0) + s * z 0 - 2 * z 1 - u 1|)) measurable_const)
  have hsub : {t : Fin 2 → ℝ |
        t ∈ Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 K⁻¹ ∧
        ∀ i, |criticalSpatialEndpoint c q s t i - u i| ≤ r} ⊆
      Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 K⁻¹ ∩
        (Submission.Obl.k4_matching_endpoint_volume.endpointLow c (q 0) s) ⁻¹' A := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    have h0 := ht.2 0
    have h1 := ht.2 1
    rw [criticalSpatialEndpoint_eq_low] at h0 h1
    exact ⟨h0, h1⟩
  calc
    _ ≤ volume (Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 K⁻¹ ∩
        (Submission.Obl.k4_matching_endpoint_volume.endpointLow c (q 0) s) ⁻¹' A) :=
      measure_mono hsub
    _ ≤ ENNReal.ofReal (C * K ^ (2 * (2 + 1) * (2 + 2))) * volume A :=
      hbound K hK c hc hgap (q 0) s hs A hA
    _ ≤ ENNReal.ofReal (C * K ^ 24) * ENNReal.ofReal (4 * r ^ 2) := by
      gcongr
      exact critical_shear_square_volume s (q 1) (q 2 - q 1 * (s - q 0))
        (u 0) (u 1) r hs hr
    _ = ENNReal.ofReal ((4 * C) * K ^ 24 * r ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring


/-- The full endpoint, with final time included. -/
def criticalEndpoint (c q : Fin 3 → ℝ) (p : ℝ × (Fin 2 → ℝ)) : Fin 3 → ℝ :=
  ![p.1, criticalSpatialEndpoint c q p.1 p.2 0, criticalSpatialEndpoint c q p.1 p.2 1]

theorem continuous_criticalEndpoint (c q : Fin 3 → ℝ) : Continuous (criticalEndpoint c q) := by
  unfold criticalEndpoint criticalSpatialEndpoint
  fun_prop

/-- Three regular horizontal traversals have at most polynomial-in-K mass
in a base cube of radius r. Times are not required to be increasing. -/
theorem critical_endpoint_cell_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 2 ≤ K → ∀ c : Fin 3 → ℝ,
      (∀ i, |c i| ≤ K) →
      (∀ i : Fin 2, K⁻¹ ≤ |c i.succ - c i.castSucc|) →
      ∀ (q u : Fin 3 → ℝ) (r : ℝ), 0 ≤ r →
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))
        {p : ℝ × (Fin 2 → ℝ) | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧
          p.2 ∈ Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 K⁻¹ ∧
          ∀ i, |criticalEndpoint c q p i - u i| ≤ r} ≤
        ENNReal.ofReal (C * K ^ 24 * r ^ 3) := by
  obtain ⟨C, hC, hslice⟩ := critical_endpoint_slice_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro K hK c hc hgap q u r hr
  let E : Set (ℝ × (Fin 2 → ℝ)) :=
    {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      p.2 ∈ Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 K⁻¹ ∧
      ∀ i, |criticalEndpoint c q p i - u i| ≤ r}
  let J : Set ℝ := Set.Icc (u 0 - r) (u 0 + r)
  let B : ENNReal := ENNReal.ofReal (C * K ^ 24 * r ^ 2)
  have hE1 : MeasurableSet {p : ℝ × (Fin 2 → ℝ) | p.1 ∈ Set.Icc (0 : ℝ) 1} :=
    measurableSet_Icc.preimage measurable_fst
  have hE2 : MeasurableSet {p : ℝ × (Fin 2 → ℝ) |
      p.2 ∈ Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 K⁻¹} :=
    (Submission.Obl.k4_matching_endpoint_volume.isClosed_separatedUnitCube 2 K⁻¹).measurableSet.preimage
      measurable_snd
  have hE3 : MeasurableSet {p : ℝ × (Fin 2 → ℝ) |
      ∀ i, |criticalEndpoint c q p i - u i| ≤ r} := by
    simp only [← Set.iInter_ofPred]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le
      (((continuous_apply i).comp (continuous_criticalEndpoint c q)).sub continuous_const).abs.measurable
      measurable_const
  have hE : MeasurableSet E := hE1.inter (hE2.inter hE3)
  have hslice' (s : ℝ) : volume (Prod.mk s ⁻¹' E) ≤ J.indicator (fun _ => B) s := by
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1 ∧ |s - u 0| ≤ r
    · have hsJ : s ∈ J := by
        have ha := abs_le.mp hs.2
        exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
      rw [Set.indicator_of_mem hsJ]
      have hs1 : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1.1], hs.1.2⟩
      have hsub : Prod.mk s ⁻¹' E ⊆ {t : Fin 2 → ℝ |
          t ∈ Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 K⁻¹ ∧
          ∀ i, |criticalSpatialEndpoint c q s t i - (![u 1, u 2] : Fin 2 → ℝ) i| ≤ r} := by
        intro t ht
        refine ⟨ht.2.1, ?_⟩
        intro i
        fin_cases i
        · exact ht.2.2 1
        · exact ht.2.2 2
      exact (measure_mono hsub).trans (hslice K hK c hc hgap q s hs1 ![u 1, u 2] r hr)
    · have hempty : Prod.mk s ⁻¹' E = ∅ := by
        ext t
        constructor
        · intro ht
          exact (hs ⟨ht.1, ht.2.2 0⟩).elim
        · intro ht
          exact ht.elim
      rw [hempty, measure_empty]
      exact bot_le
  calc
    _ = ∫⁻ s : ℝ, volume (Prod.mk s ⁻¹' E) := Measure.prod_apply hE
    _ ≤ ∫⁻ s : ℝ, J.indicator (fun _ => B) s := lintegral_mono hslice'
    _ = B * volume J := by rw [lintegral_indicator measurableSet_Icc, setLIntegral_const]
    _ = ENNReal.ofReal ((2 * C) * K ^ 24 * r ^ 3) := by
      dsimp [B, J]
      rw [Real.volume_Icc, show u 0 + r - (u 0 - r) = 2 * r by ring,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring


/-- The same cell cap holds for any unnormalized path law dominated by a
control probability times Lebesgue time measure. Extra restrictions on the
retained paths are allowed. -/
theorem critical_endpoint_dominated_cell_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 2 ≤ K →
      ∀ (ρ : Measure (Fin 3 → ℝ)) [IsProbabilityMeasure ρ]
        (μ : Measure ((Fin 3 → ℝ) × (ℝ × (Fin 2 → ℝ)))) (A : ℝ), 0 ≤ A →
      μ ≤ ENNReal.ofReal A •
        (ρ.prod ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))) →
      ∀ (q u : Fin 3 → ℝ) (r : ℝ), 0 ≤ r →
      ∀ S : Set ((Fin 3 → ℝ) × (ℝ × (Fin 2 → ℝ))), MeasurableSet S →
      (∀ p ∈ S, (∀ i, |p.1 i| ≤ K) ∧
        (∀ i : Fin 2, K⁻¹ ≤ |p.1 i.succ - p.1 i.castSucc|) ∧
        p.2.1 ∈ Set.Icc (0 : ℝ) 1 ∧
        p.2.2 ∈ Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 K⁻¹ ∧
        ∀ i, |criticalEndpoint p.1 q p.2 i - u i| ≤ r) →
      μ S ≤ ENNReal.ofReal (A * C * K ^ 24 * r ^ 3) := by
  obtain ⟨C, hC, hcell⟩ := critical_endpoint_cell_bound
  refine ⟨C, hC, ?_⟩
  intro K hK ρ _ μ A hA hμ q u r hr S hS hlegal
  have hfiber (c : Fin 3 → ℝ) :
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) (Prod.mk c ⁻¹' S) ≤
        ENNReal.ofReal (C * K ^ 24 * r ^ 3) := by
    by_cases hc : (∀ i, |c i| ≤ K) ∧
        (∀ i : Fin 2, K⁻¹ ≤ |c i.succ - c i.castSucc|)
    · have hsub : Prod.mk c ⁻¹' S ⊆ {p : ℝ × (Fin 2 → ℝ) |
          p.1 ∈ Set.Icc (0 : ℝ) 1 ∧
          p.2 ∈ Submission.Obl.k4_matching_endpoint_volume.separatedUnitCube 2 K⁻¹ ∧
          ∀ i, |criticalEndpoint c q p i - u i| ≤ r} := by
        intro p hp
        exact (hlegal (c, p) hp).2.2
      exact (measure_mono hsub).trans (hcell K hK c hc.1 hc.2 q u r hr)
    · have hempty : Prod.mk c ⁻¹' S = ∅ := by
        ext p
        constructor
        · intro hp
          have h := hlegal (c, p) hp
          exact (hc ⟨h.1, h.2.1⟩).elim
        · intro hp
          exact hp.elim
      rw [hempty, measure_empty]
      exact bot_le
  have href :
      (ρ.prod ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))) S ≤
        ENNReal.ofReal (C * K ^ 24 * r ^ 3) := by
    rw [Measure.prod_apply hS]
    calc
      _ ≤ ∫⁻ _c, ENNReal.ofReal (C * K ^ 24 * r ^ 3) ∂ρ := lintegral_mono hfiber
      _ = _ := by simp
  calc
    μ S ≤ (ENNReal.ofReal A •
        (ρ.prod ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))))) S := hμ S
    _ = ENNReal.ofReal A *
        (ρ.prod ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))) S := rfl
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C * K ^ 24 * r ^ 3) := by gcongr
    _ = ENNReal.ofReal (A * C * K ^ 24 * r ^ 3) := by
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      ring

end

end Submission.Obl.k4_critical_switching_state_preparation.Inherited
