import Submission.Obl.k4_remainder_pure_profile_normalization.KnownDensity
import Submission.Obl.k4_remainder_pure_profile_normalization.NativeDepth

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Set
open scoped ENNReal

/-- Only the pointwise number of active labels enters this restriction bound;
no measurability is needed of the lists giving the overlap certificate. -/
theorem sum_restrict_apply_le_of_lists {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (F : I → Set Ω) (hF : ∀ i, MeasurableSet (F i))
    (lst : Ω → Finset I) (D : ENNReal)
    (hmem : ∀ i x, x ∈ F i → i ∈ lst x)
    (hcard : ∀ x, ((lst x).card : ENNReal) ≤ D)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∑ i, μ.restrict (F i) A) ≤ D * μ A := by
  classical
  have hpoint (x : Ω) : (∑ i, (F i).indicator (fun _ => (1 : ENNReal)) x) ≤ D := by
    have heq : (∑ i, (F i).indicator (fun _ => (1 : ENNReal)) x) =
        ((Finset.univ.filter (fun i => x ∈ F i)).card : ENNReal) := by
      simp only [Set.indicator_apply]
      rw [← Finset.sum_filter]
      simp
    rw [heq]
    have hsub : Finset.univ.filter (fun i => x ∈ F i) ⊆ lst x := by
      intro i hi
      exact hmem i x (Finset.mem_filter.mp hi).2
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcard x)
  calc
    (∑ i, μ.restrict (F i) A) =
        ∫⁻ x in A, ∑ i, (F i).indicator (fun _ => (1 : ENNReal)) x ∂μ := by
      rw [lintegral_finsetSum _ (fun i _ => (measurable_const.indicator (hF i)))]
      apply Finset.sum_congr rfl
      intro i _
      rw [withDensity_indicator_one (hF i) |>.symm, withDensity_apply _ hA]
      rfl
    _ ≤ ∫⁻ _x in A, D ∂μ := lintegral_mono hpoint
    _ = D * μ A := by simp

/-- The known terminal list gives a measure bound in every original world. -/
theorem KnownSystem.Valid.world_overlap {p : Data} {k M D : ℕ} {r : ℝ}
    {s : KnownSystem p k} (hs : s.Valid M D r)
    (γ : Fin (p.W k)) (A : Set Incidence) (hA : MeasurableSet A) :
    (∑ b : {b : Fin s.atlas.C // s.atlas.γ b = γ},
      (((p.ν k γ).prod volume).restrict (s.atlas.F b.1)) A) ≤
      ENNReal.ofReal s.atlas.κ * p.incidenceMeasure k γ A := by
  classical
  let F (b : {b : Fin s.atlas.C // s.atlas.γ b = γ}) := s.atlas.F b.1
  have hF (b : {b : Fin s.atlas.C // s.atlas.γ b = γ}) : MeasurableSet (F b) :=
    (hs.2.2.2.1 b.1).2.2.2.2.2.2.2.1
  let lst (z : Incidence) := (s.lists γ (obs (p.B k γ) (δ (p.N k) p.L) z)).subtype
    (fun b => s.atlas.γ b = γ)
  have hm (b : {b : Fin s.atlas.C // s.atlas.γ b = γ}) (z : Incidence)
      (hz : z ∈ F b) : b ∈ lst z := by
    have h := (hs.2.2.2.1 b.1).2.2.2.2.2.2.2.2.2.2.2 z hz
    simpa only [lst, Finset.mem_subtype, b.2] using h
  have hc (z : Incidence) : ((lst z).card : ENNReal) ≤ ENNReal.ofReal s.atlas.κ := by
    calc
      ((lst z).card : ENNReal) ≤
          ((s.lists γ (obs (p.B k γ) (δ (p.N k) p.L) z)).card : ENNReal) := by
        rw [Finset.card_subtype]
        exact_mod_cast Finset.card_filter_le _ _
      _ ≤ ENNReal.ofReal s.atlas.κ := by
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (hs.2.2.1 γ _)
  have hrestr (b : {b : Fin s.atlas.C // s.atlas.γ b = γ}) :
      (p.incidenceMeasure k γ).restrict (F b) = ((p.ν k γ).prod volume).restrict (F b) := by
    have hsub : F b ⊆ p.E k γ := by
      intro z hz
      have h := ((hs.2.2.2.1 b.1).2.2.2.2.2.2.2.2.2.2.1 z hz).1
      simpa only [b.2] using h
    rw [Data.incidenceMeasure, Measure.restrict_restrict (hF b), inter_eq_left.mpr hsub]
  simpa only [hrestr] using sum_restrict_apply_le_of_lists
    (p.incidenceMeasure k γ) F hF lst (ENNReal.ofReal s.atlas.κ) hm hc A hA

/-- Sum original-world tail charges with their original weights. -/
theorem KnownSystem.Valid.weighted_overlap {p : Data} {k M D : ℕ} {r : ℝ}
    {s : KnownSystem p k} (hs : s.Valid M D r)
    (w : Fin (p.W k) → ENNReal) (A : Fin (p.W k) → Set Incidence)
    (hA : ∀ γ, MeasurableSet (A γ)) :
    (∑ b, w (s.atlas.γ b) * s.atlas.selectedMeasure b (A (s.atlas.γ b))) ≤
      ENNReal.ofReal s.atlas.κ * ∑ γ, w γ * p.incidenceMeasure k γ (A γ) := by
  classical
  calc
    (∑ b, w (s.atlas.γ b) * s.atlas.selectedMeasure b (A (s.atlas.γ b))) =
        ∑ γ, ∑ b : {b : Fin s.atlas.C // s.atlas.γ b = γ},
          w (s.atlas.γ b.1) * s.atlas.selectedMeasure b.1 (A (s.atlas.γ b.1)) :=
      (Fintype.sum_fiberwise s.atlas.γ _).symm
    _ = ∑ γ, w γ * ∑ b : {b : Fin s.atlas.C // s.atlas.γ b = γ},
          (((p.ν k γ).prod volume).restrict (s.atlas.F b.1)) (A γ) := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Atlas.selectedMeasure, b.2]
    _ ≤ ∑ γ, w γ * (ENNReal.ofReal s.atlas.κ * p.incidenceMeasure k γ (A γ)) := by
      apply Finset.sum_le_sum
      intro γ _
      exact mul_le_mul' le_rfl (hs.world_overlap γ (A γ) (hA γ))
    _ = ENNReal.ofReal s.atlas.κ * ∑ γ, w γ * p.incidenceMeasure k γ (A γ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ _
      ring

end Submission.Obl.k4_remainder_pure_profile_normalization
