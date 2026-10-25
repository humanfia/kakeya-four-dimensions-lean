import Submission.Obl.k4_initial_horizon_bound.BoundedContinuousPlanks
import Submission.Obl.k4_initial_horizon_bound.ResidualCap
import Submission.Obl.k4_initial_horizon_bound.VisitedCells

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_initial_horizon_bound

open Submission.Lib.K4ContinuousPlanks
open Submission.Lib.K4PlankGeometry (cellCode)
open Submission.Obl.k4_plank_projected_multiplicity (expandProjectedCells localCellOffsets)

theorem mesh_incidence_cap_to_prior {α : Type*} [MeasurableSpace α]
    {D : ℕ} (hD : 1 ≤ D) (ν : Measure α) (E : Set (α × ℝ)) (hE : MeasurableSet E)
    (b u : α → EuclideanSpace ℝ (Fin 2)) (hb : Measurable b) (hu : Measurable u)
    (H : Set α) (hH : MeasurableSet H) {s A : ℝ} (hs : 0 < s)
    (hduration : ∀ x ∈ H, ENNReal.ofReal s ≤ incidenceDuration E x)
    (hstop : MeshPlankCap D (ν.withDensity (incidenceDuration E)) b u A) :
    MeshPlankCap D (ν.restrict H) b u (A / s) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ
  let S := {x | InFullTracePlank (b x) (u x) c w e₁ e₂ a β}
  have hS := measurableSet_fullTracePlank b u hb hu c w e₁ e₂ a β
  have hbound : ENNReal.ofReal s * (ν.restrict H) S ≤ ENNReal.ofReal (A * a * β) :=
    (retained_duration_prior_bound ν hE hS hH (ENNReal.ofReal s)
      (fun x hx => hduration x hx.2)).trans (hstop c w e₁ e₂ a β he₁ he₂ he ha hab hβ)
  have hdiv : (ν.restrict H) S ≤ ENNReal.ofReal (A * a * β) / ENNReal.ofReal s := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top)).mpr
    simpa only [mul_comm] using hbound
  have heq : A / s * a * β = A * a * β / s := by ring
  simpa only [heq, ENNReal.ofReal_div_of_pos hs] using hdiv

/-- The mesh-restricted stopping rule suffices. Boundedness is needed only
on the current residual `R`, and duration deletion costs `s * ν R`. -/
theorem bounded_stopped_residual (ε : ℝ) (hε : 0 < ε) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
    ∀ (α : Type*) [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
      (b u : α → EuclideanSpace ℝ (Fin 2)),
      Measurable b → Measurable u → ∀ R : Set α, MeasurableSet R →
      (∀ x ∈ R, ‖b x‖ ≤ 1 ∧ ‖u x‖ ≤ 1) →
      ∀ E : Set (α × ℝ), MeasurableSet E → E ⊆ R ×ˢ Icc (0 : ℝ) 1 →
      ∀ s A : ℝ, 0 < s → 0 < A → (D : ℝ) ^ (-η) ≤ s →
      MeshPlankCap D (ν.withDensity (incidenceDuration E)) b u A →
      ∀ F : Finset (ℕ × (Fin 2 → ℤ)),
      (∀ p ∈ E, actualBaseCell D b u p ∈ F) →
      (ν.prod volume) E ≤ ENNReal.ofReal s * ν R +
        ENNReal.ofReal (C * A * (D : ℝ) ^ ε / (s * (D : ℝ) ^ 3) * (F.card : ℝ)) := by
  classical
  obtain ⟨η, hη, C₀, hC₀, Hp⟩ := continuous_mesh_plank_estimate ε hε
  refine ⟨η, 121 * C₀, hη, by positivity, ?_⟩
  intro D hD α _ ν _ b u hb hu R hR hbu E hE hsupport s A hs hA hlong hstop F hF
  have hDp : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  let H : Set α := R ∩ {x | ENNReal.ofReal s ≤ incidenceDuration E x}
  have hH : MeasurableSet H := hR.inter
    (measurableSet_le measurable_const (measurable_incidenceDuration hE))
  have hHR : H ⊆ R := inter_subset_left
  let νH : Measure H := ν.comap ((↑) : H → α)
  let bH : H → EuclideanSpace ℝ (Fin 2) := fun x => b x
  let uH : H → EuclideanSpace ℝ (Fin 2) := fun x => u x
  let J : H → Finset (Fin D) := fun x => positiveTimeMarks D E x
  let V := expandProjectedCells F localCellOffsets
  have hJ : Measurable J := (measurable_positiveTimeMarks D hE).comp measurable_subtype_coe
  have hmap : νH.map ((↑) : H → α) = ν.restrict H := map_comap_subtype_coe hH ν
  have hcap : MeshPlankCap D νH bH uH (A / s) := by
    have hcap' := mesh_incidence_cap_to_prior hD ν E hE b u hb hu H hH hs
      (fun x hx => hx.2) hstop
    intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ
    have h := hcap' c w e₁ e₂ a β he₁ he₂ he ha hab hβ
    rw [← hmap, Measure.map_apply measurable_subtype_coe
      (measurableSet_fullTracePlank b u hb hu c w e₁ e₂ a β)] at h
    exact h
  have hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun p hp => ⟨mem_univ _, (hsupport hp).2⟩
  have hJlong (x : H) : (D : ℝ) ^ (1 - η) ≤ ((J x).card : ℝ) := by
    have hpow : (D : ℝ) ^ (1 - η) = (D : ℝ) * (D : ℝ) ^ (-η) := by
      rw [sub_eq_add_neg, Real.rpow_add hDp, Real.rpow_one]
    rw [hpow]
    exact (mul_le_mul_of_nonneg_left hlong hDp.le).trans
      (positiveTimeMarks_card_lower hD E hunit x hs.le x.property.2)
  have hmarks : (∫⁻ x, ((J x).card : ℝ≥0∞) ∂νH) ≤
      ENNReal.ofReal (C₀ * (A / s) * (D : ℝ) ^ ε / (D : ℝ) ^ 2 * (V.card : ℝ)) := by
    apply Hp D hD H νH bH uH (hb.comp measurable_subtype_coe)
      (hu.comp measurable_subtype_coe) (fun x => hbu x x.property.1) J
      (fun S => hJ (measurableSet_singleton S)) hJlong (A / s) (div_pos hA hs) hcap V
    intro x j hj
    exact positiveTimeMarks_visited_table_at hD b u E F hF x (hbu x x.property.1).2 j hj
  have hhigh : (ν.withDensity (incidenceDuration E)) H ≤
      ENNReal.ofReal (C₀ * (A / s) * (D : ℝ) ^ ε / (D : ℝ) ^ 3 * (V.card : ℝ)) := by
    rw [withDensity_apply _ hH, ← hmap,
      lintegral_map (measurable_incidenceDuration hE) measurable_subtype_coe]
    calc
      _ ≤ ∫⁻ x : H, ENNReal.ofReal (1 / (D : ℝ)) * ((J x).card : ℝ≥0∞) ∂νH := by
        apply lintegral_mono
        intro x
        have h := duration_le_positiveTimeMarks hD E hunit (x : α)
        have heq : ((J x).card : ℝ) / (D : ℝ) = (1 / (D : ℝ)) * ((J x).card : ℝ) := by ring
        rw [heq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast] at h
        exact h
      _ = ENNReal.ofReal (1 / (D : ℝ)) * ∫⁻ x, ((J x).card : ℝ≥0∞) ∂νH := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (1 / (D : ℝ)) *
          ENNReal.ofReal (C₀ * (A / s) * (D : ℝ) ^ ε / (D : ℝ) ^ 2 * (V.card : ℝ)) :=
        mul_le_mul (le_refl _) hmarks zero_le zero_le
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
  have hlow : (ν.withDensity (incidenceDuration E)) (R \ H) ≤ ENNReal.ofReal s * ν R := by
    rw [withDensity_apply _ (hR.diff hH)]
    calc
      _ ≤ ∫⁻ _x in R \ H, ENNReal.ofReal s ∂ν := by
        apply setLIntegral_mono' (hR.diff hH)
        intro x hx
        exact le_of_lt (lt_of_not_ge (fun h => hx.2 ⟨hx.1, h⟩))
      _ = ENNReal.ofReal s * ν (R \ H) := by simp only [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal s * ν R := mul_le_mul (le_refl _) (measure_mono sdiff_subset) zero_le zero_le
  have htotal : (ν.withDensity (incidenceDuration E)) R = (ν.prod volume) E := by
    rw [duration_withDensity_apply ν hE hR, inter_eq_left.mpr]
    intro p hp
    exact ⟨(hsupport hp).1, mem_univ _⟩
  have hsplit : (ν.withDensity (incidenceDuration E)) H +
      (ν.withDensity (incidenceDuration E)) (R \ H) =
      (ν.withDensity (incidenceDuration E)) R := by
    simpa only [inter_eq_right.mpr hHR] using
      (measure_inter_add_sdiff R hH (μ := ν.withDensity (incidenceDuration E)))
  rw [← htotal, ← hsplit]
  have hcard : (V.card : ℝ) ≤ 121 * (F.card : ℝ) := by
    exact_mod_cast expanded_visited_table_card F
  refine (add_le_add hhigh hlow).trans ?_
  rw [add_comm]
  apply add_le_add (le_refl _)
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C₀ * (A / s) * (D : ℝ) ^ ε / (D : ℝ) ^ 3 * (121 * (F.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = _ := by field_simp

end Submission.Obl.k4_initial_horizon_bound
