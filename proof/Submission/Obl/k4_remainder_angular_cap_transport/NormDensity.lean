import Submission.Obl.k4_remainder_angular_cap_transport.AffineCore
/- Adapted from this LOT tree, o064, session x0214, commit a612574618456ee4cdb4d54c4cee48847fe99758,
Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/.
The original file names are recorded beside each adapted group below. -/

/-!
# Observation laws of normalized problems

`Frame.normalized_selected_law`: the normalized selected law of a chart is the pushforward
of the chart's selected law under `normInc` divided by `q ν(A₀)`.
`Frame.obs_normInc`: the normalized observation at scale `B/δ`, width `a`, is the base
change `obsBase` (an affine bijection of `ℝ³`, Jacobian `q⁻¹ det D⁻¹`) of the original
observation at width `δ a`. Hence `Frame.normalized_obs_law` (the normalized observation
law in terms of the original one, paper (2.15)) and `Frame.normalized_obs_ac`: normalized
observation laws are absolutely continuous with respect to `volume.prod count`, so the
density clauses of the normalized problem can be met with Radon-Nikodym derivatives.
-/
namespace Submission.Obl.k4_remainder_angular_cap_transport.Geometry
open MeasureTheory MvPolynomial

namespace Frame
variable (F : Frame)

/-- The normalization map on incidences. -/
noncomputable def normInc (p : Incidence) : Incidence := (F.normTraj p.1, (p.2 - F.t₀) / F.q)

theorem measurable_normInc : Measurable F.normInc :=
  ((ChartSystem.measurable_normTraj F).comp measurable_fst).prodMk
    ((measurable_snd.sub_const _).div_const _)

/-- Incidences of an event inside the chart's assignment and block are exactly the
preimages of the normalized event, inside the assignment. -/
theorem mem_iff_normEvent (hq : 0 < F.q) (hD : IsUnit F.D.det) {A₀ : Set Trajectory}
    {E : Set Incidence} (hsub : ∀ p ∈ E, p.1 ∈ A₀ ∧ p.2 ∈ Set.Icc F.t₀ (F.t₀ + F.q))
    (p : Incidence) : p ∈ E ↔ p.1 ∈ A₀ ∧ F.normInc p ∈ F.normEvent A₀ E := by
  have hl : F.denormTraj (F.normTraj p.1) = p.1 := F.denormTraj_normTraj hq.ne' hD p.1
  have ht : F.t₀ + F.q * ((p.2 - F.t₀) / F.q) = p.2 := by field_simp; ring
  constructor
  · intro hp
    obtain ⟨hA', ht'⟩ := hsub p hp
    refine ⟨hA', ?_, ?_, ?_⟩
    · show F.denormTraj (F.normTraj p.1) ∈ A₀
      rw [hl]; exact hA'
    · show (p.2 - F.t₀) / F.q ∈ Set.Icc (0 : ℝ) 1
      refine ⟨div_nonneg (by linarith [ht'.1]) hq.le, ?_⟩
      rw [div_le_one hq]; linarith [ht'.2]
    · show (F.denormTraj (F.normTraj p.1), F.t₀ + F.q * ((p.2 - F.t₀) / F.q)) ∈ E
      rw [hl, ht]; exact hp
  · rintro ⟨_, _, _, h3⟩
    have h3' : (F.denormTraj (F.normTraj p.1), F.t₀ + F.q * ((p.2 - F.t₀) / F.q)) ∈ E := h3
    rw [hl, ht] at h3'
    exact h3'

/-- **The normalized selected law** is the pushforward of the chart's selected law
divided by `q ν(A₀)`. -/
theorem normalized_selected_law (hq : 0 < F.q) (hD : IsUnit F.D.det) (ν : Measure Trajectory)
    [IsFiniteMeasure ν] {A₀ : Set Trajectory} {E : Set Incidence} (hA : MeasurableSet A₀)
    (hE : MeasurableSet E)
    (hsub : ∀ p ∈ E, p.1 ∈ A₀ ∧ p.2 ∈ Set.Icc F.t₀ (F.t₀ + F.q)) :
    (((ν A₀)⁻¹ • Measure.map F.normTraj (ν.restrict A₀)).prod volume).restrict
        (F.normEvent A₀ E) =
      (ν A₀ * ENNReal.ofReal F.q)⁻¹ • Measure.map F.normInc ((ν.prod volume).restrict E) := by
  have hmE := F.measurableSet_normEvent hA hE
  ext S hS
  rw [Measure.restrict_apply hS, Measure.smul_apply, Measure.map_apply (F.measurable_normInc) hS,
    Measure.restrict_apply (F.measurable_normInc hS), Measure.prod_smul_left, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul]
  have key := prod_lift_apply ν F.normTraj (ChartSystem.measurable_normTraj F) A₀ hA F.t₀ F.q hq
    (S ∩ F.normEvent A₀ E) (hS.inter hmE)
  have hset : {p : Incidence | p.1 ∈ A₀ ∧ (F.normTraj p.1, (p.2 - F.t₀) / F.q) ∈
      S ∩ F.normEvent A₀ E} = F.normInc ⁻¹' S ∩ E := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    rw [F.mem_iff_normEvent hq hD hsub p]
    show _ ↔ F.normInc p ∈ S ∧ p.1 ∈ A₀ ∧ F.normInc p ∈ F.normEvent A₀ E
    tauto
  rw [hset] at key
  rw [key, ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl (measure_ne_top _ _))]
  set X := ((Measure.map F.normTraj (ν.restrict A₀)).prod volume) (S ∩ F.normEvent A₀ E)
  have hq0 : ENNReal.ofReal F.q ≠ 0 := by simpa using hq
  calc (ν A₀)⁻¹ * X = (ν A₀)⁻¹ * ((ENNReal.ofReal F.q)⁻¹ * ENNReal.ofReal F.q) * X := by
        rw [ENNReal.inv_mul_cancel hq0 ENNReal.ofReal_ne_top]; ring
    _ = (ν A₀)⁻¹ * (ENNReal.ofReal F.q)⁻¹ * (ENNReal.ofReal F.q * X) := by ring


/-- The base change of observations: `(t, y) ↦ ((t - t₀)/q, D⁻¹ (y - c - t u))`. -/
noncomputable def obsBase (v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(v 0 - F.t₀) / F.q,
    F.D⁻¹ 0 0 * (v 1 - F.c 0 - v 0 * F.u 0) + F.D⁻¹ 0 1 * (v 2 - F.c 1 - v 0 * F.u 1),
    F.D⁻¹ 1 0 * (v 1 - F.c 0 - v 0 * F.u 0) + F.D⁻¹ 1 1 * (v 2 - F.c 1 - v 0 * F.u 1)]

theorem graphPoint_normTraj_three (hq : F.q ≠ 0) (l : Trajectory) (t : ℝ) :
    graphPoint (F.normTraj l) ((t - F.t₀) / F.q) 3 = graphPoint l t 3 := by
  simp [graphPoint, normTraj, normCoeff]
  field_simp
  ring

end Frame

/-- The observation of an incidence at hidden width `a` and derivative scale `B`, as in the
frozen statement. -/
noncomputable def obs (B a : ℝ) (p : Incidence) : EuclideanSpace ℝ (Fin 3) × ℤ :=
  (WithLp.toLp 2 ![p.2, graphPoint p.1 p.2 1, graphPoint p.1 p.2 2],
    ⌊B * graphPoint p.1 p.2 3 / a⌋)

namespace Frame
variable (F : Frame)

/-- **Observation factorization**: the normalized observation at scale `B / δ` and width
`a` of a normalized incidence is the base change of the original observation at width
`δ a`. -/
theorem obs_normInc (hq : F.q ≠ 0) (B δ a : ℝ) (hδ : δ ≠ 0) (p : Incidence) :
    obs (B / δ) a (F.normInc p) = Prod.map F.obsBase id (obs B (δ * a) p) := by
  have h3 := F.graphPoint_normTraj_three hq p.1 p.2
  simp only [obs, normInc, Prod.map, id]
  congr 1
  · ext i
    fin_cases i <;> simp [obsBase, graphPoint, normTraj, normCoeff] <;> field_simp <;> ring
  · rw [h3]
    congr 1
    field_simp


/-- The linear part of the observation base change. -/
noncomputable def obsMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![F.q⁻¹, 0, 0;
     -(F.D⁻¹ 0 0 * F.u 0 + F.D⁻¹ 0 1 * F.u 1), F.D⁻¹ 0 0, F.D⁻¹ 0 1;
     -(F.D⁻¹ 1 0 * F.u 0 + F.D⁻¹ 1 1 * F.u 1), F.D⁻¹ 1 0, F.D⁻¹ 1 1]

theorem obsBase_eq (v : EuclideanSpace ℝ (Fin 3)) :
    F.obsBase v = WithLp.toLp 2 (F.obsMatrix.mulVec (WithLp.ofLp v) +
      WithLp.ofLp (F.obsBase 0)) := by
  ext i
  fin_cases i <;> simp [obsBase, obsMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    field_simp <;> ring

theorem det_obsMatrix : F.obsMatrix.det = F.q⁻¹ * F.D⁻¹.det := by
  rw [obsMatrix, Matrix.det_fin_three, Matrix.det_fin_two]
  simp
  ring

theorem det_obsMatrix_ne_zero (hq : F.q ≠ 0) (hD : IsUnit F.D.det) : F.obsMatrix.det ≠ 0 := by
  rw [det_obsMatrix, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have : F.D.det ≠ 0 := hD.ne_zero
  simp [hq, this]

/-- Lebesgue measure under the observation base change. -/
theorem map_obsBase_volume (hq : F.q ≠ 0) (hD : IsUnit F.D.det) :
    Measure.map F.obsBase volume = ENNReal.ofReal |F.obsMatrix.det|⁻¹ • volume := by
  have hfun : F.obsBase = (WithLp.toLp 2) ∘ (fun x => x + WithLp.ofLp (F.obsBase 0)) ∘
      (Matrix.toLin' F.obsMatrix) ∘ (WithLp.ofLp (p := 2)) := by
    funext v; rw [F.obsBase_eq v]; simp [Matrix.toLin'_apply]
  have h1 := (PiLp.volume_preserving_ofLp (Fin 3))
  have h2 := (PiLp.volume_preserving_toLp (Fin 3))
  have hL : Measurable (Matrix.toLin' F.obsMatrix) := (LinearMap.continuous_on_pi _).measurable
  have hadd : Measurable (fun x : Fin 3 → ℝ => x + WithLp.ofLp (F.obsBase 0)) :=
    measurable_add_const _
  have hcomp : Measure.map (WithLp.toLp 2 ∘ (fun x => x + WithLp.ofLp (F.obsBase 0)) ∘
      (Matrix.toLin' F.obsMatrix) ∘ (WithLp.ofLp (p := 2))) volume =
      Measure.map (WithLp.toLp 2) (Measure.map (fun x => x + WithLp.ofLp (F.obsBase 0))
        (Measure.map (Matrix.toLin' F.obsMatrix) (Measure.map (WithLp.ofLp (p := 2))
          (volume : Measure (EuclideanSpace ℝ (Fin 3)))))) := by
    rw [Measure.map_map hL h1.measurable, Measure.map_map hadd (hL.comp h1.measurable),
      Measure.map_map h2.measurable (hadd.comp (hL.comp h1.measurable))]
  rw [hfun, hcomp, h1.map_eq,
    Real.map_matrix_volume_pi_eq_smul_volume_pi (F.det_obsMatrix_ne_zero hq hD),
    Measure.map_smul, map_add_right_eq_self, Measure.map_smul, h2.map_eq, abs_inv]
  all_goals first | exact h2.measurable.aemeasurable | exact hadd.aemeasurable

end Frame

theorem measurable_obs (B a : ℝ) : Measurable (obs B a) := by
  unfold obs
  refine Measurable.prodMk ?_ ?_
  · refine (PiLp.volume_preserving_toLp (Fin 3)).measurable.comp ?_
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i <;> simp [graphPoint] <;> fun_prop
  · exact Int.measurable_floor.comp (by simp [graphPoint]; fun_prop)

namespace Frame
variable (F : Frame)

theorem measurable_obsBase : Measurable F.obsBase := by
  have : F.obsBase = (WithLp.toLp 2) ∘ (fun x => x + WithLp.ofLp (F.obsBase 0)) ∘
      (Matrix.toLin' F.obsMatrix) ∘ (WithLp.ofLp (p := 2)) := by
    funext v; rw [F.obsBase_eq v]; simp [Matrix.toLin'_apply]
  rw [this]
  exact (PiLp.volume_preserving_toLp (Fin 3)).measurable.comp ((measurable_add_const _).comp
    ((LinearMap.continuous_on_pi _).measurable.comp
      (PiLp.volume_preserving_ofLp (Fin 3)).measurable))

/-- The normalized observation law, in terms of the original one. -/
theorem normalized_obs_law (hq : 0 < F.q) (hD : IsUnit F.D.det) (ν : Measure Trajectory)
    [IsFiniteMeasure ν] {A₀ : Set Trajectory} {E : Set Incidence} (hA : MeasurableSet A₀)
    (hE : MeasurableSet E) (hsub : ∀ p ∈ E, p.1 ∈ A₀ ∧ p.2 ∈ Set.Icc F.t₀ (F.t₀ + F.q))
    (B δ a : ℝ) (hδ : δ ≠ 0) :
    Measure.map (obs (B / δ) a) ((((ν A₀)⁻¹ • Measure.map F.normTraj (ν.restrict A₀)).prod
        volume).restrict (F.normEvent A₀ E)) =
      (ν A₀ * ENNReal.ofReal F.q)⁻¹ • Measure.map (Prod.map F.obsBase id)
        (Measure.map (obs B (δ * a)) ((ν.prod volume).restrict E)) := by
  rw [F.normalized_selected_law hq hD ν hA hE hsub, Measure.map_smul,
    Measure.map_map (measurable_obs _ _) F.measurable_normInc,
    Measure.map_map (F.measurable_obsBase.prodMap measurable_id) (measurable_obs _ _)]
  · congr 2
    funext p
    exact F.obs_normInc hq.ne' B δ a hδ p
  · exact (measurable_obs _ _).aemeasurable

/-- Normalized observation laws are absolutely continuous, so their densities exist. -/
theorem normalized_obs_ac (hq : 0 < F.q) (hD : IsUnit F.D.det) (ν : Measure Trajectory)
    [IsFiniteMeasure ν] {A₀ : Set Trajectory} {E E₀ : Set Incidence} (hA : MeasurableSet A₀)
    (hE : MeasurableSet E) (hEE : E ⊆ E₀)
    (hsub : ∀ p ∈ E, p.1 ∈ A₀ ∧ p.2 ∈ Set.Icc F.t₀ (F.t₀ + F.q))
    (B δ a : ℝ) (hδ : δ ≠ 0) (g : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal)
    (hg : Measure.map (obs B (δ * a)) ((ν.prod volume).restrict E₀) =
      (volume.prod Measure.count).withDensity g) :
    Measure.map (obs (B / δ) a) ((((ν A₀)⁻¹ • Measure.map F.normTraj (ν.restrict A₀)).prod
        volume).restrict (F.normEvent A₀ E)) ≪ volume.prod Measure.count := by
  rw [F.normalized_obs_law hq hD ν hA hE hsub B δ a hδ]
  refine Measure.AbsolutelyContinuous.smul_left ?_ _
  have hφ : Measurable (Prod.map F.obsBase (id : ℤ → ℤ)) :=
    F.measurable_obsBase.prodMap measurable_id
  have h1 : Measure.map (obs B (δ * a)) ((ν.prod volume).restrict E) ≪
      volume.prod Measure.count := by
    have hle : Measure.map (obs B (δ * a)) ((ν.prod volume).restrict E) ≤
        Measure.map (obs B (δ * a)) ((ν.prod volume).restrict E₀) :=
      Measure.map_mono (Measure.restrict_mono hEE le_rfl) (measurable_obs _ _)
    refine Measure.absolutelyContinuous_of_le hle |>.trans ?_
    rw [hg]
    exact withDensity_absolutelyContinuous _ _
  refine (h1.map hφ).trans ?_
  rw [← Measure.map_prod_map _ _ F.measurable_obsBase measurable_id,
    F.map_obsBase_volume hq.ne' hD, Measure.map_id, Measure.prod_smul_left]
  exact Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) _

end Frame
end Submission.Obl.k4_remainder_angular_cap_transport.Geometry
