import Mathlib

/-!
# The dummy quadratic lift: coefficients, measurability and masses

For a scalar family `a : α → EuclideanSpace ℝ (Fin 3)` (coefficients of the quadratic
`a 0 + t * a 1 + t ^ 2 * a 2`) the dummy lift is the planar affine family indexed by
`z = (l, s) : α × ℝ` with intercept `(a l 0, s)` and slope `(a l 1 - s, a l 2)`, so that
its trace at time `t` is `(a l 0 + t * (a l 1 - s), s + t * a l 2)` and the scalar trace is
recovered as `x + t * y`.  The dummy variable `s` is clipped to `[0,1]`, which keeps the
coefficients bounded for every `s` and changes nothing on `α × [0,1]`, where the lifted
prior `ν.prod (volume.restrict [0,1])` lives.
-/

open MeasureTheory

namespace Submission.Obl.k4_scalar_lift_plank

/-- Clipping of the dummy variable to `[0,1]`. -/
noncomputable def clip (s : ℝ) : ℝ := max 0 (min s 1)

lemma clip_of_mem {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : clip s = s := by
  rw [clip, min_eq_left hs.2, max_eq_right hs.1]

lemma clip_nonneg (s : ℝ) : 0 ≤ clip s := le_max_left _ _

lemma clip_le_one (s : ℝ) : clip s ≤ 1 := max_le zero_le_one (min_le_right _ _)

lemma abs_clip_le_one (s : ℝ) : |clip s| ≤ 1 := by
  rw [abs_of_nonneg (clip_nonneg s)]; exact clip_le_one s

lemma measurable_clip : Measurable clip :=
  (continuous_const.max (continuous_id.min continuous_const)).measurable

variable {α : Type*}

/-- Intercept of the dummy lift. -/
noncomputable def liftB (a : α → EuclideanSpace ℝ (Fin 3)) (z : α × ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![a z.1 0, clip z.2]

/-- Slope of the dummy lift. -/
noncomputable def liftU (a : α → EuclideanSpace ℝ (Fin 3)) (z : α × ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![a z.1 1 - clip z.2, a z.1 2]

/-- The labeled set of the lift: the dummy variable does not change the labels. -/
def liftE (E : Set (α × ℝ)) : Set ((α × ℝ) × ℝ) := {q | (q.1.1, q.2) ∈ E}

lemma mem_liftE {E : Set (α × ℝ)} {z : α × ℝ} {t : ℝ} : (z, t) ∈ liftE E ↔ (z.1, t) ∈ E :=
  Iff.rfl

lemma liftE_section (E : Set (α × ℝ)) (z : α × ℝ) :
    {t : ℝ | (z, t) ∈ liftE E} = {t : ℝ | (z.1, t) ∈ E} := rfl

lemma liftE_subset {E : Set (α × ℝ)} (hE : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) :
    liftE E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 :=
  fun _ hq => ⟨trivial, (hE hq).2⟩

/-! ### The lifted trace -/

lemma liftB_add_smul_liftU (a : α → EuclideanSpace ℝ (Fin 3)) (z : α × ℝ) (t : ℝ) :
    liftB a z + t • liftU a z
      = WithLp.toLp 2 ![a z.1 0 + t * (a z.1 1 - clip z.2), clip z.2 + t * a z.1 2] := by
  ext i
  fin_cases i <;> simp [liftB, liftU]

lemma liftB_add_smul_liftU_of_mem (a : α → EuclideanSpace ℝ (Fin 3)) {z : α × ℝ}
    (hz : z.2 ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    liftB a z + t • liftU a z
      = WithLp.toLp 2 ![a z.1 0 + t * (a z.1 1 - z.2), z.2 + t * a z.1 2] := by
  rw [liftB_add_smul_liftU, clip_of_mem hz]

lemma lift_trace_zero (a : α → EuclideanSpace ℝ (Fin 3)) (z : α × ℝ) (t : ℝ) :
    (liftB a z + t • liftU a z) 0 = a z.1 0 + t * (a z.1 1 - clip z.2) := by
  rw [liftB_add_smul_liftU]; simp

lemma lift_trace_one (a : α → EuclideanSpace ℝ (Fin 3)) (z : α × ℝ) (t : ℝ) :
    (liftB a z + t • liftU a z) 1 = clip z.2 + t * a z.1 2 := by
  rw [liftB_add_smul_liftU]; simp

/-- The scalar trace is recovered from the lifted one as `x + t * y`. -/
lemma lift_trace_recover (a : α → EuclideanSpace ℝ (Fin 3)) (z : α × ℝ) (t : ℝ) :
    (liftB a z + t • liftU a z) 0 + t * (liftB a z + t • liftU a z) 1
      = a z.1 0 + t * a z.1 1 + t ^ 2 * a z.1 2 := by
  rw [lift_trace_zero, lift_trace_one]; ring

/-! ### Measurability -/

lemma measurable_coord (i : Fin 3) :
    Measurable fun x : EuclideanSpace ℝ (Fin 3) => x i :=
  ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).measurable

lemma measurable_liftB {a : α → EuclideanSpace ℝ (Fin 3)} [MeasurableSpace α]
    (ha : Measurable a) : Measurable (liftB a) := by
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
  fin_cases i
  · exact (measurable_coord 0).comp (ha.comp measurable_fst)
  · exact measurable_clip.comp measurable_snd

lemma measurable_liftU {a : α → EuclideanSpace ℝ (Fin 3)} [MeasurableSpace α]
    (ha : Measurable a) : Measurable (liftU a) := by
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => ?_)
  fin_cases i
  · exact ((measurable_coord 1).comp (ha.comp measurable_fst)).sub
      (measurable_clip.comp measurable_snd)
  · exact (measurable_coord 2).comp (ha.comp measurable_fst)

lemma measurableSet_liftE [MeasurableSpace α] {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    MeasurableSet (liftE E) :=
  hE.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

/-! ### Norms of the lifted coefficients -/

lemma norm_toLp_two_le (x y : ℝ) :
    ‖(WithLp.toLp 2 ![x, y] : EuclideanSpace ℝ (Fin 2))‖ ≤ |x| + |y| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs,
    sq_abs]
  nlinarith [abs_nonneg x, abs_nonneg y, sq_abs x, sq_abs y]

lemma abs_coord_le (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i
  rwa [Real.norm_eq_abs] at this

lemma norm_liftB_le (a : α → EuclideanSpace ℝ (Fin 3)) (z : α × ℝ) :
    ‖liftB a z‖ ≤ ‖a z.1‖ + 1 :=
  (norm_toLp_two_le _ _).trans (add_le_add (abs_coord_le _ _) (abs_clip_le_one _))

lemma norm_liftU_le (a : α → EuclideanSpace ℝ (Fin 3)) (z : α × ℝ) :
    ‖liftU a z‖ ≤ 2 * ‖a z.1‖ + 1 := by
  refine (norm_toLp_two_le _ _).trans ?_
  have h1 := abs_coord_le (a z.1) 1
  have h2 := abs_coord_le (a z.1) 2
  have h3 := abs_clip_le_one z.2
  have h4 := abs_sub (a z.1 1) (clip z.2)
  linarith

/-! ### Masses of the lifted prior -/

variable [MeasurableSpace α]

lemma lift_prior_univ (ν : Measure α) :
    (ν.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) Set.univ = ν Set.univ := by
  rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- The lifted labeled mass equals the original labeled mass. -/
lemma lift_label_mass (ν : Measure α) {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    ((ν.prod (volume.restrict (Set.Icc (0 : ℝ) 1))).prod volume) (liftE E)
      = (ν.prod volume) E := by
  rw [Measure.prod_apply (measurableSet_liftE hE), Measure.prod_apply hE]
  have hg : Measurable fun l : α => volume (Prod.mk l ⁻¹' E) :=
    measurable_measure_prodMk_left hE
  have hsec : ∀ z : α × ℝ, Prod.mk z ⁻¹' liftE E = Prod.mk z.1 ⁻¹' E := fun _ => rfl
  simp_rw [hsec]
  rw [lintegral_prod (fun z : α × ℝ => volume (Prod.mk z.1 ⁻¹' E))
    (hg.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- The slab where the dummy variable leaves `[0,1]` is null for the lifted prior. -/
lemma lift_prior_off_null (ν : Measure α) :
    (ν.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) (Set.univ ×ˢ (Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  rw [Measure.prod_prod, Measure.restrict_apply' measurableSet_Icc, Set.compl_inter_self,
    measure_empty, mul_zero]

/-- Two sets that agree where the dummy variable is in `[0,1]` are compared by the
lifted prior. -/
lemma lift_prior_mono_of_agree (ν : Measure α) {S T : Set (α × ℝ)}
    (h : ∀ z ∈ S, z.2 ∈ Set.Icc (0 : ℝ) 1 → z ∈ T) :
    (ν.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) S
      ≤ (ν.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) T := by
  set μ := ν.prod (volume.restrict (Set.Icc (0 : ℝ) 1))
  have hsub : S ⊆ T ∪ Set.univ ×ˢ (Set.Icc (0 : ℝ) 1)ᶜ := by
    intro z hz
    by_cases hz2 : z.2 ∈ Set.Icc (0 : ℝ) 1
    · exact Or.inl (h z hz hz2)
    · exact Or.inr ⟨trivial, hz2⟩
  calc μ S ≤ μ (T ∪ Set.univ ×ˢ (Set.Icc (0 : ℝ) 1)ᶜ) := measure_mono hsub
    _ ≤ μ T + μ (Set.univ ×ˢ (Set.Icc (0 : ℝ) 1)ᶜ) := measure_union_le _ _
    _ = μ T := by rw [lift_prior_off_null, add_zero]

/-- The plank set of the lift (clipped dummy variable, lifted labels) has at most the
lifted-prior mass of the plank set written with the unclipped dummy variable. -/
lemma lift_plank_transfer (ν : Measure α) (a : α → EuclideanSpace ℝ (Fin 3))
    (E : Set (α × ℝ)) (r : ENNReal) (b₀ w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (u v : ℝ) :
    (ν.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
        {l : α × ℝ | r ≤ volume {t : ℝ | (l, t) ∈ liftE E} ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            |inner ℝ (liftB a l + t • liftU a l - b₀ - t • w) e₁| ≤ u ∧
            |inner ℝ (liftB a l + t • liftU a l - b₀ - t • w) e₂| ≤ v}
      ≤ (ν.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
        {z : α × ℝ | r ≤ volume {t : ℝ | (z.1, t) ∈ E} ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            |inner ℝ (WithLp.toLp 2 ![a z.1 0 + t * (a z.1 1 - z.2), z.2 + t * a z.1 2]
              - b₀ - t • w) e₁| ≤ u ∧
            |inner ℝ (WithLp.toLp 2 ![a z.1 0 + t * (a z.1 1 - z.2), z.2 + t * a z.1 2]
              - b₀ - t • w) e₂| ≤ v} := by
  refine lift_prior_mono_of_agree ν fun z hz hz2 => ⟨hz.1, fun t ht => ?_⟩
  have h := hz.2 t ht
  rwa [liftB_add_smul_liftU_of_mem a hz2] at h

end Submission.Obl.k4_scalar_lift_plank
