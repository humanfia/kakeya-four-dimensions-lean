-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o199, session x0700, commit 711b90f1.
-- Source: Submission/Obl/k4_finite_path_candidate_conversion/ModelMeasures.lean.
import Mathlib

/-!
# The measures of the prepared model at one parent

`nuE ν₀ A₀`: the parent world's prior conditioned on the parent assignment `A₀`;
`muE ν₀ A₀ t₀ q S`: the incidences of a prepared set `S ⊆ A₀ × [t₀, t₀ + q]`, time-normalised to
`[0, 1]` and divided by `q · ν₀(A₀)`. Then `muE ≤ nuE × dt`, `muE` lives on `univ × [0,1]`, and
properties of the prepared incidences (resp. of the assigned lines) hold almost everywhere for the
model measures. Written by x0700 for o199.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory

noncomputable section

/-- Lebesgue measure pushed forward by `t ↦ (t - t₀) / q` is `q • vol`. -/
theorem map_volume_tnorm (t₀ q : ℝ) (hq : 0 < q) :
    Measure.map (fun t : ℝ => (t - t₀) / q) volume = ENNReal.ofReal q • volume := by
  have h1 : (fun t : ℝ => (t - t₀) / q) = (fun x => q⁻¹ * x) ∘ (fun t => t + (-t₀)) := by
    funext t; simp [div_eq_inv_mul, sub_eq_add_neg]
  rw [h1, ← Measure.map_map (measurable_const_mul _) (measurable_add_const _),
    Measure.IsAddRightInvariant.map_add_right_eq_self, Real.map_volume_mul_left (inv_ne_zero hq.ne'),
    inv_inv, abs_of_pos hq]

/-- The same restricted to the block `[t₀, t₀+q]`. -/
theorem map_vol_block (t₀ q : ℝ) (hq : 0 < q) :
    Measure.map (fun t : ℝ => (t - t₀) / q) (volume.restrict (Set.Icc t₀ (t₀ + q))) =
      ENNReal.ofReal q • volume.restrict (Set.Icc 0 1) := by
  have hm : Measurable (fun t : ℝ => (t - t₀) / q) := (measurable_id.sub_const t₀).div_const q
  have hpre : (fun t : ℝ => (t - t₀) / q) ⁻¹' Set.Icc 0 1 = Set.Icc t₀ (t₀ + q) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨h0, h1⟩
      rw [le_div_iff₀ hq] at h0; rw [div_le_one hq] at h1
      constructor <;> linarith
    · rintro ⟨h0, h1⟩
      exact ⟨div_nonneg (by linarith) hq.le, (div_le_one hq).mpr (by linarith)⟩
  rw [← hpre, ← Measure.restrict_map hm measurableSet_Icc, map_volume_tnorm t₀ q hq,
    Measure.restrict_smul]

variable {α : Type} [MeasurableSpace α]

/-- Time normalisation of incidences to the parent's block. -/
def tnorm (t₀ q : ℝ) (p : α × ℝ) : α × ℝ := (p.1, (p.2 - t₀) / q)

theorem measurable_tnorm (t₀ q : ℝ) : Measurable (tnorm (α := α) t₀ q) :=
  measurable_fst.prodMk ((measurable_snd.sub_const t₀).div_const q)

/-- The model prior: the parent world's prior conditioned on the parent assignment. -/
def nuE (ν₀ : Measure α) (A₀ : Set α) : Measure α := (ν₀ A₀)⁻¹ • ν₀.restrict A₀

/-- The model incidence measure of a prepared set `S` inside the parent's region. -/
def muE (ν₀ : Measure α) (A₀ : Set α) (t₀ q : ℝ) (S : Set (α × ℝ)) : Measure (α × ℝ) :=
  (ENNReal.ofReal q * ν₀ A₀)⁻¹ • Measure.map (tnorm t₀ q) ((ν₀.prod volume).restrict S)

theorem smul_le_smul_meas {μ μ' : Measure α} (c : ENNReal) (h : μ ≤ μ') : c • μ ≤ c • μ' :=
  Measure.le_iff'.2 fun s => by
    simp only [Measure.smul_apply, smul_eq_mul]; exact mul_le_mul_right (Measure.le_iff'.1 h s) _

theorem nuE_isProb (ν₀ : Measure α) (A₀ : Set α) (h0 : ν₀ A₀ ≠ 0) (hT : ν₀ A₀ ≠ ⊤) :
    IsProbabilityMeasure (nuE ν₀ A₀) := by
  constructor
  rw [nuE, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel h0 hT]

theorem muE_mono (ν₀ : Measure α) (A₀ : Set α) (t₀ q : ℝ) {S S' : Set (α × ℝ)}
    (h : S ⊆ S') : muE ν₀ A₀ t₀ q S ≤ muE ν₀ A₀ t₀ q S' := by
  unfold muE
  exact smul_le_smul_meas _ (Measure.map_mono (Measure.restrict_mono h le_rfl)
    (measurable_tnorm t₀ q))

theorem muE_le_prod (ν₀ : Measure α) [SFinite ν₀] (A₀ : Set α) (t₀ q : ℝ) (hq : 0 < q) {S : Set (α × ℝ)}
    (hS : S ⊆ A₀ ×ˢ Set.Icc t₀ (t₀ + q)) :
    muE ν₀ A₀ t₀ q S ≤ (nuE ν₀ A₀).prod volume := by
  have hmap : Measure.map (tnorm t₀ q) ((ν₀.prod volume).restrict (A₀ ×ˢ Set.Icc t₀ (t₀ + q))) =
      ENNReal.ofReal q • ((ν₀.restrict A₀).prod (volume.restrict (Set.Icc 0 1))) := by
    have hg : Measurable (fun t : ℝ => (t - t₀) / q) := (measurable_id.sub_const t₀).div_const q
    rw [← Measure.prod_restrict, show tnorm (α := α) t₀ q =
      Prod.map id (fun t : ℝ => (t - t₀) / q) from rfl,
      ← Measure.map_prod_map (ν₀.restrict A₀) (volume.restrict (Set.Icc t₀ (t₀ + q)))
        measurable_id hg, Measure.map_id, map_vol_block t₀ q hq, Measure.prod_smul_right]
  calc muE ν₀ A₀ t₀ q S
      ≤ muE ν₀ A₀ t₀ q (A₀ ×ˢ Set.Icc t₀ (t₀ + q)) := muE_mono ν₀ A₀ t₀ q hS
    _ = (ENNReal.ofReal q * ν₀ A₀)⁻¹ • ENNReal.ofReal q •
          ((ν₀.restrict A₀).prod (volume.restrict (Set.Icc 0 1))) := by rw [muE, hmap]
    _ ≤ (ENNReal.ofReal q * ν₀ A₀)⁻¹ • ENNReal.ofReal q • ((ν₀.restrict A₀).prod volume) := by
        exact smul_le_smul_meas _ (smul_le_smul_meas _
          (Measure.prod_mono le_rfl Measure.restrict_le_self))
    _ = (nuE ν₀ A₀).prod volume := by
        rw [nuE, Measure.prod_smul_left, smul_smul]
        congr 1
        have hq' : ENNReal.ofReal q ≠ 0 := by simpa using hq
        rw [ENNReal.mul_inv (Or.inl hq') (Or.inl ENNReal.ofReal_ne_top), mul_comm _ (ν₀ A₀)⁻¹,
          mul_assoc, ENNReal.inv_mul_cancel hq' ENNReal.ofReal_ne_top, mul_one]

theorem muE_compl_block (ν₀ : Measure α) (A₀ : Set α) (t₀ q : ℝ) (hq : 0 < q)
    {S : Set (α × ℝ)} (hS : S ⊆ A₀ ×ˢ Set.Icc t₀ (t₀ + q)) :
    (muE ν₀ A₀ t₀ q S) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hm : MeasurableSet ((Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ : Set (α × ℝ)) :=
    (MeasurableSet.univ.prod measurableSet_Icc).compl
  rw [muE, Measure.smul_apply, Measure.map_apply (measurable_tnorm t₀ q) hm,
    Measure.restrict_apply ((measurable_tnorm t₀ q) hm)]
  have : tnorm t₀ q ⁻¹' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ ∩ S = ∅ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_prod,
      Set.mem_univ, true_and, Set.mem_Icc, tnorm, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hn, hp⟩
    obtain ⟨-, h0, h1⟩ := hS hp
    exact hn ⟨div_nonneg (by linarith) hq.le, (div_le_one hq).mpr (by linarith)⟩
  rw [this, measure_empty, smul_zero]

/-- The inverse time normalisation. -/
def tdenorm (t₀ q : ℝ) (p : α × ℝ) : α × ℝ := (p.1, t₀ + q * p.2)

theorem measurable_tdenorm (t₀ q : ℝ) : Measurable (tdenorm (α := α) t₀ q) :=
  measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd))

theorem image_tnorm_eq (t₀ q : ℝ) (hq : q ≠ 0) (S : Set (α × ℝ)) :
    tnorm t₀ q '' S = tdenorm t₀ q ⁻¹' S := by
  ext y
  simp only [Set.mem_image, Set.mem_preimage, tnorm, tdenorm]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have : t₀ + q * ((p.2 - t₀) / q) = p.2 := by field_simp; ring
    simpa [this] using hp
  · intro hy
    refine ⟨(y.1, t₀ + q * y.2), hy, ?_⟩
    ext
    · rfl
    · simp only; field_simp; ring

/-- A property of all prepared incidences holds almost everywhere for the model incidence measure. -/
theorem ae_muE_of_forall (ν₀ : Measure α) (A₀ : Set α) (t₀ q : ℝ) (hq : q ≠ 0)
    {S : Set (α × ℝ)} (hS : MeasurableSet S) {P : α × ℝ → Prop}
    (h : ∀ p ∈ S, P (tnorm t₀ q p)) : ∀ᵐ y ∂(muE ν₀ A₀ t₀ q S), P y := by
  rw [ae_iff]
  have hsub : {y | ¬ P y} ⊆ (tnorm t₀ q '' S)ᶜ := by
    intro y hy hmem
    obtain ⟨p, hp, rfl⟩ := hmem
    exact hy (h p hp)
  refine measure_mono_null hsub ?_
  have hm : MeasurableSet ((tnorm t₀ q '' S)ᶜ) := by
    rw [image_tnorm_eq t₀ q hq]; exact ((measurable_tdenorm t₀ q) hS).compl
  rw [muE, Measure.smul_apply, Measure.map_apply (measurable_tnorm t₀ q) hm,
    Measure.restrict_apply ((measurable_tnorm t₀ q) hm)]
  have : tnorm t₀ q ⁻¹' (tnorm t₀ q '' S)ᶜ ∩ S = ∅ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_image,
      Set.mem_empty_iff_false, iff_false, not_and, not_not]
    intro hn hp
    exact absurd ⟨p, hp, rfl⟩ hn
  rw [this, measure_empty, smul_zero]

/-- A property of all assigned lines holds almost everywhere for the model prior. -/
theorem ae_nuE_of_forall (ν₀ : Measure α) {A₀ : Set α} (hA₀ : MeasurableSet A₀) {P : α → Prop}
    (h : ∀ l ∈ A₀, P l) : ∀ᵐ l ∂(nuE ν₀ A₀), P l := by
  unfold nuE
  exact Measure.ae_smul_measure (ae_restrict_of_forall_mem hA₀ h) _

/-- The model mass of a set, in original terms. -/
theorem muE_apply (ν₀ : Measure α) (A₀ : Set α) (t₀ q : ℝ) (S : Set (α × ℝ))
    {X : Set (α × ℝ)} (hX : MeasurableSet X) :
    muE ν₀ A₀ t₀ q S X =
      (ENNReal.ofReal q * ν₀ A₀)⁻¹ * (ν₀.prod volume) (tnorm t₀ q ⁻¹' X ∩ S) := by
  rw [muE, Measure.smul_apply, Measure.map_apply (measurable_tnorm t₀ q) hX,
    Measure.restrict_apply ((measurable_tnorm t₀ q) hX), smul_eq_mul]

end

end Submission.Obl.k4_finite_affine_parent_sources
