import Mathlib
import Submission.Obl.k4_profile_density_bounds.Slices

/-!
# Observation densities in sheared coordinates

In product sheared coordinates `(z, w) ∈ ℝ³ × ℝ⁴`, `z = (t, y₁, y₂)` and
`w = (w, s₁, s₂, s₃)`, the native observation at depths `(r, u)` is `z` together with the hidden
bin of `w` and the velocity bins of `(s₁, s₂)`. A density `f` in these coordinates therefore
pushes forward to the density `marg a b f` against `reference = (volume ⊗ count) ⊗ count`: the
integral of `f(z, ·)` over the transverse bin (Fubini). Consequences: total mass, `L¹` contraction,
cell constancy, support and size bounds of these marginals.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_native_base_flattening

open Submission.Obl.k4_profile_density_bounds (Observation reference Base)

/-- Transverse sheared coordinates `(w, s₁, s₂, s₃)` to their hidden bin at width `a` and their
velocity bins at width `b`. -/
noncomputable def tbin (a b : ℝ) (w : Fin 4 → ℝ) : ℤ × (Fin 2 → ℤ) :=
  (⌊w 0 / a⌋, fun j => ⌊![w 1, w 2] j / b⌋)

lemma measurable_tbin (a b : ℝ) : Measurable (tbin a b) := by
  unfold tbin
  refine Measurable.prodMk (by fun_prop) ?_
  refine measurable_pi_iff.mpr fun j => ?_
  fin_cases j <;> simp <;> fun_prop

/-- The observation in product sheared coordinates. -/
noncomputable def sobs (a b : ℝ) (q : (Fin 3 → ℝ) × (Fin 4 → ℝ)) : Observation :=
  ((WithLp.toLp 2 q.1, (tbin a b q.2).1), (tbin a b q.2).2)

lemma measurable_sobs (a b : ℝ) : Measurable (sobs a b) := by
  unfold sobs
  have h := measurable_tbin a b
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
  · exact (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable.comp measurable_fst
  · exact measurable_fst.comp (h.comp measurable_snd)
  · exact measurable_snd.comp (h.comp measurable_snd)

/-- The marginal density on observations of a density in product sheared coordinates. -/
noncomputable def marg (a b : ℝ) (f : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ℝ≥0∞) (y : Observation) :
    ℝ≥0∞ :=
  ∫⁻ w, (tbin a b ⁻¹' {(y.1.2, y.2)}).indicator (fun w => f (WithLp.ofLp y.1.1, w)) w

lemma measurable_marg (a b : ℝ) {f : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (marg a b f) := by
  refine measurable_from_prod_countable_left fun v => ?_
  refine measurable_from_prod_countable_left fun h => ?_
  simp only [marg]
  have hset : MeasurableSet (tbin a b ⁻¹' {(h, v)}) :=
    measurable_tbin a b (measurableSet_singleton _)
  have hm : Measurable (fun p : Base × (Fin 4 → ℝ) =>
      (tbin a b ⁻¹' {(h, v)}).indicator (fun w => f (WithLp.ofLp p.1, w)) p.2) := by
    have : Measurable (fun p : Base × (Fin 4 → ℝ) => f (WithLp.ofLp p.1, p.2)) :=
      hf.comp (Measurable.prodMk
        ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurable.comp measurable_fst) measurable_snd)
    exact this.indicator (measurable_snd hset)
  exact hm.lintegral_prod_right'

/-- Integrals against the reference measure: sum over the bins of base integrals. -/
lemma lintegral_reference {φ : Observation → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y, φ y ∂reference =
      ∫⁻ z : Fin 3 → ℝ, ∑' p : ℤ × (Fin 2 → ℤ), φ ((WithLp.toLp 2 z, p.1), p.2) := by
  rw [reference, lintegral_prod _ hφ.aemeasurable]
  rw [lintegral_prod _ (hφ.lintegral_prod_right').aemeasurable]
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
  congr 1
  funext z
  simp only [lintegral_count]
  exact (ENNReal.tsum_prod (f := fun h v => φ ((WithLp.toLp 2 z, h), v))).symm

theorem map_sobs_withDensity (a b : ℝ) {f : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    Measure.map (sobs a b) (((volume : Measure (Fin 3 → ℝ)).prod
      (volume : Measure (Fin 4 → ℝ))).withDensity f) = reference.withDensity (marg a b f) := by
  ext B hB
  rw [Measure.map_apply (measurable_sobs a b) hB, withDensity_apply _ (measurable_sobs a b hB),
    withDensity_apply _ hB, ← lintegral_indicator (measurable_sobs a b hB),
    ← lintegral_indicator hB,
    lintegral_reference ((measurable_marg a b hf).indicator hB),
    lintegral_prod _ ((hf.indicator (measurable_sobs a b hB)).aemeasurable)]
  congr 1
  funext z
  have hfz : Measurable (fun w : Fin 4 → ℝ => f (z, w)) :=
    hf.comp (Measurable.prodMk measurable_const measurable_id)
  have hind : ∀ p : ℤ × (Fin 2 → ℤ), Measurable (fun w : Fin 4 → ℝ =>
      (tbin a b ⁻¹' {p}).indicator (fun w => f (z, w)) w) := fun p =>
    hfz.indicator (measurable_tbin a b (measurableSet_singleton _))
  have hterm : ∀ p : ℤ × (Fin 2 → ℤ), Measurable (fun w : Fin 4 → ℝ =>
      B.indicator (fun _ => (1 : ℝ≥0∞)) ((WithLp.toLp 2 z, p.1), p.2) *
        (tbin a b ⁻¹' {p}).indicator (fun w => f (z, w)) w) := fun p =>
    measurable_const.mul (hind p)
  calc
    _ = ∫⁻ w, ∑' p : ℤ × (Fin 2 → ℤ), B.indicator (fun _ => (1 : ℝ≥0∞))
          ((WithLp.toLp 2 z, p.1), p.2) * (tbin a b ⁻¹' {p}).indicator (fun w => f (z, w)) w := by
      congr 1
      funext w
      rw [tsum_eq_single (tbin a b w)]
      · have hs : sobs a b (z, w) = ((WithLp.toLp 2 z, (tbin a b w).1), (tbin a b w).2) := rfl
        simp only [indicator, mem_preimage, mem_singleton_iff, ite_true, hs]
        by_cases hw : ((WithLp.toLp 2 z, (tbin a b w).1), (tbin a b w).2) ∈ B
        · simp [hw, hs]
        · simp [hw, hs]
      · intro p hp
        simp [indicator, Ne.symm hp]
    _ = ∑' p : ℤ × (Fin 2 → ℤ), ∫⁻ w, B.indicator (fun _ => (1 : ℝ≥0∞))
          ((WithLp.toLp 2 z, p.1), p.2) * (tbin a b ⁻¹' {p}).indicator (fun w => f (z, w)) w :=
      lintegral_tsum fun p => (hterm p).aemeasurable
    _ = _ := by
      congr 1
      funext p
      rw [lintegral_const_mul _ (hind p)]
      by_cases hp : ((WithLp.toLp 2 z, p.1), p.2) ∈ B
      · simp [indicator_of_mem hp, marg]
      · simp [indicator_of_notMem hp]


/-- Total mass is preserved by the marginal. -/
theorem lintegral_marg (a b : ℝ) {f : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, marg a b f y ∂reference = ∫⁻ q, f q ∂((volume : Measure (Fin 3 → ℝ)).prod
      (volume : Measure (Fin 4 → ℝ))) := by
  have h := congrArg (fun μ : Measure Observation => μ univ) (map_sobs_withDensity a b hf)
  simp only [Measure.map_apply (measurable_sobs a b) MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  exact h.symm

lemma marg_add (a b : ℝ) {f g : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ℝ≥0∞} (hf : Measurable f)
    (y : Observation) : marg a b (fun q => f q + g q) y = marg a b f y + marg a b g y := by
  simp only [marg]
  rw [← lintegral_add_left]
  · congr 1
    funext w
    by_cases hw : w ∈ tbin a b ⁻¹' {(y.1.2, y.2)} <;> simp [indicator, hw]
  · exact (hf.comp (Measurable.prodMk measurable_const measurable_id)).indicator
      (measurable_tbin a b (measurableSet_singleton _))

lemma marg_mono (a b : ℝ) {f g : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ℝ≥0∞} (hfg : ∀ q, f q ≤ g q)
    (y : Observation) : marg a b f y ≤ marg a b g y := by
  refine lintegral_mono fun w => ?_
  by_cases hw : w ∈ tbin a b ⁻¹' {(y.1.2, y.2)} <;> simp [indicator, hw, hfg]

/-- The symmetric truncated difference of two extended reals (their distance when finite). -/
def ediff (x y : ℝ≥0∞) : ℝ≥0∞ := (x - y) + (y - x)

lemma ediff_comm (x y : ℝ≥0∞) : ediff x y = ediff y x := add_comm _ _

lemma measurable_ediff {α : Type*} [MeasurableSpace α] {f g : α → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun x => ediff (f x) (g x)) := by
  unfold ediff
  fun_prop

/-- `L¹` contraction: marginals are at least as close as the densities. -/
theorem lintegral_ediff_marg_le (a b : ℝ) {f g : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ y, ediff (marg a b f y) (marg a b g y) ∂reference ≤
      ∫⁻ q, ediff (f q) (g q) ∂((volume : Measure (Fin 3 → ℝ)).prod
        (volume : Measure (Fin 4 → ℝ))) := by
  have hfg : Measurable (fun q => f q - g q) := by fun_prop
  have hgf : Measurable (fun q => g q - f q) := by fun_prop
  calc
    _ ≤ ∫⁻ y, marg a b (fun q => ediff (f q) (g q)) y ∂reference := by
      refine lintegral_mono fun y => ?_
      have h1 : marg a b f y - marg a b g y ≤ marg a b (fun q => f q - g q) y := by
        rw [tsub_le_iff_left, ← marg_add a b hg]
        exact marg_mono a b (fun q => le_add_tsub) y
      have h2 : marg a b g y - marg a b f y ≤ marg a b (fun q => g q - f q) y := by
        rw [tsub_le_iff_left, ← marg_add a b hf]
        exact marg_mono a b (fun q => le_add_tsub) y
      calc
        ediff (marg a b f y) (marg a b g y) ≤
            marg a b (fun q => f q - g q) y + marg a b (fun q => g q - f q) y :=
          add_le_add h1 h2
        _ = _ := (marg_add a b hfg y).symm
    _ = _ := lintegral_marg a b (measurable_ediff hf hg)

/-- Marginals of densities constant on base cells are constant on base cells. -/
lemma marg_eq_of_cell (a b ρ : ℝ) {f : (Fin 3 → ℝ) × (Fin 4 → ℝ) → ℝ≥0∞}
    (hf : ∀ z z' w, (∀ i, ⌊z i / ρ⌋ = ⌊z' i / ρ⌋) → f (z, w) = f (z', w))
    {x x' : Base} (hx : ∀ i, ⌊x i / ρ⌋ = ⌊x' i / ρ⌋) (h : ℤ) (v : Fin 2 → ℤ) :
    marg a b f ((x, h), v) = marg a b f ((x', h), v) := by
  simp only [marg]
  congr 1
  funext w
  simp only [indicator]
  rw [hf (WithLp.ofLp x) (WithLp.ofLp x') w hx]

end Submission.Obl.k4_native_base_flattening
