-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.Shear.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.TubeMoment

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

def horizontalShear {h : ℝ → ℝ} (hh : Measurable h) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (p.1 + h p.2, p.2)
  invFun p := (p.1 - h p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := (measurable_fst.add (hh.comp measurable_snd)).prodMk measurable_snd
  measurable_invFun := (measurable_fst.sub (hh.comp measurable_snd)).prodMk measurable_snd

lemma measurePreserving_horizontalShear {h : ℝ → ℝ} (hh : Measurable h) :
    MeasurePreserving (horizontalShear hh) := by
  have hs : MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.2 + h p.1)) := by
    change MeasurePreserving _ (volume.prod volume) (volume.prod volume)
    apply (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun z : ℝ => fun u : ℝ => u + h z)
    · exact measurable_snd.add (hh.comp measurable_fst)
    · exact Filter.Eventually.of_forall fun z =>
        (measurePreserving_add_right (volume : Measure ℝ) (h z)).map_eq
  exact (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).comp
    (hs.comp (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)))

lemma volume_horizontalShear_image {h : ℝ → ℝ} (hh : Measurable h) (E : Set (ℝ × ℝ)) :
    volume (horizontalShear hh '' E) = volume E := by
  have he := (measurePreserving_horizontalShear hh).measure_preimage_equiv
    (horizontalShear hh '' E)
  rw [Set.preimage_image_eq _ (horizontalShear hh).injective] at he
  exact he.symm

def parameterTranslation (a b d : ℝ) (p : Space) : Space :=
  WithLp.toLp 2 ![p 0 + a, p 1 + b + d * p 2, p 2]

lemma projection_parameterTranslation {f : ℝ → ℝ} (hf : Measurable f)
    (a b d : ℝ) (p : Space) :
    projection f (parameterTranslation a b d p) =
      horizontalShear (h := fun z => a + (b + d * z) * f z) (by fun_prop) (projection f p) := by
  ext <;> simp [projection, parameterTranslation, horizontalShear] <;> ring

/-- Translated line-parameter copies have exactly the same outer projected area. -/
theorem volume_projection_parameterTranslation {f : ℝ → ℝ} (hf : Measurable f)
    (a b d : ℝ) (E : Set Space) :
    volume (projection f '' (parameterTranslation a b d '' E)) =
      volume (projection f '' E) := by
  have he : projection f '' (parameterTranslation a b d '' E) =
      horizontalShear (h := fun z => a + (b + d * z) * f z) (by fun_prop) ''
        (projection f '' E) := by
    rw [← image_comp, ← image_comp]
    congr 1
    funext p
    exact projection_parameterTranslation hf a b d p
  rw [he, volume_horizontalShear_image]

/-- Removing the common linear term in a slice preserves its cinematic moment. -/
theorem lintegral_graphStrip_shear {ι : Type*} [Fintype ι] (q : ι → Space) (δ c : ℝ) (f : ℝ → ℝ) :
    (∫⁻ p : ℝ × ℝ, multiplicity (fun i => graphStrip δ f c (q i)) p ^ (3 / 2 : ℝ)) =
      ∫⁻ p : ℝ × ℝ, multiplicity (fun i => graphStrip δ f 0 (q i)) p ^ (3 / 2 : ℝ) := by
  classical
  let h : ℝ → ℝ := fun z => -(c * z)
  have hh : Measurable h := by fun_prop
  have hset (i : ι) (p : ℝ × ℝ) :
      p ∈ graphStrip δ f c (q i) ↔ horizontalShear hh p ∈ graphStrip δ f 0 (q i) := by
    change (p.2 ∈ Icc (-1 : ℝ) 1 ∧
        |p.1 - (q i 0 + c * p.2 + q i 1 * f p.2 + q i 2 * p.2 * f p.2)| ≤ δ) ↔
      (p.2 ∈ Icc (-1 : ℝ) 1 ∧
        |p.1 + h p.2 - (q i 0 + 0 * p.2 + q i 1 * f p.2 + q i 2 * p.2 * f p.2)| ≤ δ)
    have he : p.1 + h p.2 -
        (q i 0 + 0 * p.2 + q i 1 * f p.2 + q i 2 * p.2 * f p.2) =
        p.1 - (q i 0 + c * p.2 + q i 1 * f p.2 + q i 2 * p.2 * f p.2) := by
      dsimp [h]
      ring
    rw [he]
  have heq (p : ℝ × ℝ) : multiplicity (fun i => graphStrip δ f c (q i)) p =
      multiplicity (fun i => graphStrip δ f 0 (q i)) (horizontalShear hh p) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : p ∈ graphStrip δ f c (q i)
    · simp [hp, (hset i p).mp hp]
    · simp [hp, mt (hset i p).mpr hp]
  simp_rw [heq]
  exact (measurePreserving_horizontalShear hh).lintegral_comp_emb
    (horizontalShear hh).measurableEmbedding
    (fun p : ℝ × ℝ => multiplicity (fun i => graphStrip δ f 0 (q i)) p ^ (3 / 2 : ℝ))

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
