import Submission.Obl.k4_native_shear_source_transport.ShearedDensity
import Submission.Obl.k4_native_base_flattening.Bridge
import Submission.Lib.K4MarginalAveraging.CountedMarginal

namespace Submission.Obl.k4_horizon_light_cell_mass

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_native_base_flattening (ediff measurable_ediff)

abbrev Raw := Fin 7 → ℝ
abbrev Base := EuclideanSpace ℝ (Fin 3)
abbrev Hidden := Fin 4 → ℝ
abbrev State := (ℕ × (Fin 6 → ℝ)) × ℝ
abbrev Observation := Base × ℤ

noncomputable def reference : Measure Observation := volume.prod Measure.count

noncomputable def rawSplit : Raw ≃ᵐ Hidden × Base :=
  Submission.Obl.k4_native_shear_source_transport.baseFiberEquiv.trans MeasurableEquiv.prodComm

lemma rawSplit_measurePreserving : MeasurePreserving rawSplit volume
    ((volume : Measure Hidden).prod (volume : Measure Base)) :=
  Measure.measurePreserving_swap.comp
    Submission.Obl.k4_native_shear_source_transport.measurePreserving_baseFiberEquiv

lemma rawSplit_symm_eq (w : Hidden) (z : Base) :
    rawSplit.symm (w, z) =
      Submission.Obl.k4_native_base_flattening.join (WithLp.ofLp z, w) := by
  apply rawSplit.injective
  rw [MeasurableEquiv.apply_symm_apply]
  change (w, z) = ((Submission.Obl.k4_native_shear_source_transport.baseFiberEquiv
    (Submission.Obl.k4_native_base_flattening.join (WithLp.ofLp z, w))).2,
    (Submission.Obl.k4_native_shear_source_transport.baseFiberEquiv
      (Submission.Obl.k4_native_base_flattening.join (WithLp.ofLp z, w))).1)
  rw [Submission.Obl.k4_native_shear_source_transport.baseFiberEquiv_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> rfl
  · apply WithLp.ofLp_injective
    ext i; fin_cases i <;> rfl

noncomputable def rawChart (p : State) : Raw :=
  ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4,
    p.1.2 2 + p.2 * p.1.2 5, p.1.2 3, p.1.2 4, p.1.2 5]

lemma rawChart_measurable : Measurable rawChart := by
  apply Measurable.of_eval
  intro i
  fin_cases i <;> dsimp [rawChart] <;> fun_prop

noncomputable def pureMap (B a : ℝ) (p : State) : Observation :=
  (WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4],
    ⌊B * (p.1.2 2 + p.2 * p.1.2 5) / a⌋)

noncomputable def rawObserve (B a : ℝ) (x : Raw) : Observation :=
  (WithLp.toLp 2 ![x 0, x 1, x 2], ⌊B * x 3 / a⌋)

noncomputable def hiddenLabel (B a : ℝ) (w : Hidden) : ℤ := ⌊B * w 0 / a⌋

lemma hiddenLabel_measurable (B a : ℝ) : Measurable (hiddenLabel B a) := by
  unfold hiddenLabel
  fun_prop

lemma rawObserve_measurable (B a : ℝ) : Measurable (rawObserve B a) := by
  apply Measurable.prodMk
  · apply (MeasurableEquiv.toLp 2 _).measurable.comp
    apply Measurable.of_eval
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  · fun_prop

lemma pureMap_eq (B a : ℝ) : pureMap B a = rawObserve B a ∘ rawChart := rfl

lemma pureMap_measurable (B a : ℝ) : Measurable (pureMap B a) :=
  (rawObserve_measurable B a).comp rawChart_measurable

/-- The native incidence law in the seven sheared coordinates, using the accepted source law. -/
theorem rawChart_law {m : ℕ} (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)) (hA : ∀ j, MeasurableSet (A j))
    (ν : Measure (ℕ × (Fin 6 → ℝ)))
    (hν : ν = ∑ j, ENNReal.ofReal (c j) • Measure.map (fun x => (i j, x)) (volume.restrict (A j)))
    (E : Set State) (hE : MeasurableSet E) :
    ((ν.prod volume).restrict E).map rawChart =
      volume.withDensity (fun x => ENNReal.ofReal (∑ j,
        Submission.Obl.k4_native_base_flattening.nativeComponentDensity (c j) (A j)
          (Submission.Obl.k4_native_base_flattening.eventFiber E (i j)) x)) := by
  have h := Submission.Obl.k4_native_shear_source_transport.map_native_of_factor
    rawChart id rawChart_measurable measurable_id (by
      intro i x t
      rw [Submission.Obl.k4_native_shear_source_transport.shearEquiv_apply]
      rfl) c i hA hν hE
  rw [Measure.map_id,
    Submission.Obl.k4_native_shear_source_transport.nativeDensity_eq_ofReal hc] at h
  rw [h]
  congr 1
  funext x
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  classical
  have hset : x ∈ Submission.Obl.k4_native_shear_source_transport.shearedPiece (A j) (i j) E ↔
      Submission.Obl.k4_native_base_flattening.nativeCoefficients x ∈ A j ∧
        Submission.Obl.k4_native_base_flattening.nativeEventPoint x ∈
          Submission.Obl.k4_native_base_flattening.eventFiber E (i j) := by
    rw [Submission.Obl.k4_native_base_flattening.nativeEventPoint_mem_eventFiber]
    simp only [Submission.Obl.k4_native_shear_source_transport.shearedPiece, mem_preimage,
      Submission.Obl.k4_native_shear_source_transport.shearEquiv_symm_apply]
    rfl
  change c j * _ = _
  unfold Submission.Obl.k4_native_base_flattening.nativeComponentDensity
  by_cases hx : x ∈ Submission.Obl.k4_native_shear_source_transport.shearedPiece (A j) (i j) E
  · simp [hx, hset.mp hx]
  · have hn := not_iff_not.mpr hset |>.mp hx
    simp [hx, hn]

noncomputable def pureMarginal (B a : ℝ) (f : Raw → ℝ≥0∞) : Observation → ℝ≥0∞ :=
  Submission.Lib.K4MarginalAveraging.countedMarginal volume
    (fun w z => f (rawSplit.symm (w, z))) (fun q => hiddenLabel B a q.1)

lemma pureMarginal_measurable (B a : ℝ) {f : Raw → ℝ≥0∞} (hf : Measurable f) :
    Measurable (pureMarginal B a f) :=
  Submission.Lib.K4MarginalAveraging.countedMarginal_measurable volume
    (fun w z => f (rawSplit.symm (w, z))) (hf.comp rawSplit.symm.measurable) _ ((hiddenLabel_measurable B a).comp measurable_fst)

lemma rawObserve_eq_split (B a : ℝ) (x : Raw) :
    rawObserve B a x = ((rawSplit x).2, hiddenLabel B a (rawSplit x).1) := by
  change rawObserve B a x = ((Submission.Obl.k4_native_shear_source_transport.baseFiberEquiv x).1,
    hiddenLabel B a (Submission.Obl.k4_native_shear_source_transport.baseFiberEquiv x).2)
  rw [Submission.Obl.k4_native_shear_source_transport.baseFiberEquiv_apply]
  rfl

lemma map_rawObserve_withDensity (B a : ℝ) {f : Raw → ℝ≥0∞} (hf : Measurable f) :
    (volume.withDensity f).map (rawObserve B a) =
      reference.withDensity (pureMarginal B a f) := by
  have h := Submission.Obl.k4_native_shear_source_transport.map_withDensity_comp_equiv
    rawSplit rawSplit_measurePreserving (f ∘ rawSplit.symm)
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply] at h
  have hm : Measurable (fun q : Hidden × Base => (q.2, hiddenLabel B a q.1)) :=
    measurable_snd.prodMk ((hiddenLabel_measurable B a).comp measurable_fst)
  calc
    _ = ((volume.withDensity f).map rawSplit).map
        (fun q : Hidden × Base => (q.2, hiddenLabel B a q.1)) := by
      rw [Measure.map_map hm rawSplit.measurable]
      congr 1
      funext x
      exact rawObserve_eq_split B a x
    _ = _ := by
      rw [h]
      exact Submission.Lib.K4MarginalAveraging.map_counted_withDensity volume volume
        (fun w z => f (rawSplit.symm (w, z))) (hf.comp rawSplit.symm.measurable) _ ((hiddenLabel_measurable B a).comp measurable_fst)

lemma pureMarginal_mass (B a : ℝ) {f : Raw → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, pureMarginal B a f z ∂reference) = ∫⁻ x, f x := by
  have h := congrArg (fun μ : Measure Observation => μ univ) (map_rawObserve_withDensity B a hf)
  simpa only [Measure.map_apply (rawObserve_measurable B a) MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h.symm

lemma pureMarginal_add (B a : ℝ) {f g : Raw → ℝ≥0∞} (hf : Measurable f) (z : Observation) :
    pureMarginal B a (fun x => f x + g x) z = pureMarginal B a f z + pureMarginal B a g z := by
  classical
  unfold pureMarginal Submission.Lib.K4MarginalAveraging.countedMarginal
  rw [← lintegral_add_left]
  · apply lintegral_congr
    intro w
    split_ifs <;> simp
  · exact ((hf.comp rawSplit.symm.measurable).comp (measurable_id.prodMk measurable_const)).indicator
      (measurableSet_eq_fun (hiddenLabel_measurable B a) measurable_const)

lemma pureMarginal_mono (B a : ℝ) {f g : Raw → ℝ≥0∞} (hfg : ∀ x, f x ≤ g x) (z : Observation) :
    pureMarginal B a f z ≤ pureMarginal B a g z := by
  classical
  apply lintegral_mono
  intro w
  dsimp only
  split_ifs
  · exact hfg _
  · exact le_rfl

/-- Passing to the pure observation loses no factor for the number of hidden bins. -/
lemma pureMarginal_ediff_le (B a : ℝ) {f g : Raw → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ z, ediff (pureMarginal B a f z) (pureMarginal B a g z) ∂reference) ≤
      ∫⁻ x, ediff (f x) (g x) := by
  have hfg : Measurable (fun x => f x - g x) := by fun_prop
  have hgf : Measurable (fun x => g x - f x) := by fun_prop
  refine (lintegral_mono fun z => ?_).trans_eq
    (pureMarginal_mass B a (measurable_ediff hf hg))
  have h1 : pureMarginal B a f z - pureMarginal B a g z ≤
      pureMarginal B a (fun x => f x - g x) z := by
    rw [tsub_le_iff_left, ← pureMarginal_add B a hg]
    exact pureMarginal_mono B a (fun _ => le_add_tsub) z
  have h2 : pureMarginal B a g z - pureMarginal B a f z ≤
      pureMarginal B a (fun x => g x - f x) z := by
    rw [tsub_le_iff_left, ← pureMarginal_add B a hf]
    exact pureMarginal_mono B a (fun _ => le_add_tsub) z
  exact (add_le_add h1 h2).trans_eq (pureMarginal_add B a hfg z).symm

end Submission.Obl.k4_horizon_light_cell_mass
