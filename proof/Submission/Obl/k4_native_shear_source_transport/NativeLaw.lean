-- Copied from LOT tree oai_074_kakeya_four_dimensions, obligation o075 (k4_joint_homogenization),
-- branch x0254, file Submission/Obl/k4_joint_homogenization/NativeLaw.lean (session x0254's own proofs), renamed into this namespace.
import Submission.Obl.k4_native_shear_source_transport.Interface
import Submission.Obl.k4_native_shear_source_transport.Shear
import Submission.Obl.k4_native_shear_source_transport.PushDensity

/-!
# The native joint-observation law

For a prior `ν = ∑ₐ cₐ · (index iₐ) ⊗ vol|Aₐ` and any measurable selection `E'`, the
selected trajectory/time law pushed to the joint observation is the labeled pushforward of
an explicit density on the sheared coordinates `ℝ⁷`. Consequently it has a density with
respect to `volume ⊗ count ⊗ count` (`nativeDensityStatement`).
-/

namespace Submission.Obl.k4_native_shear_source_transport

open MeasureTheory Set
open scoped ENNReal

/-- The joint observation in sheared coordinates `z = (t, y₁, y₂, w, s₁, s₂, s₃)`. -/
noncomputable def shObs (a b : ℝ) (z : Fin 7 → ℝ) : ObsSpace :=
  ((WithLp.toLp 2 ![z 0, z 1, z 2], ⌊z 3 / a⌋), fun j => ⌊(WithLp.toLp 2 ![z 4, z 5]) j / b⌋)

theorem obsMap_eq_shObs (a b : ℝ) (i : ℕ) (x : Fin 6 → ℝ) (t : ℝ) :
    obsMap a b ((i, x), t) = shObs a b (shearEquiv (x, t)) := by
  rw [shearEquiv_apply]
  rfl

/-- Hidden label of a fiber point `w = (w(t), s₁, s₂, s₃)`. -/
noncomputable def hidLabel (a : ℝ) (w : Fin 4 → ℝ) : ℤ := ⌊w 0 / a⌋

/-- Velocity label of a fiber point. -/
noncomputable def velLabel (b : ℝ) (w : Fin 4 → ℝ) : Fin 2 → ℤ :=
  fun j => ⌊(WithLp.toLp 2 ![w 1, w 2]) j / b⌋

theorem measurable_hidLabel (a : ℝ) : Measurable (hidLabel a) := by
  unfold hidLabel; fun_prop

theorem measurable_velLabel (b : ℝ) : Measurable (velLabel b) := by
  unfold velLabel; fun_prop

theorem shObs_eq_labels (a b : ℝ) (z : Fin 7 → ℝ) :
    shObs a b z = (fun q : EuclideanSpace ℝ (Fin 3) × (Fin 4 → ℝ) =>
      ((q.1, hidLabel a q.2), velLabel b q.2)) (baseFiberEquiv z) := by
  rw [baseFiberEquiv_apply]
  rfl

theorem measurable_shObs (a b : ℝ) : Measurable (shObs a b) := by
  have h : shObs a b = (fun q : EuclideanSpace ℝ (Fin 3) × (Fin 4 → ℝ) =>
      ((q.1, hidLabel a q.2), velLabel b q.2)) ∘ baseFiberEquiv := by
    funext z; exact shObs_eq_labels a b z
  rw [h]
  exact ((measurable_fst.prodMk ((measurable_hidLabel a).comp measurable_snd)).prodMk
    ((measurable_velLabel b).comp measurable_snd)).comp baseFiberEquiv.measurable

theorem measurable_obsMap (a b : ℝ) : Measurable (obsMap a b) := by
  unfold obsMap
  fun_prop

/-- **Labeled pushforward in sheared coordinates.** -/
theorem map_shObs_withDensity (a b : ℝ) {φ : (Fin 7 → ℝ) → ℝ≥0∞} (hφ : Measurable φ) :
    Measure.map (shObs a b) ((volume : Measure (Fin 7 → ℝ)).withDensity φ) =
      refMeasure.withDensity
        (labelDensity volume (hidLabel a) (velLabel b) (φ ∘ baseFiberEquiv.symm)) := by
  have h1 := map_withDensity_comp_equiv baseFiberEquiv.symm
    (measurePreserving_baseFiberEquiv.symm baseFiberEquiv) φ
  rw [← h1, Measure.map_map (measurable_shObs a b) baseFiberEquiv.symm.measurable]
  have h2 : shObs a b ∘ baseFiberEquiv.symm =
      fun q : EuclideanSpace ℝ (Fin 3) × (Fin 4 → ℝ) =>
        ((q.1, hidLabel a q.2), velLabel b q.2) := by
    funext q
    simp only [Function.comp_apply, shObs_eq_labels, MeasurableEquiv.apply_symm_apply]
  rw [h2]
  exact map_labels_withDensity volume volume (measurable_hidLabel a) (measurable_velLabel b)
    (hφ.comp baseFiberEquiv.symm.measurable)

/-- The sheared selection of one prior piece `(index i) ⊗ vol|A`. -/
def shearedPiece (A : Set (Fin 6 → ℝ)) (i : ℕ) (E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) :
    Set (Fin 7 → ℝ) :=
  shearEquiv.symm ⁻¹' {p | p.1 ∈ A ∧ ((i, p.1), p.2) ∈ E'}

theorem measurableSet_shearedPiece {A : Set (Fin 6 → ℝ)} (hA : MeasurableSet A) (i : ℕ)
    {E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hE' : MeasurableSet E') :
    MeasurableSet (shearedPiece A i E') := by
  apply shearEquiv.symm.measurable
  exact (measurable_fst hA).inter
    (((measurable_const.prodMk measurable_fst).prodMk measurable_snd) hE')

/-- One prior piece, pushed by any map factoring through the shear. -/
theorem map_piece_of_factor {Y : Type*} [MeasurableSpace Y]
    (F : (ℕ × (Fin 6 → ℝ)) × ℝ → Y) (Φ : (Fin 7 → ℝ) → Y) (hF : Measurable F)
    (hΦ : Measurable Φ) (i : ℕ) (hFΦ : ∀ x t, F ((i, x), t) = Φ (shearEquiv (x, t)))
    {A : Set (Fin 6 → ℝ)} (hA : MeasurableSet A)
    {E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hE' : MeasurableSet E') :
    Measure.map F
        (((Measure.map (fun x => (i, x)) (volume.restrict A)).prod volume).restrict E') =
      Measure.map Φ
        ((volume : Measure (Fin 7 → ℝ)).withDensity ((shearedPiece A i E').indicator 1)) := by
  have he : Measurable (fun x : Fin 6 → ℝ => (i, x)) := measurable_const.prodMk measurable_id
  have hP : Measurable (Prod.map (fun x : Fin 6 → ℝ => (i, x)) (id : ℝ → ℝ)) :=
    he.prodMap measurable_id
  rw [withDensity_indicator_one (measurableSet_shearedPiece hA i hE')]
  rw [show (volume : Measure ℝ) = Measure.map id volume from Measure.map_id.symm,
    Measure.map_prod_map _ _ he measurable_id,
    Measure.restrict_map hP hE', Measure.map_map hF hP]
  have hpr : (volume.restrict A).prod (volume : Measure ℝ) =
      ((volume : Measure (Fin 6 → ℝ)).prod (volume : Measure ℝ)).restrict (A ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hpr, Measure.restrict_restrict (hP hE')]
  have hcomp : F ∘ Prod.map (fun x : Fin 6 → ℝ => (i, x)) (id : ℝ → ℝ) = Φ ∘ shearEquiv := by
    funext p
    exact hFΦ p.1 p.2
  rw [hcomp, ← Measure.map_map hΦ shearEquiv.measurable]
  congr 1
  have hPset : (Prod.map (fun x : Fin 6 → ℝ => (i, x)) (id : ℝ → ℝ) ⁻¹' E' ∩ A ×ˢ univ) =
      shearEquiv ⁻¹' (shearedPiece A i E') := by
    ext p
    simp only [shearedPiece, mem_preimage, MeasurableEquiv.symm_apply_apply, mem_inter_iff,
      mem_prod, mem_univ, and_true, Set.mem_ofPred_eq, Prod.map, id]
    tauto
  rw [hPset, ← MeasurableEquiv.restrict_map, measurePreserving_shearEquiv.map_eq]

/-- One prior piece. -/
theorem map_obs_piece (a b : ℝ) {A : Set (Fin 6 → ℝ)} (hA : MeasurableSet A) (i : ℕ)
    {E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hE' : MeasurableSet E') :
    Measure.map (obsMap a b)
        (((Measure.map (fun x => (i, x)) (volume.restrict A)).prod volume).restrict E') =
      Measure.map (shObs a b)
        ((volume : Measure (Fin 7 → ℝ)).withDensity ((shearedPiece A i E').indicator 1)) :=
  map_piece_of_factor (obsMap a b) (shObs a b) (measurable_obsMap a b) (measurable_shObs a b) i
    (obsMap_eq_shObs a b i) hA hE'

/-- The native density in sheared coordinates. -/
noncomputable def nativeDensity {m : ℕ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) :
    (Fin 7 → ℝ) → ℝ≥0∞ :=
  ∑' j, (ENNReal.ofReal (c j)) • (shearedPiece (A j) (i j) E').indicator 1

theorem measurable_nativeDensity {m : ℕ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    {A : Fin m → Set (Fin 6 → ℝ)} (hA : ∀ j, MeasurableSet (A j))
    {E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hE' : MeasurableSet E') :
    Measurable (nativeDensity c i A E') := by
  unfold nativeDensity
  apply Measurable.tsum'
  intro j
  exact (measurable_one.indicator (measurableSet_shearedPiece (hA j) (i j) hE')).const_smul _

/-- **The native law**, pushed by any map factoring through the shear. -/
theorem map_native_of_factor {Y : Type*} [MeasurableSpace Y]
    (F : (ℕ × (Fin 6 → ℝ)) × ℝ → Y) (Φ : (Fin 7 → ℝ) → Y) (hF : Measurable F)
    (hΦ : Measurable Φ) (hFΦ : ∀ i x t, F ((i, x), t) = Φ (shearEquiv (x, t)))
    {ν : Measure (ℕ × (Fin 6 → ℝ))} {m : ℕ} (c : Fin m → ℝ)
    (i : Fin m → ℕ) {A : Fin m → Set (Fin 6 → ℝ)} (hA : ∀ j, MeasurableSet (A j))
    (hν : ν = ∑ j, (ENNReal.ofReal (c j)) •
      Measure.map (fun x => (i j, x)) (volume.restrict (A j)))
    {E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hE' : MeasurableSet E') :
    Measure.map F ((ν.prod volume).restrict E') =
      Measure.map Φ ((volume : Measure (Fin 7 → ℝ)).withDensity
        (nativeDensity c i A E')) := by
  have hpieces : ∀ j, Measurable ((ENNReal.ofReal (c j)) •
      (shearedPiece (A j) (i j) E').indicator (1 : (Fin 7 → ℝ) → ℝ≥0∞)) := fun j =>
    (measurable_one.indicator (measurableSet_shearedPiece (hA j) (i j) hE')).const_smul _
  rw [nativeDensity, withDensity_tsum hpieces, hν, ← Measure.sum_fintype,
    Measure.prod_sum_left, Measure.restrict_sum _ hE',
    Measure.map_sum hF.aemeasurable, Measure.map_sum hΦ.aemeasurable]
  congr 1
  funext j
  rw [Measure.prod_smul_left, Measure.restrict_smul, Measure.map_smul _ hF.aemeasurable,
    withDensity_smul _ (measurable_one.indicator (measurableSet_shearedPiece (hA j) (i j) hE')),
    Measure.map_smul _ hΦ.aemeasurable,
    map_piece_of_factor F Φ hF hΦ (i j) (hFΦ (i j)) (hA j) hE']

/-- **The native law.** -/
theorem map_obs_native (a b : ℝ) {ν : Measure (ℕ × (Fin 6 → ℝ))} {m : ℕ} (c : Fin m → ℝ)
    (i : Fin m → ℕ) {A : Fin m → Set (Fin 6 → ℝ)} (hA : ∀ j, MeasurableSet (A j))
    (hν : ν = ∑ j, (ENNReal.ofReal (c j)) •
      Measure.map (fun x => (i j, x)) (volume.restrict (A j)))
    {E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hE' : MeasurableSet E') :
    Measure.map (obsMap a b) ((ν.prod volume).restrict E') =
      Measure.map (shObs a b) ((volume : Measure (Fin 7 → ℝ)).withDensity
        (nativeDensity c i A E')) :=
  map_native_of_factor (obsMap a b) (shObs a b) (measurable_obsMap a b) (measurable_shObs a b)
    (obsMap_eq_shObs a b) c i hA hν hE'

/-- Sets in the frozen Boolean polynomial format are measurable. -/
theorem measurableSet_of_boolPolyFormat {n m : ℕ} {A : Set (Fin n → ℝ)}
    (p : Fin m → MvPolynomial (Fin n) ℝ) (b : (Fin m → Bool) → Bool)
    (h : ∀ x, x ∈ A ↔ b (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) = true) :
    MeasurableSet A := by
  have hA : A = (fun x => fun i => decide (0 ≤ MvPolynomial.eval x (p i))) ⁻¹'
      {v | b v = true} := by
    ext x; exact h x
  rw [hA]
  have hmeas : Measurable (fun x : Fin n → ℝ => fun i => decide (0 ≤ MvPolynomial.eval x (p i))) := by
    apply Measurable.of_eval
    intro i
    apply measurable_to_countable'
    intro v
    have hc : Measurable fun x : Fin n → ℝ => MvPolynomial.eval x (p i) :=
      (MvPolynomial.continuous_eval (p i)).measurable
    cases v
    · have : (fun x : Fin n → ℝ => decide (0 ≤ MvPolynomial.eval x (p i))) ⁻¹' {false} =
          {x | 0 ≤ MvPolynomial.eval x (p i)}ᶜ := by
        ext x; simp
      rw [this]
      exact (measurableSet_le measurable_const hc).compl
    · have : (fun x : Fin n → ℝ => decide (0 ≤ MvPolynomial.eval x (p i))) ⁻¹' {true} =
          {x | 0 ≤ MvPolynomial.eval x (p i)} := by
        ext x; simp
      rw [this]
      exact measurableSet_le measurable_const hc
  exact hmeas (Set.toFinite _).measurableSet

/-- **Native densities exist** for every measurable selection. -/
theorem nativeDensityStatement : NativeDensityStatement := by
  intro N M D K ν E hfmt E' hE' a b _ _
  obtain ⟨-, ⟨m, -, c, i, A, hA, hν⟩, -⟩ := hfmt
  have hAm : ∀ j, MeasurableSet (A j) := by
    intro j
    obtain ⟨-, -, -, ⟨m₀, -, p₀, -, b₀, hb₀⟩, -⟩ := hA j
    exact measurableSet_of_boolPolyFormat p₀ b₀ hb₀
  refine ⟨_, measurable_labelDensity volume (measurable_hidLabel a) (measurable_velLabel b)
    ((measurable_nativeDensity c i hAm hE').comp baseFiberEquiv.symm.measurable), ?_⟩
  rw [map_obs_native a b c i hAm hν hE',
    map_shObs_withDensity a b (measurable_nativeDensity c i hAm hE')]

end Submission.Obl.k4_native_shear_source_transport
