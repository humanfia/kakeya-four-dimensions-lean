/- Adapted from: here:o254 (session x0898).
Complete original-source-preserving finite-cell jitter.
Source credits retained below. -/
import Submission.Lib.K4MeshJitter.Coupling
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Floor

namespace Submission.Lib.K4MeshJitter

open MeasureTheory Set
open scoped ENNReal

noncomputable section

def meshCode2 (δ : ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℤ := fun i => ⌊z i / δ⌋

def meshCell2 (δ : ℝ) (q : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  Set.pi univ (fun i => Ico ((q i : ℝ) * δ) (((q i : ℝ) + 1) * δ))

theorem measurable_meshCode2 (δ : ℝ) : Measurable (meshCode2 δ) := by
  unfold meshCode2
  fun_prop

theorem measurableSet_meshCell2 (δ : ℝ) (q : Fin 2 → ℤ) :
    MeasurableSet (meshCell2 δ q) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ico)

theorem mem_meshCell2_iff {δ : ℝ} (hδ : 0 < δ) (q : Fin 2 → ℤ) (z : Fin 2 → ℝ) :
    z ∈ meshCell2 δ q ↔ meshCode2 δ z = q := by
  simp only [meshCell2, mem_pi, mem_univ, true_implies]
  constructor
  · intro h
    ext i
    exact Int.floor_eq_iff.mpr
      ⟨(le_div_iff₀ hδ).mpr (h i).1, (div_lt_iff₀ hδ).mpr (h i).2⟩
  · intro h i
    have hi := Int.floor_eq_iff.mp (congrFun h i)
    exact ⟨(le_div_iff₀ hδ).mp hi.1, (div_lt_iff₀ hδ).mp hi.2⟩

theorem meshCell2_disjoint {δ : ℝ} (hδ : 0 < δ) :
    Pairwise (fun q q' : Fin 2 → ℤ => Disjoint (meshCell2 δ q) (meshCell2 δ q')) := by
  intro q q' hne
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact hne (((mem_meshCell2_iff hδ q z).mp hz).symm.trans
    ((mem_meshCell2_iff hδ q' z).mp hz'))

theorem volume_meshCell2 {δ : ℝ} (hδ : 0 ≤ δ) (q : Fin 2 → ℤ) :
    volume (meshCell2 δ q) = ENNReal.ofReal (δ ^ 2) := by
  rw [meshCell2, Real.volume_pi_Ico]
  have hi (i : Fin 2) : ((q i : ℝ) + 1) * δ - (q i : ℝ) * δ = δ := by ring
  simp_rw [hi]
  simp only [Fin.prod_univ_two]
  rw [← ENNReal.ofReal_mul hδ]
  congr 1
  ring

theorem meshCode2_close {δ : ℝ} (hδ : 0 < δ) {z y : Fin 2 → ℝ}
    (hcode : meshCode2 δ z = meshCode2 δ y) : ∀ i, |z i - y i| ≤ δ := by
  have hz := (mem_meshCell2_iff hδ (meshCode2 δ y) z).mpr hcode
  have hy := (mem_meshCell2_iff hδ (meshCode2 δ y) y).mpr rfl
  intro i
  have hzi := hz i (mem_univ _)
  have hyi := hy i (mem_univ _)
  rw [abs_le]
  constructor <;> linarith [hzi.1, hzi.2, hyi.1, hyi.2]

/-- The source event is retained verbatim; only its observed base point is
redrawn uniformly inside the same original mesh cell. -/
def finiteMeshCoupling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 2 → ℝ) (δ : ℝ) (Q : Finset (Fin 2 → ℤ)) :
    Measure (Ω × (Fin 2 → ℝ)) :=
  cellCoupling
    (fun q : Q => μ.restrict {ω | meshCode2 δ (Z ω) = q.val})
    (fun q : Q => ProbabilityTheory.cond volume (meshCell2 δ q.val))

theorem finiteMeshCoupling_fst {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂μ, meshCode2 δ (Z ω) ∈ Q) :
    (finiteMeshCoupling μ Z δ Q).map Prod.fst = μ := by
  haveI (q : Q) : IsProbabilityMeasure (ProbabilityTheory.cond volume (meshCell2 δ q.val)) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by rw [volume_meshCell2 hδ.le]; positivity) (by rw [volume_meshCell2 hδ.le]; finiteness)
  rw [finiteMeshCoupling, cellCoupling_fst]
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion]
  · apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [hcover] with ω hω
    exact mem_iUnion.mpr ⟨⟨meshCode2 δ (Z ω), hω⟩, rfl⟩
  · intro q q' hne
    apply Set.disjoint_left.mpr
    intro ω hω hω'
    exact hne (Subtype.ext (hω.symm.trans hω'))
  · intro q
    exact measurableSet_eq_fun ((measurable_meshCode2 δ).comp hZ) measurable_const

theorem finiteMeshCoupling_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ)) :
    IsFiniteMeasure (finiteMeshCoupling μ Z δ Q) := by
  haveI (q : Q) : IsProbabilityMeasure (ProbabilityTheory.cond volume (meshCell2 δ q.val)) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by rw [volume_meshCell2 hδ.le]; positivity) (by rw [volume_meshCell2 hδ.le]; finiteness)
  exact cellCoupling_finite _ _

theorem finiteMeshCoupling_close {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ)) :
    ∀ᵐ z ∂finiteMeshCoupling μ Z δ Q, ∀ i, |(Z z.1) i - z.2 i| ≤ δ := by
  haveI (q : Q) : IsProbabilityMeasure (ProbabilityTheory.cond volume (meshCell2 δ q.val)) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by rw [volume_meshCell2 hδ.le]; positivity) (by rw [volume_meshCell2 hδ.le]; finiteness)
  have hs := cellCoupling_support
    (fun q : Q => μ.restrict {ω | meshCode2 δ (Z ω) = q.val})
    (fun q : Q => ProbabilityTheory.cond volume (meshCell2 δ q.val))
    (fun q : Q => {ω | meshCode2 δ (Z ω) = q.val})
    (fun q : Q => meshCell2 δ q.val)
    (fun q => ae_restrict_mem (measurableSet_eq_fun ((measurable_meshCode2 δ).comp hZ) measurable_const))
    (fun q => ProbabilityTheory.ae_cond_mem (measurableSet_meshCell2 δ q.val))
  filter_upwards [hs] with z hz
  obtain ⟨q, hq, hy⟩ := hz
  exact meshCode2_close hδ (hq.trans ((mem_meshCell2_iff hδ q.val z.2).mp hy).symm)

/-- Original cell ceilings become exact continuous base ceilings for every
original index event, without a factor for the number of mesh cells. -/
theorem finiteMeshCoupling_density {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ)
    {δ : ℝ} {A : ℝ≥0∞} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ))
    (E : Set Ω) (hE : MeasurableSet E)
    (hcap : ∀ q ∈ Q, μ {ω | meshCode2 δ (Z ω) = q ∧ ω ∈ E} ≤
      A * ENNReal.ofReal (δ ^ 2))
    (U : Set (Fin 2 → ℝ)) (hU : MeasurableSet U) :
    finiteMeshCoupling μ Z δ Q (E ×ˢ U) ≤ A * volume U := by
  haveI (q : Q) : IsProbabilityMeasure (ProbabilityTheory.cond volume (meshCell2 δ q.val)) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by rw [volume_meshCell2 hδ.le]; positivity) (by rw [volume_meshCell2 hδ.le]; finiteness)
  apply cellCoupling_density _ _ volume (fun q : Q => meshCell2 δ q.val)
    (fun q => measurableSet_meshCell2 δ q.val)
    (fun q q' hne => meshCell2_disjoint hδ (fun hh => hne (Subtype.ext hh)))
    (ENNReal.ofReal (δ ^ 2)) A (by positivity) (by finiteness) E
    (by
      intro q
      rw [Measure.restrict_apply hE]
      calc
        _ = μ {ω | meshCode2 δ (Z ω) = q.val ∧ ω ∈ E} := by
          congr 1
          ext ω
          exact and_comm
        _ ≤ _ := hcap q.val q.property)
    (by
      intro q W hW
      rw [ProbabilityTheory.cond_apply (measurableSet_meshCell2 δ q.val), volume_meshCell2 hδ.le,
        inter_comm]) U hU

/-- Every almost-everywhere property of the original source event survives
the coupling, including earlier assignments and stored polynomial choices. -/
theorem finiteMeshCoupling_ae_original {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂μ, meshCode2 δ (Z ω) ∈ Q)
    {P : Ω → Prop} (hP : ∀ᵐ ω ∂μ, P ω) :
    ∀ᵐ z ∂finiteMeshCoupling μ Z δ Q, P z.1 := by
  apply ae_of_ae_map measurable_fst.aemeasurable
  rw [finiteMeshCoupling_fst μ Z hZ hδ Q hcover]
  exact hP

/-- Resolved jitter preserves the near agreement used by matching. The
Lipschitz estimates may depend on the complete original source record. -/
theorem finiteMeshCoupling_agreement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ) (hZ : Measurable Z)
    {δ a e : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂μ, meshCode2 δ (Z ω) ∈ Q)
    (f g : Ω → (Fin 2 → ℝ) → ℝ)
    (hsource : ∀ᵐ ω ∂μ,
      |f ω (Z ω) - g ω (Z ω)| ≤ a ∧
      ∀ y, (∀ i, |(Z ω) i - y i| ≤ δ) →
        |f ω (Z ω) - f ω y| ≤ e ∧ |g ω (Z ω) - g ω y| ≤ e) :
    ∀ᵐ z ∂finiteMeshCoupling μ Z δ Q, |f z.1 z.2 - g z.1 z.2| ≤ a + 2 * e := by
  filter_upwards [finiteMeshCoupling_ae_original μ Z hZ hδ Q hcover hsource,
    finiteMeshCoupling_close μ Z hZ hδ Q] with z hz hclose
  obtain ⟨hf, hg⟩ := hz.2 z.2 hclose
  calc
    _ ≤ |f z.1 z.2 - f z.1 (Z z.1)| +
        |f z.1 (Z z.1) - g z.1 (Z z.1)| + |g z.1 (Z z.1) - g z.1 z.2| := by
      have h₁ := abs_sub_le (f z.1 z.2) (f z.1 (Z z.1)) (g z.1 z.2)
      have h₂ := abs_sub_le (f z.1 (Z z.1)) (g z.1 (Z z.1)) (g z.1 z.2)
      linarith
    _ ≤ e + a + e := by rw [abs_sub_comm (f z.1 z.2)]; exact add_le_add (add_le_add hf hz.1) hg
    _ = a + 2 * e := by ring

end
end Submission.Lib.K4MeshJitter
