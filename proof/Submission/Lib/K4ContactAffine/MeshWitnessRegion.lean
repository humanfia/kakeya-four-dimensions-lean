/- Adapted from: here:o223
   (x0927; countable-cell threshold extends x0775). -/
import Submission.Lib.K4ContactAffine.CountableCells
import Submission.Lib.K4AffineMeshCaps.Saturation

/-!+# A witnessed region directly from the original mesh ceilings

We saturate the actual source image by complete mesh cells and apply the
countable threshold argument. There is no finite code enumeration and no
measurability assumption on the source image or on its fibers.
-/

namespace Submission.Lib.K4ContactAffine

open Set MeasureTheory
open Submission.Lib.K4AffineMeshCaps

/-- Mesh saturation and original joint velocity-bin ceilings give an actual
base region with three separated good witnesses within one mesh step in
every coordinate. -/
theorem mesh_witness_region {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 3 → ℝ) (v : Ω → ℝ)
    (S : Set (Fin 3 → ℝ)) (G : Set Ω)
    {m β V δ η : ℝ} (hm : 0 < m) (hβ : 0 < β) (hV : 0 < V)
    (hδ : 0 < δ) (hη : 0 < η) (pmax : ENNReal)
    (hmass : ENNReal.ofReal m ≤ μ univ)
    (hS : ∀ᵐ p ∂μ, point p ∈ S) (hG : ∀ᵐ p ∂μ, p ∈ G)
    (hvol : volume (meshSaturation δ S) ≤ ENNReal.ofReal V)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh δ (point p) = q} ≤ ENNReal.ofReal (β * δ ^ 3))
    (hbin : ∀ (q : Fin 3 → ℤ) (a : ℤ),
      μ {p | baseMesh δ (point p) = q ∧ ⌊v p / η⌋ = a} ≤
        ENNReal.ofReal (β * δ ^ 3) * pmax)
    (hsmall : 6 * ENNReal.ofReal β * pmax < ENNReal.ofReal (m / (2 * V))) :
    ∃ E : Set (Fin 3 → ℝ), MeasurableSet E ∧ E ⊆ meshSaturation δ S ∧
      ENNReal.ofReal (m / (2 * β)) ≤ volume E ∧
      ∀ x ∈ E, ∃ p₀ p₁ p₂ : Ω,
        (point p₀ ∈ S ∧ p₀ ∈ G) ∧ (point p₁ ∈ S ∧ p₁ ∈ G) ∧
        (point p₂ ∈ S ∧ p₂ ∈ G) ∧
        (∀ e, |point p₀ e - x e| ≤ δ) ∧
        (∀ e, |point p₁ e - x e| ≤ δ) ∧
        (∀ e, |point p₂ e - x e| ≤ δ) ∧
        η < |v p₀ - v p₁| ∧ η < |v p₀ - v p₂| ∧ η < |v p₁ - v p₂| := by
  classical
  let events : (Fin 3 → ℤ) → Set Ω := fun q =>
    {p | point p ∈ S ∧ baseMesh δ (point p) = q}
  let cells := selectedMeshCell δ S
  have hcellsvol : ∑' q, volume (cells q) ≤ ENNReal.ofReal V := by
    rw [← measure_iUnion (selectedMeshCell_pairwiseDisjoint δ S)
      (measurableSet_selectedMeshCell δ S)]
    exact hvol
  have hcover : ∀ᵐ p ∂μ, ∃ q, p ∈ events q := by
    filter_upwards [hS] with p hp
    exact ⟨baseMesh δ (point p), hp, rfl⟩
  have hcellcap : ∀ q, μ (events q) ≤ ENNReal.ofReal β * volume (cells q) := by
    intro q
    by_cases hq : ∃ z ∈ S, baseMesh δ z = q
    · rw [show cells q = meshBox δ q from ite_eq_left hq, volume_meshBox hδ,
        ← ENNReal.ofReal_mul hβ.le]
      exact (measure_mono (fun p hp => hp.2)).trans (hcap q)
    · have he : events q = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        exact hq ⟨point p, hp.1, hp.2⟩
      rw [he, measure_empty]
      exact bot_le
  have hcellbin : ∀ q a, μ {p | p ∈ events q ∧ ⌊v p / η⌋ = a} ≤
      ENNReal.ofReal β * volume (cells q) * pmax := by
    intro q a
    by_cases hq : ∃ z ∈ S, baseMesh δ z = q
    · rw [show cells q = meshBox δ q from ite_eq_left hq, volume_meshBox hδ,
        ← ENNReal.ofReal_mul hβ.le]
      exact (measure_mono (show {p | p ∈ events q ∧ ⌊v p / η⌋ = a} ⊆
        {p | baseMesh δ (point p) = q ∧ ⌊v p / η⌋ = a} from
          fun p hp => ⟨hp.1.2, hp.2⟩)).trans (hbin q a)
    · have he : {p | p ∈ events q ∧ ⌊v p / η⌋ = a} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        exact hq ⟨point p, hp.1.1, hp.1.2⟩
      rw [he, measure_empty]
      exact bot_le
  obtain ⟨E, hE, hES, hEV, hwit⟩ := occupied_region_of_countable_caps
    μ volume events cells (selectedMeshCell_pairwiseDisjoint δ S)
      (measurableSet_selectedMeshCell δ S) hm hβ hV hη hcellsvol hmass
        hcover hcellcap v pmax hcellbin hsmall G hG
  refine ⟨E, hE, hES, hEV, ?_⟩
  intro x hx
  obtain ⟨q, hxq, p₀, p₁, p₂, hp₀, hp₁, hp₂, h₀₁, h₀₂, h₁₂⟩ := hwit x hx
  have hxcell : x ∈ meshBox δ q := selectedMeshCell_subset δ S q hxq
  refine ⟨p₀, p₁, p₂, ⟨hp₀.1.1, hp₀.2⟩, ⟨hp₁.1.1, hp₁.2⟩,
    ⟨hp₂.1.1, hp₂.2⟩, ?_, ?_, ?_, h₀₁, h₀₂, h₁₂⟩
  · exact fun e => meshBox_coordinate_distance hδ hp₀.1.2 hxcell e
  · exact fun e => meshBox_coordinate_distance hδ hp₁.1.2 hxcell e
  · exact fun e => meshBox_coordinate_distance hδ hp₂.1.2 hxcell e

/-- If the source points are separated from the cube's boundary, the entire
occupied mesh saturation lies in the cube. -/
theorem meshSaturation_subset_cube_of_margin {S : Set (Fin 3 → ℝ)} {δ h : ℝ}
    (hδ : 0 < δ) (hδh : δ ≤ h)
    (hS : ∀ x ∈ S, ∀ e, h ≤ x e ∧ x e ≤ 1 - h) :
    meshSaturation δ S ⊆ Icc (0 : Fin 3 → ℝ) 1 := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := meshSaturation_close hδ S hx
  constructor
  · intro e
    change (0 : ℝ) ≤ x e
    have hd := (abs_le.mp (hxy e)).1
    linarith [(hS y hy e).1]
  · intro e
    change x e ≤ (1 : ℝ)
    have hd := (abs_le.mp (hxy e)).2
    linarith [(hS y hy e).2]

/-- The cube form of the witness construction has no boundary deletion. Its
time margin can be supplied by extending quadratic fits to a triple block. -/
theorem cube_mesh_witness_region {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 3 → ℝ) (v : Ω → ℝ)
    (S : Set (Fin 3 → ℝ)) (G : Set Ω)
    {m β δ η h : ℝ} (hm : 0 < m) (hβ : 0 < β)
    (hδ : 0 < δ) (hη : 0 < η) (hδh : δ ≤ h) (pmax : ENNReal)
    (hmass : ENNReal.ofReal m ≤ μ univ)
    (hS : ∀ᵐ p ∂μ, point p ∈ S) (hG : ∀ᵐ p ∂μ, p ∈ G)
    (hmargin : ∀ x ∈ S, ∀ e, h ≤ x e ∧ x e ≤ 1 - h)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh δ (point p) = q} ≤ ENNReal.ofReal (β * δ ^ 3))
    (hbin : ∀ (q : Fin 3 → ℤ) (a : ℤ),
      μ {p | baseMesh δ (point p) = q ∧ ⌊v p / η⌋ = a} ≤
        ENNReal.ofReal (β * δ ^ 3) * pmax)
    (hsmall : 6 * ENNReal.ofReal β * pmax < ENNReal.ofReal (m / 2)) :
    ∃ E : Set (Fin 3 → ℝ), MeasurableSet E ∧ E ⊆ Icc (0 : Fin 3 → ℝ) 1 ∧
      ENNReal.ofReal (m / (2 * β)) ≤ volume E ∧
      ∀ x ∈ E, ∃ p₀ p₁ p₂ : Ω,
        (point p₀ ∈ S ∧ p₀ ∈ G) ∧ (point p₁ ∈ S ∧ p₁ ∈ G) ∧
        (point p₂ ∈ S ∧ p₂ ∈ G) ∧
        (∀ e, |point p₀ e - x e| ≤ δ) ∧
        (∀ e, |point p₁ e - x e| ≤ δ) ∧
        (∀ e, |point p₂ e - x e| ≤ δ) ∧
        η < |v p₀ - v p₁| ∧ η < |v p₀ - v p₂| ∧ η < |v p₁ - v p₂| := by
  have hsat : meshSaturation δ S ⊆ Icc (0 : Fin 3 → ℝ) 1 :=
    meshSaturation_subset_cube_of_margin hδ hδh hmargin
  have hvol : volume (meshSaturation δ S) ≤ ENNReal.ofReal (1 : ℝ) := by
    simpa [Real.volume_Icc_pi] using (measure_mono hsat :
      volume (meshSaturation δ S) ≤ volume (Icc (0 : Fin 3 → ℝ) 1))
  obtain ⟨E, hE, hES, hEV, hwit⟩ := mesh_witness_region μ point v S G hm hβ
    zero_lt_one hδ hη pmax hmass hS hG hvol hcap hbin (by simpa using hsmall)
  exact ⟨E, hE, hES.trans hsat, hEV, hwit⟩

end Submission.Lib.K4ContactAffine
