/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/PreparedParentSupport.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedParentGeometry
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Two stable native-signal groups on a full original prepared parent. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

theorem parentNativeLaw_meshCap (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s)
    (i : Fin (a.n k s)) {delta : ℝ}
    (hcap : ∀ q : Fin 3 → ℤ,
      a.mu k {z | baseMesh delta (basePoint (a.b k z.1) z.2) = q} ≤
        ENNReal.ofReal ((4 * p.K k + 2) * p.K k * delta ^ 3)) :
    RootMeshCap (a.parentNativeLaw k s i)
      ((4 * p.K k + 2) * p.K k / (a.mu k (a.parentSet k s i)).toReal) delta := by
  have : IsFiniteMeasure (a.mu k) := a.incidence_finite p hcommon k
  apply conditionalNativeLaw_mesh_cap _ (a.measurableSet_parentSet p hatlas i) _
    (a.measurable_nativePoint k (hcommon k).1)
    (a.original_parent_mass_pos p hp hatlas i).ne' (measure_ne_top _ _)
  intro q
  have hsub : {z | baseMesh delta (rootBaseCoordinates (a.nativePoint k z)) = q ∧
      z ∈ a.parentSet k s i} ⊆
      {z | baseMesh delta (basePoint (a.b k z.1) z.2) = q} := by
    intro z hz
    simpa only [nativePoint_base, mem_setOf_eq] using hz.1
  exact (measure_mono hsub).trans (hcap q)

theorem parentNativeLaw_filling (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) {R : ℝ} {k : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s)) :
    27 * ((4 * p.K k + 2) * p.K k / (a.mu k (a.parentSet k s i)).toReal) *
      |(a.parentSupportZoom p k s i).baseMatrix.det|⁻¹ ≤
        parentFilling (p.K k) (width p k s) := by
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have ha : 0 < width p k s := Real.rpow_pos_of_pos hN _
  have ha1 : width p k s ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.1 k]) (by linarith)
  have hq : 0 < a.q k s := by unfold q; positivity
  have hg : 0 < narrow p k s := Real.rpow_pos_of_pos hN _
  rw [a.parentSupportZoom_jacobian p hp]
  exact (parent_filling_bound hK ha hq hg
    (a.original_parent_mass_toReal_lower p hp hcommon hatlas i)).trans
      (parent_filling_le hK ha ha1 hp.2.2.2.2.1.le)

/-- The full parent produces exactly two measurable incidence groups. The
discard is measured in its original law, and the signal remains the native P. -/
theorem finite_mesh_prepared_parent_support (A : ℕ) :
    ∃ J C : ℕ, 1 ≤ C ∧ ∀ (p : Parameters), p.Valid →
      ∀ a : PreparedModel α, a.Common p → ∀ (R : ℝ) (k : ℕ) (s : ℝ), 0 ≤ s →
        a.AtlasAt p R k s → ∀ i : Fin (a.n k s),
        ∀ delta sigma : ℝ, 0 < delta → 0 < sigma →
          sigma ≤ (parentFilling (p.K k) (width p k s) ^ J)⁻¹ →
          (∀ e, (∑ j, |(a.parentSupportZoom p k s i).baseMatrix e j| * delta) ≤ sigma) →
          (∀ q : Fin 3 → ℤ,
            a.mu k {z | baseMesh delta (basePoint (a.b k z.1) z.2) = q} ≤
              ENNReal.ofReal ((4 * p.K k + 2) * p.K k * delta ^ 3)) →
          ∃ E : Fin 2 → Set (α × ℝ),
            (∀ e, MeasurableSet (E e)) ∧
            (∀ e, E e ⊆ a.parentSet k s i) ∧
            (∀ e e', e ≠ e' → Disjoint (E e) (E e')) ∧
            a.mu k (a.parentSet k s i \ ⋃ e, E e) ≤
              a.mu k (a.parentSet k s i) *
                ENNReal.ofReal ((parentFilling (p.K k) (width p k s) ^ A)⁻¹) ∧
            ∀ e z, z ∈ E e → ∀ w, w ∈ E e →
              |eval (a.x k z.1 z.2) (a.P k) - eval (a.x k w.1 w.2) (a.P k)| ≤
                2 * (2 * p.K k) ^ 14 * width p k s +
                  parentFilling (p.K k) (width p k s) ^ C *
                    ‖nativeBase ((a.parentSupportZoom p k s i).nativePoint (a.nativePoint k z)) -
                      nativeBase ((a.parentSupportZoom p k s i).nativePoint (a.nativePoint k w))‖ := by
  classical
  obtain ⟨J, C, hC, hpart⟩ := finite_mesh_parent_signal_partition A
  refine ⟨J, C, hC, ?_⟩
  intro p hp a hcommon R k s hs hatlas i delta sigma hd hσ hσJ hresolve hcap
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have ha : 0 < width p k s := Real.rpow_pos_of_pos hN _
  have ha1 : width p k s ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.1 k]) (by linarith)
  have : IsFiniteMeasure (a.mu k) := a.incidence_finite p hcommon k
  let H := parentFilling (p.K k) (width p k s)
  let C₀ := (4 * p.K k + 2) * p.K k / (a.mu k (a.parentSet k s i)).toReal
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hFdeg : (a.F k s i).totalDegree ≤ 2 := (hatlas.2.2.2.2.1 i).2.2.2.2.1
  have hPdeg : (a.P k).totalDegree ≤ 2 := (hcommon k).2.2.2.2.2.2.2.1
  obtain ⟨F, hFm, hFd, hFloss, hFosc⟩ := hpart (2 * p.K k) H (width p k s)
    delta sigma C₀ (by linarith) (native_power_le_parentFilling hK ha ha1)
    ha ha1 hd hσ hσJ hC₀ (a.parentSupportZoom p k s i)
    (a.parentSupportZoom_ok p hp k s i) (a.parentSupportZoom_hidden p k s i)
    hresolve (a.parentNativeLaw_filling p hp hcommon hs hatlas i)
    (a.F k s i) (a.P k) hFdeg hPdeg (a.parentNativeLaw k s i)
    (a.parentNativeLaw_probability p hp hcommon hatlas i)
    (a.parentNativeLaw_small p hp hcommon hatlas i)
    (a.parentNativeLaw_meshCap p hp hcommon hatlas i hcap)
    (a.parentNativeLaw_good p hp hcommon hatlas i)
  let E : Fin 2 → Set (α × ℝ) := fun e => a.parentSet k s i ∩ a.nativePoint k ⁻¹' F e
  refine ⟨E, ?_, fun _ => inter_subset_left, ?_, ?_, ?_⟩
  · intro e
    exact (a.measurableSet_parentSet p hatlas i).inter
      ((hFm e).preimage (a.measurable_nativePoint k (hcommon k).1))
  · intro e e' he
    exact ((hFd e e' he).preimage (a.nativePoint k)).mono inter_subset_right inter_subset_right
  · have hsub : a.parentSet k s i \ ⋃ e, E e ⊆
        a.parentSet k s i \ ⋃ e, a.nativePoint k ⁻¹' F e := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      intro hw
      obtain ⟨e, he⟩ := mem_iUnion.mp hw
      exact hz.2 (mem_iUnion.mpr ⟨e, hz.1, he⟩)
    exact (measure_mono hsub).trans (conditionalNativeLaw_restore_loss _
      (a.measurableSet_parentSet p hatlas i) (a.original_parent_mass_pos p hp hatlas i).ne'
      (measure_ne_top _ _) _ (a.measurable_nativePoint k (hcommon k).1) F hFm hFloss)
  · intro e z hz w hw
    simpa only [nativePoint_value] using hFosc e (a.nativePoint k z) hz.2
      (a.nativePoint k w) hw.2

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
