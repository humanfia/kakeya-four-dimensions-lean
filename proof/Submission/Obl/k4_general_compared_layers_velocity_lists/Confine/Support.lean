-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Confine.Support; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- The proof of `prepared_parent_support_fixed` below is adapted from this LOT tree,
   accepted obligation o253 (`k4_general_parent_projected_layers`), file
   `Submission/Obl/k4_general_parent_projected_layers/Support/PreparedParentSupport.lean`,
   theorem `finite_mesh_prepared_parent_support` (itself adapted from o222, session x0774,
   commit 1823dd94). It is restated here with the two exponents of the accepted native-signal
   partition fixed once and for all, independently of the trajectory type. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Confine.Bridge
import Submission.Obl.k4_general_compared_layers_velocity_lists.Lists.Interface
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedParentSupport
import Submission.Obl.k4_general_parent_projected_layers.Support.SupportMeshResolution
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedZoomGap
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedBaseCaps

/-!
# Two native-signal groups on one true block of a general parent

The accepted two-group support of a full prepared parent (o253), with its mesh and
Lipschitz exponents fixed universally, transported to `Parent`, and with the zoomed base
distance bounded by the original base distance.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

/-- The mesh exponent of the accepted native-signal partition at loss exponent one. -/
def supportJ : ℕ := (finite_mesh_parent_signal_partition 1).choose

/-- The Lipschitz exponent of the accepted native-signal partition at loss exponent one. -/
def supportC : ℕ := (finite_mesh_parent_signal_partition 1).choose_spec.choose

theorem one_le_supportC : 1 ≤ supportC :=
  (finite_mesh_parent_signal_partition 1).choose_spec.choose_spec.1

/-- `finite_mesh_prepared_parent_support` of accepted o253 at loss exponent one, with the
exponents `supportJ` and `supportC` (which do not depend on the trajectory type). -/
theorem prepared_parent_support_fixed {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    {R : ℝ} {k : ℕ} {s : ℝ} (hs : 0 ≤ s) (hatlas : a.AtlasAt p R k s) (i : Fin (a.n k s))
    {delta sigma : ℝ} (hd : 0 < delta) (hσ : 0 < sigma)
    (hσJ : sigma ≤ (parentFilling (p.K k) (PreparedModel.width p k s) ^ supportJ)⁻¹)
    (hresolve : ∀ e, (∑ j, |(a.parentSupportZoom p k s i).baseMatrix e j| * delta) ≤ sigma)
    (hcap : ∀ q : Fin 3 → ℤ,
      a.mu k {z | baseMesh delta (basePoint (a.b k z.1) z.2) = q} ≤
        ENNReal.ofReal ((4 * p.K k + 2) * p.K k * delta ^ 3)) :
    ∃ E : Fin 2 → Set (α × ℝ),
      (∀ e, MeasurableSet (E e)) ∧
      (∀ e, E e ⊆ a.parentSet k s i) ∧
      a.mu k (a.parentSet k s i \ ⋃ e, E e) ≤
        a.mu k (a.parentSet k s i) *
          ENNReal.ofReal ((parentFilling (p.K k) (PreparedModel.width p k s))⁻¹) ∧
      ∀ e z, z ∈ E e → ∀ w, w ∈ E e →
        |eval (a.x k z.1 z.2) (a.P k) - eval (a.x k w.1 w.2) (a.P k)| ≤
          2 * (2 * p.K k) ^ 14 * PreparedModel.width p k s +
            parentFilling (p.K k) (PreparedModel.width p k s) ^ supportC *
              ‖nativeBase ((a.parentSupportZoom p k s i).nativePoint (a.nativePoint k z)) -
                nativeBase ((a.parentSupportZoom p k s i).nativePoint (a.nativePoint k w))‖ := by
  classical
  have hpart := (finite_mesh_parent_signal_partition 1).choose_spec.choose_spec.2
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have ha : 0 < PreparedModel.width p k s := Real.rpow_pos_of_pos hN _
  have ha1 : PreparedModel.width p k s ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.1 k]) (by linarith)
  have : IsFiniteMeasure (a.mu k) := a.incidence_finite p hcommon k
  let H := parentFilling (p.K k) (PreparedModel.width p k s)
  let C₀ := (4 * p.K k + 2) * p.K k / (a.mu k (a.parentSet k s i)).toReal
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hFdeg : (a.F k s i).totalDegree ≤ 2 := (hatlas.2.2.2.2.1 i).2.2.2.2.1
  have hPdeg : (a.P k).totalDegree ≤ 2 := (hcommon k).2.2.2.2.2.2.2.1
  obtain ⟨F, hFm, _hFd, hFloss, hFosc⟩ := hpart (2 * p.K k) H (PreparedModel.width p k s)
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
  refine ⟨E, ?_, fun _ => inter_subset_left, ?_, ?_⟩
  · intro e
    exact (a.measurableSet_parentSet p hatlas i).inter
      ((hFm e).preimage (a.measurable_nativePoint k (hcommon k).1))
  · have hsub : a.parentSet k s i \ ⋃ e, E e ⊆
        a.parentSet k s i \ ⋃ e, a.nativePoint k ⁻¹' F e := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      intro hw
      obtain ⟨e, he⟩ := mem_iUnion.mp hw
      exact hz.2 (mem_iUnion.mpr ⟨e, hz.1, he⟩)
    have hloss := (measure_mono hsub).trans (conditionalNativeLaw_restore_loss _
      (a.measurableSet_parentSet p hatlas i) (a.original_parent_mass_pos p hp hatlas i).ne'
      (measure_ne_top _ _) _ (a.measurable_nativePoint k (hcommon k).1) F hFm hFloss)
    simpa only [pow_one] using hloss
  · intro e z hz w hw
    have hzw := hFosc e (a.nativePoint k z) hz.2 (a.nativePoint k w) hw.2
    simp only [PreparedModel.nativePoint_value] at hzw
    exact hzw

namespace Parent

variable {α : Type} [MeasurableSpace α]

theorem toModel_parentSupportZoom (p : Parent α) (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) :
    p.toModel.parentSupportZoom p.toParams k s i =
      supportZoom (p.K k) ((2 : ℝ) ^ p.T k s)⁻¹ (p.N k ^ (-p.ℓ * s)) (p.toModel.blockMid k s i)
        (p.c k s i 0 + p.toModel.blockMid k s i * p.c k s i 1) (p.c k s i) := by
  unfold PreparedModel.parentSupportZoom
  rw [toModel_q]
  rfl

/-- **Two native-signal groups on one true block of a general parent.** On a true block
at depth `s`, a physical base mesh `delta` resolving the block's normalized packet and
admissible for the pure base caps gives two measurable groups covering the block up to a
`parentFilling⁻¹` proportion of its incidence mass, on each of which the native signal is
controlled by the original base distance. -/
theorem Valid.parent_groups {p : Parent α} (h : p.Valid) {R : ℝ} {k : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (hat : p.AtDepth k s R) (i : Fin (p.n k s)) {delta : ℝ} (hd : 0 < delta)
    (hres : delta / (((2 : ℝ) ^ p.T k s)⁻¹ * p.N k ^ (-p.ℓ * s)) ≤
      (parentFilling (p.K k) (p.N k ^ (-s)) ^ supportJ)⁻¹)
    (hcap : ∀ q : Fin 3 → ℤ,
      p.μ k {z | baseMesh delta (basePoint (p.b k z.1) z.2) = q} ≤
        ENNReal.ofReal ((4 * p.K k + 2) * p.K k * delta ^ 3)) :
    ∃ E : Fin 2 → Set (α × ℝ),
      (∀ e, MeasurableSet (E e)) ∧
      (∀ e, E e ⊆ p.B k s i ×ˢ block (p.T k s) (p.j k s i)) ∧
      p.μ k ((p.B k s i ×ˢ block (p.T k s) (p.j k s i)) \ ⋃ e, E e) ≤
        p.μ k (p.B k s i ×ˢ block (p.T k s) (p.j k s i)) *
          ENNReal.ofReal ((parentFilling (p.K k) (p.N k ^ (-s)))⁻¹) ∧
      ∀ e z, z ∈ E e → ∀ w, w ∈ E e → ∀ D : ℝ, 0 ≤ D →
        (∀ c : Fin 3, |p.base k z.1 z.2 c - p.base k w.1 w.2 c| ≤ D) →
        |p.signal k z.1 z.2 - p.signal k w.1 w.2| ≤
          2 * (2 * p.K k) ^ 14 * p.N k ^ (-s) +
            parentFilling (p.K k) (p.N k ^ (-s)) ^ supportC *
              (12 * p.K k ^ 2 * D / (((2 : ℝ) ^ p.T k s)⁻¹ * p.N k ^ (-p.ℓ * s))) := by
  have hp := h.toParams_valid
  have hcommon := h.toModel_common
  have hatlas := hat.toAtlasAt
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hq : 0 < ((2 : ℝ) ^ p.T k s)⁻¹ := by positivity
  have hg : 0 < p.N k ^ (-p.ℓ * s) := Real.rpow_pos_of_pos hN _
  have hg1 : p.N k ^ (-p.ℓ * s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [h.scale k])
      (by nlinarith [h.transverse_pos])
  have hc : ∀ e, |p.c k s i e| ≤ p.K k := (hat.2.2.2.2.1 i).2.2.2.1
  set sigma := delta / (((2 : ℝ) ^ p.T k s)⁻¹ * p.N k ^ (-p.ℓ * s)) with hsigma
  have hσ : 0 < sigma := by positivity
  have hresolve : ∀ e, (∑ j, |(p.toModel.parentSupportZoom p.toParams k s i).baseMatrix e j| *
      delta) ≤ sigma := by
    intro e
    have h1 := supportZoom_mesh_resolution (K := p.K k) (q := ((2 : ℝ) ^ p.T k s)⁻¹)
      (g := p.N k ^ (-p.ℓ * s)) hK hq hg hg1 hd.le
      (p.toModel.blockMid k s i) (p.c k s i 0 + p.toModel.blockMid k s i * p.c k s i 1)
      (p.c k s i) (hc 3) (hc 4) e
    rw [toModel_parentSupportZoom]
    exact h1
  obtain ⟨E, hEm, hEsub, hEloss, hEosc⟩ :=
    prepared_parent_support_fixed p.toParams hp p.toModel hcommon hs hatlas i hd hσ hres
      hresolve hcap
  refine ⟨E, hEm, hEsub, hEloss, ?_⟩
  intro e z hz w hw D hD hbase
  have hosc := hEosc e z hz w hw
  have hgap : ‖nativeBase ((p.toModel.parentSupportZoom p.toParams k s i).nativePoint
        (p.toModel.nativePoint k z)) -
      nativeBase ((p.toModel.parentSupportZoom p.toParams k s i).nativePoint
        (p.toModel.nativePoint k w))‖ ≤
      12 * p.K k ^ 2 * D / (((2 : ℝ) ^ p.T k s)⁻¹ * p.N k ^ (-p.ℓ * s)) := by
    have h0 : |p.toModel.nativePoint k z 0 - p.toModel.nativePoint k w 0| ≤ 2 * (D / 2) := by
      have := hbase 0
      have he : 2 * (D / 2) = D := by ring
      rw [he]
      exact this
    have h1 : |p.toModel.nativePoint k z 1 - p.toModel.nativePoint k w 1| ≤
        4 * 0 + 2 * p.K k * (D / 2) := by
      have := hbase 1
      have he : 4 * 0 + 2 * p.K k * (D / 2) = p.K k * D := by ring
      rw [he]
      exact this.trans (le_mul_of_one_le_left hD hK)
    have h2 : |p.toModel.nativePoint k z 2 - p.toModel.nativePoint k w 2| ≤
        2 * p.N k ^ (-p.ℓ * s) * (D / 2) + 2 * p.K k * (D / 2) := by
      have := hbase 2
      have he : 2 * p.N k ^ (-p.ℓ * s) * (D / 2) + 2 * p.K k * (D / 2) =
          p.N k ^ (-p.ℓ * s) * D + p.K k * D := by ring
      rw [he]
      have hgD : 0 ≤ p.N k ^ (-p.ℓ * s) * D := mul_nonneg hg.le hD
      exact this.trans (by nlinarith)
    have hz := supportZoom_base_gap (K := p.K k) (q := ((2 : ℝ) ^ p.T k s)⁻¹)
      (g := p.N k ^ (-p.ℓ * s)) (sigma := D / 2) (chi := 0)
      (tmid := p.toModel.blockMid k s i)
      (z₀ := p.c k s i 0 + p.toModel.blockMid k s i * p.c k s i 1)
      (p.c k s i) hK hq hg hg1 (by linarith) le_rfl (hc 3) (hc 4)
      (p.toModel.nativePoint k z) (p.toModel.nativePoint k w) h0 h1 h2
    have he : 24 * p.K k ^ 2 * (D / 2 + 0) / (((2 : ℝ) ^ p.T k s)⁻¹ * p.N k ^ (-p.ℓ * s)) =
        12 * p.K k ^ 2 * D / (((2 : ℝ) ^ p.T k s)⁻¹ * p.N k ^ (-p.ℓ * s)) := by ring
    rw [← he, toModel_parentSupportZoom]
    exact hz
  have hpf : 0 ≤ parentFilling (p.K k) (p.N k ^ (-s)) ^ supportC := by
    unfold parentFilling
    have : 0 < p.N k ^ (-s) := Real.rpow_pos_of_pos hN _
    positivity
  calc |p.signal k z.1 z.2 - p.signal k w.1 w.2| ≤ _ := hosc
    _ ≤ _ := by
      change 2 * (2 * p.K k) ^ 14 * p.N k ^ (-s) +
          parentFilling (p.K k) (p.N k ^ (-s)) ^ supportC * _ ≤ _
      gcongr

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
