-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.AffinePhysicalSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/AffinePhysicalSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/AffinePhysicalSupport.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/AffinePhysicalSupport.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterFloors2
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomBlockVisits
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set
open Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts

noncomputable section

def originalBaseCoordinates {Λ : Type*} (c : Λ → Fin 7 → ℝ) (z : Λ × ℝ) : Fin 3 → ℝ :=
  ![z.2,zy (c z.1) z.2 0,zy (c z.1) z.2 1]

def originalBaseCode {Λ : Type*} (c : Λ → Fin 7 → ℝ) (p : ℝ) (z : Λ × ℝ) : Fin 3 → ℤ :=
  fun j => ⌊originalBaseCoordinates c z j/p⌋

/-- An entire original affine-bin family visits only O(K^3/p) actual
base cells. The list is constructed from the family, keeping arbitrary
original line tags and ordinary time. -/
theorem original_affine_base_cell_list {Λ : Type*}
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ) (p K : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hK : 0 ≤ K) (β J : Fin 2 → ℤ)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (hV : ∀ z∈E, ∀ i, |zv (c z.1) i| ≤ K)
    (hy : ∀ z∈E, ybin p (c z.1)=β) (hv : ∀ z∈E, vbin p (c z.1)=J) :
    ∃ F : Finset (Fin 3 → ℤ), (F.card : ℝ) ≤ 4*(4*K+6)^3/p ∧
      ∀ z∈E, originalBaseCode c p z∈F := by
  classical
  have hTimes := records_finite_card E (fun z : Λ × ℝ => fun _ : Fin 1 => z.2)
    (fun _ => p) (fun _ => 1) (fun _ => hp) (by intro i; norm_num)
    (by intro i z hz z' hz'; exact abs_le.mpr ⟨by linarith [(ht z hz).1,(ht z' hz').2],
      by linarith [(ht z hz).2,(ht z' hz').1]⟩)
  let times := hTimes.1.toFinset
  have hTimeCard : (times.card : ℝ) ≤ 4/p := by
    have hh := hTimes.2
    rw [Set.ncard_eq_toFinset_card _ hTimes.1] at hh
    have h4 : 2/p+2 ≤ 4/p := by
      apply (le_div_iff₀ hp).mpr
      field_simp
      nlinarith
    have h2 : (times.card : ℝ) ≤ 2/p+2 := by
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,pow_one,mul_one] using hh
    exact h2.trans h4
  let Ej := fun j : Fin 1 → ℤ => {z∈E | ⌊z.2/p⌋=j 0}
  have hFib (j : Fin 1 → ℤ) :
      (originalBaseCode c p '' Ej j).Finite ∧
        ((originalBaseCode c p '' Ej j).ncard : ℝ) ≤ (4*K+6)^3 := by
    have hd (i : Fin 3) (z : Λ × ℝ) (hz : z∈Ej j)
        (z' : Λ × ℝ) (hz' : z'∈Ej j) :
        |originalBaseCoordinates c z i-originalBaseCoordinates c z' i| ≤ (2+2*K)*p := by
      have htz := bin_mem_Icc hp hz.2
      have htz' := bin_mem_Icc hp hz'.2
      have hs0 : 0 ≤ p*(j 0 : ℝ) := by
        have h0 : (0 : ℤ) ≤ j 0 := hz.2 ▸ Int.floor_nonneg.mpr (div_nonneg (ht z hz.1).1 hp.le)
        exact mul_nonneg hp.le (by exact_mod_cast h0)
      have hs1 : p*(j 0 : ℝ) ≤ 1 := htz.1.trans (ht z hz.1).2
      have hpos (k : Fin 2) := zy_mem_window_box hp (hV z hz.1) β J (hy z hz.1) (hv z hz.1)
        hs0 hs1 htz k
      have hpos' (k : Fin 2) := zy_mem_window_box hp (hV z' hz'.1) β J (hy z' hz'.1) (hv z' hz'.1)
        hs0 hs1 htz' k
      fin_cases i
      · change |z.2-z'.2| ≤ _
        rw [abs_le]
        constructor <;> nlinarith [htz.1,htz.2,htz'.1,htz'.2]
      · change |zy (c z.1) z.2 0-zy (c z'.1) z'.2 0| ≤ _
        rw [abs_le]
        constructor <;> linarith [(hpos 0).1,(hpos 0).2,(hpos' 0).1,(hpos' 0).2]
      · change |zy (c z.1) z.2 1-zy (c z'.1) z'.2 1| ≤ _
        rw [abs_le]
        constructor <;> linarith [(hpos 1).1,(hpos 1).2,(hpos' 1).1,(hpos' 1).2]
    have hh := records_finite_card_of_relative_diameter (Ej j) (originalBaseCoordinates c)
      (fun _ => p) (2+2*K) (fun _ => hp) (by linarith) hd
    exact ⟨hh.1,hh.2.trans_eq (by norm_num; ring)⟩
  let F := times.biUnion fun j => (hFib j).1.toFinset
  refine ⟨F,?_,?_⟩
  · calc
      (F.card : ℝ) ≤ ∑ j∈times, (((hFib j).1.toFinset).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j∈times, (4*K+6)^3 := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [Set.ncard_eq_toFinset_card _ (hFib j).1] using (hFib j).2
      _ = (times.card : ℝ)*(4*K+6)^3 := by simp
      _ ≤ (4/p)*(4*K+6)^3 := mul_le_mul_of_nonneg_right hTimeCard (by positivity)
      _ = _ := by ring
  · intro z hz
    let j : Fin 1 → ℤ := fun _ => ⌊z.2/p⌋
    have hj : j∈times := hTimes.1.mem_toFinset.mpr ⟨z,hz,rfl⟩
    exact Finset.mem_biUnion.mpr ⟨j,hj,(hFib j).1.mem_toFinset.mpr ⟨z,⟨hz,rfl⟩,rfl⟩⟩

/-- The actual scalar bins over one original physical base cell. -/
def originalScalarFiber {Λ : Type*} (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ)
    (p : ℝ) (q : Fin 3 → ℤ) : Set ℤ :=
  {j | ∃ z∈E, originalBaseCode c p z=q ∧ ⌊zx (c z.1) z.2/p⌋=j}

/-- Produce the ENTIRE original `(time,X)` support table in every
position/velocity affine bin. The inputs are the original vertical
physical-cell count and the actual native coefficient bound; no scalar
support table or scalar counting certificate is assumed. -/
theorem original_affine_scalar_support_tables {Λ : Type*}
    (E : Set (Λ × ℝ)) (c : Λ → Fin 7 → ℝ) (p K H d : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (hcoeff : ∀ z∈E, ∀ i, |c z.1 i| ≤ K)
    (hvertical : ∀ q, ((originalScalarFiber E c p q).ncard : ℝ) ≤ H*p^(-d)) :
    ∃ F : (Fin 2 → ℤ) → (Fin 2 → ℤ) → Finset (ℤ × ℤ),
      (∀ β J, ((F β J).card : ℝ) ≤ (4*(4*K+6)^3*H)*p^(-1-d)) ∧
      ∀ z∈E, (⌊z.2/p⌋,⌊zx (c z.1) z.2/p⌋)∈F (ybin p (c z.1)) (vbin p (c z.1)) := by
  classical
  have hScalar := records_finite_card E (fun z : Λ × ℝ => fun _ : Fin 1 => zx (c z.1) z.2)
    (fun _ => p) (fun _ => 6*K) (fun _ => hp) (fun _ => by positivity)
    (by
      intro i z hz z' hz'
      have h0 := abs_zx_le (hcoeff z hz) (ht z hz)
      have h1 := abs_zx_le (hcoeff z' hz') (ht z' hz')
      exact (abs_sub _ _).trans (by linarith))
  let scalarBins := hScalar.1.toFinset.image (fun q => q 0)
  have hScalarKnown (z : Λ × ℝ) (hz : z∈E) : ⌊zx (c z.1) z.2/p⌋∈scalarBins :=
    Finset.mem_image.mpr ⟨_,hScalar.1.mem_toFinset.mpr ⟨z,hz,rfl⟩,rfl⟩
  let fiber := fun q : Fin 3 → ℤ => scalarBins.filter (fun j => j∈originalScalarFiber E c p q)
  have hFiberSet (q) : (↑(fiber q) : Set ℤ)=originalScalarFiber E c p q := by
    ext j
    simp only [fiber,Finset.mem_coe,Finset.mem_filter]
    constructor
    · exact fun hh => hh.2
    · intro hh
      obtain ⟨z,hz,hq,hj⟩ := hh
      exact ⟨hj ▸ hScalarKnown z hz,⟨z,hz,hq,hj⟩⟩
  have hFiberCard (q) : ((fiber q).card : ℝ) ≤ H*p^(-d) := by
    have hh := hvertical q
    rw [←hFiberSet q,Set.ncard_coe_finset] at hh
    exact hh
  let Ew := fun β J : Fin 2 → ℤ => {z∈E | ybin p (c z.1)=β ∧ vbin p (c z.1)=J}
  have hBase (β J : Fin 2 → ℤ) := original_affine_base_cell_list (Ew β J) c p K hp hp1 hK β J
    (fun z hz => ht z hz.1)
    (by
      intro z hz i
      fin_cases i
      · change |c z.1 4| ≤ K
        exact hcoeff z hz.1 4
      · change |c z.1 6| ≤ K
        exact hcoeff z hz.1 6)
    (fun z hz => hz.2.1) (fun z hz => hz.2.2)
  choose baseCells hBaseCard hBaseKnown using hBase
  let F := fun β J => (baseCells β J).biUnion fun q => (fiber q).image (fun a => (q 0,a))
  refine ⟨F,?_,?_⟩
  · intro β J
    calc
      ((F β J).card : ℝ) ≤ ∑ q∈baseCells β J, (((fiber q).image (fun a => (q 0,a))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q∈baseCells β J, ((fiber q).card : ℝ) :=
        Finset.sum_le_sum fun q _ => Nat.cast_le.mpr Finset.card_image_le
      _ ≤ ∑ _q∈baseCells β J, H*p^(-d) := Finset.sum_le_sum fun q _ => hFiberCard q
      _ = ((baseCells β J).card : ℝ)*(H*p^(-d)) := by simp
      _ ≤ (4*(4*K+6)^3/p)*(H*p^(-d)) :=
        mul_le_mul_of_nonneg_right (hBaseCard β J) (mul_nonneg hH (Real.rpow_nonneg hp.le _))
      _ = (4*(4*K+6)^3*H)*p^(-1-d) := by
        rw [show -1-d=(-1)+(-d) by ring,Real.rpow_add hp,Real.rpow_neg_one]
        ring
  · intro z hz
    have hbase := hBaseKnown (ybin p (c z.1)) (vbin p (c z.1)) z ⟨hz,rfl,rfl⟩
    have hfiber : ⌊zx (c z.1) z.2/p⌋∈fiber (originalBaseCode c p z) := by
      rw [←Finset.mem_coe,hFiberSet]
      exact ⟨z,hz,rfl,rfl⟩
    exact Finset.mem_biUnion.mpr ⟨_,hbase,Finset.mem_image.mpr ⟨_,hfiber,rfl⟩⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
