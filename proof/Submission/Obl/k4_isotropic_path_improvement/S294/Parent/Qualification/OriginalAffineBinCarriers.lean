-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalAffineBinCarriers, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalAffineBinCarriers.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalAffineBinCarriers.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalAffineBinCarriers.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.AffinePhysicalSupport


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts

noncomputable section

/-- Construct the actual finite affine-bin carrier and its ORIGINAL
palette-weighted area budget. The number of velocity bins never enters. -/
theorem original_affine_bin_carrier {Λ : Type*}
    (S : Set Λ) (c : Λ → Fin 7 → ℝ) (p K : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hK : 0 ≤ K) (hcoeff : ∀ l∈S, ∀ i, |c l i| ≤ K)
    (π : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure π] :
    ∃ A2 : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)),
      (∀ l∈S, (ybin p (c l),vbin p (c l))∈A2) ∧
      (∑ q∈A2, π {q.2}*ENNReal.ofReal (p^2)) ≤ ENNReal.ofReal ((4*K+2)^2) := by
  classical
  let y0 := fun l : Λ => (![c l 3,c l 5] : Fin 2 → ℝ)
  let vel := fun l : Λ => (![c l 4,c l 6] : Fin 2 → ℝ)
  have hdiamY (i : Fin 2) (l : Λ) (hl : l∈S) (l' : Λ) (hl' : l'∈S) :
      |y0 l i-y0 l' i| ≤ 2*K := by
    fin_cases i
    · change |c l 3-c l' 3| ≤ 2*K
      exact (abs_sub _ _).trans (by linarith [hcoeff l hl 3,hcoeff l' hl' 3])
    · change |c l 5-c l' 5| ≤ 2*K
      exact (abs_sub _ _).trans (by linarith [hcoeff l hl 5,hcoeff l' hl' 5])
  have hdiamV (i : Fin 2) (l : Λ) (hl : l∈S) (l' : Λ) (hl' : l'∈S) :
      |vel l i-vel l' i| ≤ 2*K := by
    fin_cases i
    · change |c l 4-c l' 4| ≤ 2*K
      exact (abs_sub _ _).trans (by linarith [hcoeff l hl 4,hcoeff l' hl' 4])
    · change |c l 6-c l' 6| ≤ 2*K
      exact (abs_sub _ _).trans (by linarith [hcoeff l hl 6,hcoeff l' hl' 6])
  have hY := records_finite_card S y0 (fun _ => p) (fun _ => 2*K)
    (fun _ => hp) (fun _ => by positivity) hdiamY
  have hV := records_finite_card S vel (fun _ => p) (fun _ => 2*K)
    (fun _ => hp) (fun _ => by positivity) hdiamV
  let Y := hY.1.toFinset
  let V := hV.1.toFinset
  have hYweight : (Y.card : ℝ)*p^2 ≤ (4*K+2)^2 := by
    have hcard : (Y.card : ℝ) ≤ (4*K/p+2)^2 := by
      have hh := hY.2
      rw [Set.ncard_eq_toFinset_card _ hY.1] at hh
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,show 2*(2*K)=4*K by ring] using hh
    calc
      (Y.card : ℝ)*p^2 ≤ (4*K/p+2)^2*p^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg p)
      _ = (4*K+2*p)^2 := by field_simp
      _ ≤ (4*K+2)^2 := by gcongr; linarith
  have hYenn : (Y.card : ENNReal)*ENNReal.ofReal (p^2) ≤ ENNReal.ofReal ((4*K+2)^2) := by
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg Y.card)]
    exact ENNReal.ofReal_le_ofReal hYweight
  have hπ : ∑ j∈V, π {j} ≤ 1 := by
    rw [sum_measure_singleton]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ : π univ=1)
  refine ⟨Y.product V,?_,?_⟩
  · intro l hl
    have hy : ybin p (c l)=record y0 (fun _ => p) l := by
      funext i
      fin_cases i <;> simp [ybin,record,y0,zy]
    have hv : vbin p (c l)=record vel (fun _ => p) l := by
      funext i
      fin_cases i <;> rfl
    exact Finset.mem_product.mpr ⟨hY.1.mem_toFinset.mpr ⟨l,hl,hy.symm⟩,
      hV.1.mem_toFinset.mpr ⟨l,hl,hv.symm⟩⟩
  · calc
      (∑ q∈Y.product V, π {q.2}*ENNReal.ofReal (p^2)) =
          (Y.card : ENNReal)*((∑ j∈V, π {j})*ENNReal.ofReal (p^2)) := by
        calc
          _ = ∑ _y∈Y, ∑ j∈V, π {j}*ENNReal.ofReal (p^2) :=
            Finset.sum_product Y V (fun q => π {q.2}*ENNReal.ofReal (p^2))
          _ = _ := by simp only [←Finset.sum_mul,Finset.sum_const,nsmul_eq_mul,mul_assoc]
      _ ≤ (Y.card : ENNReal)*(1*ENNReal.ofReal (p^2)) :=
        mul_le_mul' le_rfl (mul_le_mul' hπ le_rfl)
      _ ≤ _ := by simpa only [one_mul] using hYenn

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
