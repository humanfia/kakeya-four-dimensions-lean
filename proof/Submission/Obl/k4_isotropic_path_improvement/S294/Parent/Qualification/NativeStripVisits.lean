-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.NativeStripVisits, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/NativeStripVisits.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/NativeStripVisits.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/NativeStripVisits.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.RoundedCurveCover
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalNormalStrips
import Submission.Obl.k4_scalar_heavy_intercept_selection.AssignedCells


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set

noncomputable section

def originalPhysicalCoordinates (signal : Polynomial ℝ) (a v : Fin 3 → ℝ) (t : ℝ) :
    Fin 4 → ℝ := Fin.snoc (fun j => a j + v j * t) (signal.eval t)

theorem originalPhysicalCoordinates_time (signal : Polynomial ℝ) (a v : Fin 3 → ℝ)
    (ha : a 0 = 0) (hv : v 0 = 1) (t : ℝ) :
    originalPhysicalCoordinates signal a v t 0 = t := by
  change a 0 + v 0 * t = t
  simp [ha, hv]

/-- Actual cube/normal-strip pairs visited by ONE original trajectory.
Coarse cubes and normal strips are both assigned from its fine physical
states. The full curve cover and the within-cube strip count are imported;
their hypotheses are filled from the actual active occurrences. -/
theorem original_normal_strip_pairs_count
    (S : Finset ((Fin 4 → ℤ) × ℤ)) (signal : Polynomial ℝ)
    (hsignal : signal.natDegree ≤ 2) (a v : Fin 3 → ℝ)
    (ha0 : a 0 = 0) (hv0 : v 0 = 1)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (field : ℝ → Fin 3 → ℝ)
    (time : ((Fin 4 → ℤ) × ℤ) → ℝ) (L ρ b B E η K p : ℝ)
    (hL : 0 ≤ L) (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hη : 0 ≤ η) (hK : 0 ≤ K) (hp : 0 < p)
    (D : ℕ) (hD : 1 ≤ D) (hscale : L ≤ (D : ℝ) * ρ)
    (hLip : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ j,
      |originalPhysicalCoordinates signal a v t j -
        originalPhysicalCoordinates signal a v s j| ≤ L * |t - s|)
    (hrow_bound : ∀ C j, |row C j| ≤ B) (hvel : ∀ j, |v j| ≤ K)
    (hunit : ∀ z ∈ S, time z ∈ Icc (0 : ℝ) 1)
    (hcoarse : ∀ z ∈ S,
      roundedPhysicalCode b ρ (originalPhysicalCoordinates signal a v (time z)) = z.1)
    (hgraph : ∀ z ∈ S,
      |signal.derivative.eval (time z) - ∑ j, field (time z) j * v j| ≤ E)
    (hrow : ∀ z ∈ S, ∀ j, |field (time z) j - row z.1 j| ≤ η)
    (hstrip : ∀ z ∈ S,
      ⌊originalNormalStateCenter signal a v (row z.1) b (time z) / p⌋ = z.2) :
    (S.card : ℝ) ≤ ((D : ℝ) + 1) * 7 ^ 4 * 7 ^ 4 *
      (2 * (2 * ((1 + 3 * B) * b) + (E + 3 * η * K) * (2 * ρ)) / p + 4) := by
  classical
  obtain ⟨Q, hQ, hcover⟩ := exists_rounded_curve_cover
    (originalPhysicalCoordinates signal a v) hL hb hρ hbρ D hD hscale hLip
  let strips : (Fin 4 → ℤ) → Finset ℤ := fun C =>
    (S.filter fun z => z.1 = C).image Prod.snd
  let J : ℝ := 2 * (2 * ((1 + 3 * B) * b) + (E + 3 * η * K) * (2 * ρ)) / p + 4
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hstrips (C : Fin 4 → ℤ) (i : ℤ) : i ∈ strips C ↔ (C,i) ∈ S := by
    constructor
    · intro hi
      obtain ⟨z, hz, hzi⟩ := Finset.mem_image.mp hi
      obtain ⟨hzS, hzC⟩ := Finset.mem_filter.mp hz
      have heq : z = (C,i) := Prod.ext hzC hzi
      exact heq ▸ hzS
    · intro hi
      exact Finset.mem_image.mpr ⟨(C,i), Finset.mem_filter.mpr ⟨hi, rfl⟩, rfl⟩
  have hcount (C : Fin 4 → ℤ) : ((strips C).card : ℝ) ≤ J := by
    apply original_normal_strip_visit_count (strips C) signal hsignal a v (row C)
      (fun i => field (time (C,i))) (fun i => time (C,i))
      (ρ * (C 0 : ℝ)) (2 * ρ) b B E η K p (by positivity) hb hB hE hη hK hp
      (hrow_bound C) hvel
    · intro i hi
      have hiS := (hstrips C i).mp hi
      have hcode := congrFun (hcoarse (C,i) hiS) 0
      change (⌊b * (⌊originalPhysicalCoordinates signal a v (time (C,i)) 0 / b⌋ : ℝ) / ρ⌋ : ℤ)
        = C 0 at hcode
      rw [originalPhysicalCoordinates_time signal a v ha0 hv0] at hcode
      have htime := Submission.Obl.k4_scalar_heavy_intercept_selection.assigned_time_slab
        (h := 1) (b := b) (ξ := ρ) (t₀ := 0) (by norm_num) hb hρ (C 0)
        (by simpa only [sub_zero, div_one] using hcode)
      constructor <;> nlinarith [htime.1, htime.2]
    · intro i hi
      exact hgraph (C,i) ((hstrips C i).mp hi)
    · intro i hi
      exact hrow (C,i) ((hstrips C i).mp hi)
    · intro i hi
      exact hstrip (C,i) ((hstrips C i).mp hi)
  have hsub : S ⊆ Q.biUnion (fun C => (strips C).image (Prod.mk C)) := by
    intro z hz
    have hC : z.1 ∈ Q := by simpa only [hcoarse z hz] using hcover (time z) (hunit z hz)
    apply Finset.mem_biUnion.mpr
    refine ⟨z.1, hC, Finset.mem_image.mpr ⟨z.2, ?_, Prod.eta z⟩⟩
    exact (hstrips z.1 z.2).mpr (by simpa only [Prod.eta] using hz)
  calc
    (S.card : ℝ) ≤ ((Q.biUnion fun C => (strips C).image (Prod.mk C)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ C ∈ Q, (((strips C).image (Prod.mk C)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ C ∈ Q, ((strips C).card : ℝ) :=
      Finset.sum_le_sum fun _ _ => Nat.cast_le.mpr Finset.card_image_le
    _ ≤ ∑ _C ∈ Q, J := Finset.sum_le_sum fun C _ => hcount C
    _ = (Q.card : ℝ) * J := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hQ hJ

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
