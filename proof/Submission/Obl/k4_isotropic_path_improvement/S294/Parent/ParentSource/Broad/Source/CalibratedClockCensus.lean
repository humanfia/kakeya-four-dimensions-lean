-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CalibratedClockCensus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CalibratedClockCensus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CalibratedClockCensus.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockIsotropicCensus

/-!
# Preserve the exact height-scaling factor in the clock census

The coarsening proof adapts o265/x0943 e0bf23d4b, ClockIsotropicCensus.lean,
using accepted Census.rescale_census with its exact height factor.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Set
open Submission.Lib.K4ParentSignalPreparation.Census
noncomputable section

theorem clock_isotropic_support_height_calibrated {Ω : Type*}
    (E : Set Ω) (z : Ω → Fin 3 → ℝ) (X : Ω → ℝ)
    {ε θ K d : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K^(100:ℕ)*p ≤ θ*w → (occupied E z X p w).Finite ∧
        ((occupied E z X p w).ncard : ℝ) ≤ K/(p^3*w^d))
    (steps : ℕ) (hsteps : K^(100:ℕ) ≤ (2:ℝ)^steps)
    (hresolved : ε*(2:ℝ)^steps ≤ θ) :
    let mesh := ε*(2:ℝ)^steps
    ∃ S : Finset ((Fin 3 → ℤ) × ℤ),
      (S.card : ℝ)*mesh^((3:ℝ)+d) ≤ K*θ^d*((2:ℝ)^steps)^3 ∧
      ∀ x∈E, gridCode z (fun x => θ*X x) mesh mesh x∈S := by
  classical
  let mesh := ε*(2:ℝ)^steps
  have hmesh : 0 < mesh := by dsimp [mesh]; positivity
  have hKpow : K ≤ K^(100:ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (by norm_num : (1:ℕ) ≤ 100)
  have hKD : K ≤ (2:ℝ)^steps := hKpow.trans hsteps
  have hθD : θ ≤ (2:ℝ)^steps := hθK.trans hKD
  obtain ⟨hfinite,hcount⟩ := rescale_census E z X hε hθ hcensus
    (p:=ε) (w:=mesh) le_rfl hε1
    (by dsimp [mesh]; nlinarith) hresolved (by dsimp [mesh]; nlinarith)
  let F := hfinite.toFinset
  let S := F.image (coarsenProductBase steps)
  have hcard : (S.card : ℝ) ≤ (K*θ^d)/(ε^3*mesh^d) := by
    apply (show (S.card : ℝ) ≤ (F.card : ℝ) from by exact_mod_cast Finset.card_image_le).trans
    change (hfinite.toFinset.card : ℝ) ≤ _
    rw [←Set.ncard_eq_toFinset_card _ hfinite]
    exact hcount
  have hθd : 0 < θ^d := Real.rpow_pos_of_pos hθ d
  have hmeshD : 0 < mesh^d := Real.rpow_pos_of_pos hmesh d
  refine ⟨S,?_,?_⟩
  · calc
      _ = (S.card : ℝ)*mesh^3*mesh^d := by rw [Real.rpow_add hmesh]; norm_num; ring
      _ ≤ ((K*θ^d)/(ε^3*mesh^d))*mesh^3*mesh^d := by gcongr
      _ = K*θ^d*((2:ℝ)^steps)^3 := by
        have hs : mesh^3=ε^3*((2:ℝ)^steps)^3 := by dsimp [mesh]; ring
        rw [hs]
        field_simp
  · intro x hx
    have hh : gridCode z (fun x => θ*X x) ε mesh x∈F :=
      hfinite.mem_toFinset.mpr ⟨x,hx,rfl⟩
    rw [product_gridCode_dyadic_base]
    exact Finset.mem_image_of_mem _ hh

/-- A polynomial coarsening retains the full `theta^dimension` factor. -/
theorem clock_isotropic_support_height_calibrated_precision {Ω : Type*}
    (E : Set Ω) (z : Ω → Fin 3 → ℝ) (X : Ω → ℝ)
    {ε θ K d ζ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : 0 < θ)
    (hK : 1 ≤ K) (hθK : θ ≤ K)
    (hεζ : ε ≤ θ * ζ) (hmargin : 2 * K ^ (100 : ℕ) * ζ ≤ 1)
    (hcensus : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
      K ^ (100 : ℕ) * p ≤ θ * w → (occupied E z X p w).Finite ∧
        ((occupied E z X p w).ncard : ℝ) ≤ K / (p ^ 3 * w ^ d)) :
    ∃ (steps : ℕ) (S : Finset ((Fin 3 → ℤ) × ℤ)),
      K ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps ∧ (2 : ℝ) ^ steps ≤ 2 * K ^ (100 : ℕ) ∧
      ε ≤ ε * (2 : ℝ) ^ steps ∧ ε * (2 : ℝ) ^ steps ≤ θ ∧
      (S.card : ℝ) * (ε * (2 : ℝ) ^ steps) ^ ((3 : ℝ) + d) ≤
        8 * K ^ (301 : ℕ) * θ ^ d ∧
      ∀ x ∈ E, gridCode z (fun x => θ * X x)
        (ε * (2 : ℝ) ^ steps) (ε * (2 : ℝ) ^ steps) x ∈ S := by
  obtain ⟨steps, hlo, hhi, hres⟩ := exists_clock_coarsening_steps hε hθ hK hεζ hmargin
  obtain ⟨S, hS, hcover⟩ := clock_isotropic_support_height_calibrated
    E z X hε hε1 hθ hK hθK hcensus steps hlo hres
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hθd : 0 ≤ θ ^ d := Real.rpow_nonneg hθ.le _
  refine ⟨steps, S, hlo, hhi, ?_, hres, hS.trans ?_, hcover⟩
  · exact le_mul_of_one_le_right hε.le ((one_le_pow₀ hK).trans hlo)
  · calc
      _ ≤ K * θ ^ d * (2 * K ^ (100 : ℕ)) ^ 3 := by gcongr
      _ = _ := by ring

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
