-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ConcentratedPacking.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainOverlapCount
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.RoundBodyPacking

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (frozen_prism_convex)
open WangZahlLot.Obl.wz_flat_factored_improvement (BodyPacking)

noncomputable section

def grainPackingColors (δ ε : ℝ) : ℕ :=
  ⌈grainOverlapConstant (1 / 20000) * δ ^ (-(21 * ε / 40))⌉₊ + 1

def grainPackingCoefficient (δ ε : ℝ) : ℝ :=
  10000000 * Real.sqrt (grainPackingColors δ ε)

namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

/-- Large-overlap degrees are unchanged by the common affine normalization,
after accounting for its exact volume factor. -/
theorem selected_image_overlap_degree (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {k : ℕ} (ι : Fin k → Fin D.L) (hιinj : Function.Injective ι)
    (hι : ∀ j, ι j ∈ D.Q) (f : V ≃ᵃ[ℝ] V)
    (hvol : ∀ W, μ (f '' W) = O (ρ / (64 * D.a * c ^ 2)) * μ W) (i : Fin k) :
    (Finset.univ.filter fun j => O (ρ ^ 2 / 1280000) <
      μ ((f '' P D.a (ρ * c) c (D.z (ι i)) (D.e (ι i))) ∩
        (f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))))).card ≤ grainPackingColors δ ε := by
  classical
  obtain ⟨ha, hρ, -, hc, -⟩ := D.dimensions hδ
  let U := fun j : Fin D.L => P D.a (ρ * c) c (D.z j) (D.e j)
  let F := Finset.univ.filter fun j => O (ρ ^ 2 / 1280000) < μ ((f '' U (ι i)) ∩ (f '' U (ι j)))
  let R := D.Q.filter fun j => O ((1 / 20000 : ℝ) * (D.a * (ρ * c) * c)) < μ (U (ι i) ∩ U j)
  have hthreshold : O (ρ ^ 2 / 1280000) = O (ρ / (64 * D.a * c ^ 2)) *
      O ((1 / 20000 : ℝ) * (D.a * (ρ * c) * c)) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ρ / (64 * D.a * c ^ 2))]
    congr 1
    field_simp
    <;> ring
  have hFR : F.image ι ⊆ R := by
    intro j hj
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
    refine Finset.mem_filter.mpr ⟨hι l, ?_⟩
    have hh := (Finset.mem_filter.mp hl).2
    rw [← Set.image_inter f.injective, hvol, hthreshold] at hh
    by_contra hn
    exact not_lt_of_ge (mul_le_mul' le_rfl (le_of_not_gt hn)) hh
  have hcard : F.card ≤ R.card := by
    calc
      _ = (F.image ι).card := (Finset.card_image_of_injective F hιinj).symm
      _ ≤ _ := Finset.card_le_card hFR
  have hR : (R.card : ℝ) ≤ grainOverlapConstant (1 / 20000) * δ ^ (-(21 * ε / 40)) :=
    D.selected_overlap_count hδ (by norm_num : (0 : ℝ) < 1 / 20000) (ι i)
  have hceil : F.card ≤ ⌈grainOverlapConstant (1 / 20000) * δ ^ (-(21 * ε / 40))⌉₊ := by
    exact_mod_cast (Nat.cast_le.mpr hcard).trans (hR.trans (Nat.le_ceil _))
  exact hceil.trans (Nat.le_succ _)

/-- The normalized selected grains have a packing constant depending only
on their density loss, independently of the large convex concentration. -/
theorem selected_image_packing (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {k : ℕ} (ι : Fin k → Fin D.L) (hιinj : Function.Injective ι)
    (hι : ∀ j, ι j ∈ D.Q) (f : V ≃ᵃ[ℝ] V)
    (hvol : ∀ W, μ (f '' W) = O (ρ / (64 * D.a * c ^ 2)) * μ W)
    (hball : ∀ j, ball (f (D.z (ι j))) (ρ / 100) ⊆
      f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)))
    (hlong : ∀ j, ∃ p ∈ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)),
      ∃ q ∈ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)), (1 / 4 : ℝ) ≤ dist p q) :
    BodyPacking (fun j => f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)))
      (ρ ^ 2 / 64) (grainPackingCoefficient δ ε) := by
  obtain ⟨-, hρ, -, -, -⟩ := D.dimensions hδ
  apply round_body_packing hρ (Nat.succ_pos _)
    (fun j => f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)))
    (fun j => f (D.z (ι j)))
    (fun j => (frozen_prism_convex _ _ _ _ _).affine_image f.toAffineMap) hball hlong
  exact D.selected_image_overlap_degree hδ ι hιinj hι f hvol

end ConcentratedGrainData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
