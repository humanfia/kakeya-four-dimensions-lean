-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainDilateCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainDilateCount.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CoarseGrainContainer
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedDensity
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSFibre

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (frozen_prism_volume)

noncomputable section

/-- A fixed dilation contains only a density-controlled number of grains.
The coarse separation bounds the number of occupied parent fibres, and
disjointness within each fibre bounds its total shading mass. -/
theorem grain_dilation_card_bound {a ρ c C θ : ℝ} {L N : ℕ}
    (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1)
    (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hac : a ≤ ρ * c)
    (y w : Fin N → V) (hw : ∀ k, ‖w k‖ = 1) (hX : X ρ N y w)
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (H : Fin L → Set V)
    (γ : Fin L → Fin N) (R : Finset (Fin L)) (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
    (hHm : ∀ j ∈ R, MeasurableSet (H j))
    (hHU : ∀ j ∈ R, H j ⊆ P a (ρ * c) c (z j) (e j))
    (hparent : ∀ j ∈ R, P a (ρ * c) c (z j) (e j) ⊆ T ρ (y (γ j)) (w (γ j)))
    (halign : ∀ j ∈ R, (e j (w (γ j)) 0) ^ 2 + (e j (w (γ j)) 1) ^ 2 ≤ (10 * ρ) ^ 2)
    (hdisj : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → γ i = γ j → Disjoint (H i) (H j))
    (hdense : ∀ j ∈ R, O (θ * (a * (ρ * c) * c)) ≤ μ (H j))
    (hsub : ∀ j ∈ R, P a (ρ * c) c (z j) (e j) ⊆
      P (C * a) (C * (ρ * c)) (C * c) z₀ e₀) :
    θ * R.card ≤ 1000000 * ((4 * C + 44) ^ 2 * (C + 6)) ^ 2 * C ^ 3 := by
  classical
  let U := P (C * a) (C * (ρ * c)) (C * c) z₀ e₀
  let W := P ((4 * C + 44) * ρ) ((4 * C + 44) * ρ) (C + 6) z₀ e₀
  let S := R.image γ
  have hW : μ W = O (((4 * C + 44) ^ 2 * (C + 6)) * ρ ^ 2) := by
    rw [show μ W = O (((4 * C + 44) * ρ) * ((4 * C + 44) * ρ) * (C + 6)) from
      frozen_prism_volume (by positivity) (by positivity) (by positivity) z₀ e₀]
    congr 1
    ring
  have hSW : ∀ k ∈ S, T ρ (y k) (w k) ⊆ W := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact coarse_parent_of_grain_containment ha hρ hρ1 hc hc1 hC hac
      (z j) z₀ (y (γ j)) (w (γ j)) (e j) e₀ (hw (γ j))
      (hparent j hj) (halign j hj) (hsub j hj)
  have hparents : (S.card : ℝ) ≤ 1000000 * ((4 * C + 44) ^ 2 * (C + 6)) ^ 2 :=
    WangZahlLot.Obl.wz_extremal_lipschitz_grains.card_le_of_subset_vol hρ
      (by positivity) y w hw hX W hW.le S hSW
  have hmass : (∑ j ∈ R, μ (H j)) ≤ (S.card : ENNReal) * μ U := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem γ hj)
      (fun j => μ (H j))]
    calc
      _ ≤ ∑ _k ∈ S, μ U := by
        apply Finset.sum_le_sum
        intro k hk
        have hd : ((R.filter fun j => γ j = k) : Set (Fin L)).PairwiseDisjoint H := by
          intro i hi j hj hij
          exact hdisj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij
            ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
        rw [← measure_biUnion_finset hd (fun j hj => hHm j (Finset.mem_filter.mp hj).1)]
        apply measure_mono
        intro q hq
        obtain ⟨j, hj, hq⟩ := mem_iUnion₂.mp hq
        exact hsub j (Finset.mem_filter.mp hj).1 (hHU j (Finset.mem_filter.mp hj).1 hq)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hU : μ U = O (C ^ 3 * (a * (ρ * c) * c)) := by
    rw [show μ U = O ((C * a) * (C * (ρ * c)) * (C * c)) from
      frozen_prism_volume (by positivity) (by positivity) (by positivity) z₀ e₀]
    congr 1
    ring
  have hlo : O ((θ * R.card) * (a * (ρ * c) * c)) ≤ ∑ j ∈ R, μ (H j) := by
    calc
      _ = ∑ _j ∈ R, O (θ * (a * (ρ * c) * c)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg R.card)]
        congr 1
        ring
      _ ≤ _ := Finset.sum_le_sum hdense
  have hreal : (θ * R.card) * (a * (ρ * c) * c) ≤
      ((S.card : ℝ) * C ^ 3) * (a * (ρ * c) * c) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    convert hlo.trans hmass using 1
    rw [hU, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]
    congr 1
    ring
  have hcancel : θ * R.card ≤ (S.card : ℝ) * C ^ 3 :=
    (mul_le_mul_iff_left₀ (by positivity : 0 < a * (ρ * c) * c)).mp hreal
  exact hcancel.trans (mul_le_mul_of_nonneg_right hparents (by positivity))

namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

theorem selected_dilation_count (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {C : ℝ} (hC : 0 ≤ C) (R : Finset (Fin D.L)) (hR : R ⊆ D.Q)
    (z₀ : V) (e₀ : V ≃ₗᵢ[ℝ] V)
    (hsub : ∀ j ∈ R, P D.a (ρ * c) c (D.z j) (D.e j) ⊆
      P (C * D.a) (C * (ρ * c)) (C * c) z₀ e₀) :
    δ ^ (21 * ε / 40) * R.card ≤
      1000000 * ((4 * C + 44) ^ 2 * (C + 6)) ^ 2 * C ^ 3 := by
  obtain ⟨ha, hρ, hρ1, hc, hc1⟩ := D.dimensions hδ
  have hg := D.grains
  apply grain_dilation_card_bound ha hρ hρ1 hc hc1 hC
    (Real.rpow_nonneg hδ.le _) hg.2.1 D.y D.w D.cover.2.2.1 D.cover.2.2.2.2.2.2.2.1
    D.z D.e D.Hg D.γ R z₀ e₀
  · exact fun j _ => (hg.2.2.2.2.1 j).1
  · exact fun j _ => (hg.2.2.2.2.1 j).2.1
  · exact fun j _ => (hg.2.2.2.2.1 j).2.2.1
  · exact fun j _ => (hg.2.2.2.2.1 j).2.2.2
  · exact fun i _ j _ hij hγ => hg.2.2.2.2.2.1 i j hij hγ
  · intro j hj
    have hh := D.selected_density hδ j (hR hj)
    rw [show μ (P D.a (ρ * c) c (D.z j) (D.e j)) = O (D.a * (ρ * c) * c) from
      frozen_prism_volume ha.le (mul_pos hρ hc).le hc.le _ _,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)] at hh
    exact hh
  · exact hsub

end ConcentratedGrainData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
