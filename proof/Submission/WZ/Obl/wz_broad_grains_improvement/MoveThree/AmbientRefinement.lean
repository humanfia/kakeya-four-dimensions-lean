-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.AmbientRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/AmbientRefinement.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainDensityCap
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainMass
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Mono

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (assignedFiber half_mass_after_loss)

noncomputable section

/-- A state for a retained ambient shading lifts back to the original
family by paying the ambient retention exponent. -/
theorem stage_of_ambient_refinement {ω ζ δ h e ρ c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (he : 0 ≤ e)
    {n j : ℕ} {x v : Fin n → V} {Y Y' : Fin n → Set V}
    (hsub : ∀ i, Y' i ⊆ Y i)
    (hretain : O (δ ^ e) * ∑ i, μ (Y i) ≤ ∑ i, μ (Y' i))
    (hJ : J ω ζ δ h ρ c n x v Y' j) :
    J ω ζ δ (h + e) ρ c n x v Y j := by
  obtain ⟨S, Z, N, y, w, f, a, g, hC, hρ, hg, hB, hH, hstop⟩ := hJ
  have hCmono := cover_mono hδ hδ1 (show h ≤ h + e by linarith) hC
  refine ⟨S, Z, N, y, w, f, a, g, ?_, hρ, hg,
    Broad_mono hδ hδ1 (by linarith) hB, ?_, hstop⟩
  · refine ⟨fun i => ⟨(hC.1 i).1, ((hC.1 i).2.1).trans (hsub i), (hC.1 i).2.2⟩,
      ?_, hCmono.2.2⟩
    calc
      _ = O (δ ^ h) * (O (δ ^ e) * ∑ i, μ (Y i)) := by
        rw [Real.rpow_add hδ]
        change ENNReal.ofReal (δ ^ h * δ ^ e) * _ = _
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le h), mul_assoc]
      _ ≤ O (δ ^ h) * ∑ i, μ (Y' i) := mul_le_mul' le_rfl hretain
      _ ≤ _ := hC.2.1
  · exact grains_mono hδ hδ1 (by linarith) hH

/-- Removing a small amount of grain mass yields a state whose ambient
family itself lies in the good set. This lets all subsequent refinements
inherit a density cap without changing their geometric arguments. -/
theorem stage_inside_common_cut {ω ζ δ h h' h'' ρ c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (hh' : h ≤ h'')
    (hbudget : O (δ ^ h') ≤ O (1 / 4 : ℝ) * O (δ ^ h))
    (hdensity : h + h' ≤ h'')
    {n N L j : ℕ} {x v : Fin n → V} {Y Z : Fin n → Set V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    {a g : ℝ} {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {Hg : Fin L → Set V} {γ : Fin L → Fin N} {m : ℝ}
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hρ : δ ^ (1 - ω / 100) ≤ ρ) (hg : 0 < g)
    (hB : Broad ω ζ δ h ρ n N v S Z f)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c 0 g L z e Hg γ m)
    (hstop : (1 ≤ j → δ ^ ζ * (ρ / δ) * N / n ≤ c) ∧
      (2 ≤ j → ρ ≤ δ ^ (ω / 100)) ∧ (3 ≤ j → g ≤ δ ^ (-ζ)))
    {Γ : Set V} (hΓ : MeasurableSet Γ)
    (hloss : (∑ k, μ (Hg k \ Γ)) ≤ (1 / 2 : ENNReal) * ∑ k, μ (Hg k)) :
    A δ h'' (δ ^ (-h'')) (δ ^ (-h'')) n x v (fun i => Y i ∩ Γ) ∧
      O (δ ^ h') * ∑ i, μ (Y i) ≤ ∑ i, μ (Y i ∩ Γ) ∧
      J ω ζ δ h' ρ c n x v (fun i => Y i ∩ Γ) j := by
  have hfin : (∑ k, μ (Hg k)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun k _ => (grain_real_weights hδ hG).1 k)
  have hsplit : (∑ k, μ (Hg k)) ≤ (∑ k, μ (Hg k ∩ Γ)) + ∑ k, μ (Hg k \ Γ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => (measure_inter_add_sdiff (Hg k) hΓ).symm.le
  have hkeep := half_mass_after_loss hfin hsplit hloss
  have hkeep' : O (1 / 2 : ℝ) * ∑ k, μ (Hg k) ≤ ∑ k, μ (Hg k ∩ Γ) := by
    simpa [O, ENNReal.ofReal_div_of_pos] using hkeep
  let W := fun i => Z i ∩ assignedFiber γ (fun k => Hg k ∩ Γ) (f i)
  have hC' : C δ h' n x v Y S W ρ N y w f True :=
    cover_of_grain_refinement hδ hδ1 hh (by norm_num : (0 : ℝ) ≤ 1 / 2) hC hG
      (fun k => (hG.2.2.2.2.1 k).1.inter hΓ) (fun _ => inter_subset_left) hkeep'
      (by simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using hbudget)
  have hWΓ i : W i ⊆ Γ := by rintro q ⟨hq, k, hk, hqk⟩; exact hqk.2
  have hWsub i : W i ⊆ Y i ∩ Γ := fun q hq => ⟨(hC'.1 i).2.1 hq, hWΓ i hq⟩
  have hamb : O (δ ^ h') * ∑ i, μ (Y i) ≤ ∑ i, μ (Y i ∩ Γ) :=
    hC'.2.1.trans ((Finset.sum_le_sum fun i _ => measure_mono (hWsub i)).trans
      (Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)))
  have hAm := admissible_mono hδ hδ1 hh' hA
  refine ⟨⟨hA.1, fun i => ⟨(hA.2.1 i).1, (hA.2.1 i).2.1,
    (hA.2.1 i).2.2.1.inter hΓ, inter_subset_left.trans (hA.2.1 i).2.2.2⟩,
    hA.2.2.1, ?_, hAm.2.2.2.2⟩, hamb, ?_⟩
  · calc
      _ ≤ O (δ ^ (h + h') * n * δ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hdensity) (Nat.cast_nonneg n)
      _ = O (δ ^ h') * O (δ ^ h * n * δ ^ 2) := by
        rw [Real.rpow_add hδ, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        congr 1
        ring
      _ ≤ O (δ ^ h') * ∑ i, μ (Y i) := mul_le_mul' le_rfl hA.2.2.2.1
      _ ≤ _ := hamb
  · have hmass : O (δ ^ h' * L * a * (ρ * c) * c) ≤ ∑ k, μ (Hg k ∩ Γ) := by
      have hb : O (δ ^ h') ≤ O (1 / 2 : ℝ) * O (δ ^ h) :=
        hbudget.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by norm_num)) le_rfl)
      calc
        _ = O (δ ^ h') * O (L * a * (ρ * c) * c) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]; congr 1; ring
        _ ≤ (O (1 / 2 : ℝ) * O (δ ^ h)) * O (L * a * (ρ * c) * c) := mul_le_mul' hb le_rfl
        _ = O (1 / 2 : ℝ) * O (δ ^ h * L * a * (ρ * c) * c) := by
          rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]; congr 2; ring
        _ ≤ O (1 / 2 : ℝ) * ∑ k, μ (Hg k) := mul_le_mul' le_rfl hG.2.2.2.2.2.2.2.1
        _ ≤ _ := hkeep'
    refine ⟨S, W, N, y, w, f, a, g, ?_, hρ, hg,
      Broad_mono hδ hδ1 hh (broad_restrict_fibres _ hB),
      ⟨L, z, e, (fun k => Hg k ∩ Γ), γ, m,
        grainWitnesses_of_refinement hG (fun k => (hG.2.2.2.2.1 k).1.inter hΓ)
          (fun _ => inter_subset_left) hmass⟩, hstop⟩
    refine ⟨fun i => ⟨(hC'.1 i).1, hWsub i, (hC'.1 i).2.2⟩, ?_, hC'.2.2⟩
    exact (mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => measure_mono inter_subset_left)).trans hC'.2.1

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
