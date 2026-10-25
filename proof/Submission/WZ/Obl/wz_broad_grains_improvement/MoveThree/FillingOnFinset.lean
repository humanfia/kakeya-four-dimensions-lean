-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FillingOnFinset.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FillingOnFinset.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FillingOnFinset.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FlatPrismNet
import Submission.WZ.Obl.wz_separated_cover_refinement.Covers

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open scoped ENNReal Classical
open WangZahlLot.Obl.wz_separated_cover_refinement
  (enumerate enumerate_mem enumerate_injective enumerate_surjective enumerate_count enumerate_sum ncard_setOf)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent (uniformMap)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit pd)

/-- First filling on an occupied set of original indices. The original labels
are preserved, allowing the resulting counts to be summed over angular packets. -/
theorem flat_prism_dense_net_input_on_finset {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) {δ a b θ β C lam D k : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hδa : δ ≤ a) (hab : a ≤ b)
    (hb : b ≤ 4) (hθ1 : θ ≤ 1) (hr : δ + 5 * (a / 2) ≤ 1 / 100)
    (hflat : 100 * (δ + 5 * (a / 2)) ≤ 3 * b)
    (hθ : 32 * (δ + 5 * (a / 2)) ≤ θ) (hθb : θ ≤ 3 * b)
    (hlam : 0 < lam) (hC : 0 < C) (hD : 0 < D) (hk : 0 < k) (hksmall : k ≤ 1 / 1000000000)
    (hsmall : C * (θ / (3 * b)) ^ β ≤ lam / 8)
    (hnum : D * (10 ^ 13 * ((3 * b) / θ) * (1 + Real.log (1 / δ))) ≤
      (lam / 16000) ^ 2 * (48 * lam))
    (x v : Fin n → V) (Y : Fin n → Set V) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hvlo : ∀ i ∈ S, (1 / 4 : ℝ) ≤ ‖v i‖) (hvhi : ∀ i ∈ S, ‖v i‖ ≤ 1)
    (hends : ∀ i ∈ S, x i ∈ P a b 4 z e ∧ x i + v i ∈ P a b 4 z e)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hzero : ∀ i, i ∉ S → Y i = ∅)
    (hmass : O (768 * lam * δ ^ 2 * S.card) ≤ ∑ i, μ (Y i))
    (hbroad : ∀ (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ 3 * b →
      q n {i | p ∈ Y i ∧ pd (unit (v i)) u ≤ r} ≤
        C * (r / (3 * b)) ^ β * q n {i | p ∈ Y i})
    (f : V ≃ᵃ[ℝ] V)
    (hf : ∀ q i, f.linear q i = (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i * e q i)
    (hfvol : ∀ Q : Set V, μ (f '' Q) = O (1 / (4 * a * b)) * μ Q)
    (hfball : f '' P a b 4 z e ⊆ ball (0 : V) 1) :
    let F := f.trans (uniformMap hk).toAffineEquiv
    let B := 256 * k * δ / a
    ∃ (G : Finset (Fin n)) (u : Fin n → Fin 3 → V),
      G ⊆ S ∧ G.Nonempty ∧ (lam / 8) * S.card ≤ (G.card : ℝ) ∧ B ≤ 1 / 1000000 ∧
      ∀ i ∈ G, O (48 * lam * δ ^ 2) ≤ μ (Y i) ∧ Orthonormal ℝ (u i) ∧ ‖F (x i + (1 / 2 : ℝ) • v i)‖ < 1 / 100 ∧
        F '' T δ (x i) (v i) ⊆ WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          B B (F (x i + (1 / 2 : ℝ) • v i)) (u i) ∧
        O ((D * k / 16000) * B ^ 2) ≤ μ
          (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
            B B (F (x i + (1 / 2 : ℝ) • v i)) (u i) ∩ F '' (⋃ j, Y j)) := by
  classical
  let ι := enumerate S
  have hιmem (i : Fin S.card) : ι i ∈ S := enumerate_mem S i
  have hιinj : Function.Injective ι := enumerate_injective S
  have hmass' : (∑ i, μ (Y (ι i))) = ∑ i, μ (Y i) := by
    change (∑ i, μ (Y (enumerate S i))) = _
    rw [enumerate_sum S (fun i => μ (Y i))]
    exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hzero i hi, μ])
  have hcount (Q : Fin n → Prop) (hQ : ∀ i, Q i → i ∈ S) :
      q S.card {i | Q (ι i)} = q n {i | Q i} := by
    dsimp only [q]
    congr 1
    rw [enumerate_count, ncard_setOf]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right, fun hi => ⟨hQ i hi, hi⟩⟩
  have hsupport i (p : V) (hp : p ∈ Y i) : i ∈ S := by
    by_contra hi
    simpa only [hzero i hi, mem_empty_iff_false] using hp
  have hbr : ∀ (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ 3 * b →
      q S.card {i | p ∈ Y (ι i) ∧ pd (unit (v (ι i))) u ≤ r} ≤
        C * (r / (3 * b)) ^ β * q S.card {i | p ∈ Y (ι i)} := by
    intro p u r hu hr hrb
    rw [hcount (fun i => p ∈ Y i ∧ pd (unit (v i)) u ≤ r)
      (fun i hi => hsupport i p hi.1), hcount (fun i => p ∈ Y i) (fun i hi => hsupport i p hi)]
    exact hbroad p u r hu hr hrb
  have hUnion : (⋃ j, Y (ι j)) = ⋃ j, Y j := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => subset_iUnion Y (ι i)
    · apply iUnion_subset
      intro i p hp
      obtain ⟨j, hj⟩ := enumerate_surjective S (hsupport i p hp)
      exact mem_iUnion.mpr ⟨j, by simpa only [ι, hj] using hp⟩
  obtain ⟨G, u, hG, hcard, hB, hdata⟩ :=
    flat_prism_dense_net_input_of_coefficients (Finset.card_pos.mpr hS)
      hδ hδ1 hδa hab hb hθ1 hr hflat hθ hθb hlam hC hD hk hksmall hsmall hnum
      (x ∘ ι) (v ∘ ι) (Y ∘ ι) z e
      (fun i => hvlo _ (hιmem i)) (fun i => hvhi _ (hιmem i))
      (fun i => hends _ (hιmem i)) (fun i => hYm _) (fun i => hYT _)
      (by simpa only [Function.comp_apply, hmass'] using hmass) hbr f hf hfvol hfball
  let u' := Function.extend ι u (fun _ _ => (0 : V))
  have hext i : u' (ι i) = u i := hιinj.extend_apply u _ i
  refine ⟨G.image ι, u', ?_, hG.image ι, ?_, hB, ?_⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact hιmem j
  · simpa only [Finset.card_image_of_injective _ hιinj] using hcard
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    simpa only [Function.comp_apply, hext, hUnion] using hdata j hj

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
