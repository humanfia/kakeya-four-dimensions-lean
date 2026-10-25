-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.CoverTransport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.ReverseConvex
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.ReverseSlabs
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.ParentSlabs
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Reindex

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

attribute [local irreducible] normalize

set_option maxHeartbeats 800000 in
/-- Transport a balanced selection of whole normalized fibres to unit physical covers. -/
lemma transport_balanced_cover (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {r s ρ B H L₀ Lc Lf : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1 / 100)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / (100 * coverScale))
    (hsmall : normalizedRadius r s ≤ contraction ^ 2)
    (hB : 0 ≤ B) (hH : 0 < H) (hL₀ : 0 ≤ L₀) (hLc : 0 ≤ Lc)
    (hw : ‖w‖ = 1) {n M N : ℕ} (hn : 0 < n)
    (x v : Fin n → Space) (j : Fin M → Fin n) (hj : Function.Injective j)
    (z u : Fin M → Space) (Z U : Fin N → Space) (f : Fin M → Fin N)
    (S S' : Finset (Fin M)) (hS : S' ⊆ S)
    (hwhole : ∀ i ∈ S', ∀ j ∈ S, f i = f j → j ∈ S')
    (hret : H * n ≤ S'.card)
    (hbal : ∀ i ∈ S', ∀ j ∈ S',
      ((S'.filter (fun k => f k = f i)).card : ℝ) ≤ B * (S'.filter (fun k => f k = f j)).card)
    (hv : ∀ i, ‖v i‖ = 1) (hu : ∀ i, ‖u i‖ = 1) (hU : ∀ k, ‖U k‖ = 1)
    (hT : ∀ i, tube s (x i) (v i) ⊆ tube r y w)
    (hforward : ∀ i, normalize e y w r hr '' tube s (x (j i)) (v (j i)) ⊆
      tube (normalizedRadius r s) (z i) (u i))
    (hmid : ∀ i, z i + (1 / 2 : ℝ) • u i = normalize e y w r hr (x (j i) + (1 / 2 : ℝ) • v (j i)))
    (hcover : ∀ i ∈ S, tube (normalizedRadius r s) (z i) (u i) ⊆ tube ρ (Z (f i)) (U (f i)))
    (hK : ConvexCount ρ Lc (fun _ => True) (fun k => tube ρ (Z k) (U k)))
    (hSb : SlabBound (doubled r y w) L₀ (fun _ => True) (fun i => tube s (x i) (v i)))
    (hSf : ∀ k, SlabBound (doubled ρ (Z k) (U k)) Lf
      (fun i => i ∈ S ∧ f i = k) (fun i => tube (normalizedRadius r s) (z i) (u i))) :
    ∃ (N' : ℕ) (X V : Fin N' → Space) (g : Fin M → Fin N'),
      0 < N' ∧
      (∀ k, ‖V k‖ = 1 ∧ tube (coverScale * r * ρ) (X k) (V k) ⊆ tube (2 * r) y w) ∧
      (∀ i ∈ S', tube s (x (j i)) (v (j i)) ⊆ doubled (coverScale * r * ρ) (X (g i)) (V (g i))) ∧
      ConvexCount (coverScale * r * ρ) (coarseConvexLoss * Lc) (fun _ => True)
        (fun k => tube (coverScale * r * ρ) (X k) (V k)) ∧
      SlabBound (doubled r y w) (2000000 * (B * L₀ / H)) (fun _ => True)
        (fun k => tube (coverScale * r * ρ) (X k) (V k)) ∧
      ∀ k, SlabBound (doubled (coverScale * r * ρ) (X k) (V k)) (localSlabLoss * Lf)
        (fun i => i ∈ S' ∧ g i = k) (fun i => tube s (x (j i)) (v (j i))) := by
  classical
  have hscale := coverScale_pos
  have hS' : S'.Nonempty := by
    apply Finset.card_pos.mp
    have hh : 0 < (S'.card : ℝ) := (mul_pos hH (Nat.cast_pos.mpr hn)).trans_le hret
    exact_mod_cast hh
  obtain ⟨N', b, g, rep, hN', hb, hrep, hbg, hpred⟩ := reindex_whole_fibres S S' hS hS' f hwhole
  let X := fun k => x (j (rep k))
  let V := fun k => v (j (rep k))
  have hρk : ρ ≤ contraction ^ 2 := by
    have hh := hρsmall
    norm_num [coverScale, contraction] at hh ⊢
    linarith
  have hRr : coverScale * r * ρ ≤ r / 100 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 100 * coverScale)).mp hρsmall
    have hh' := mul_le_mul_of_nonneg_right hh hr.le
    nlinarith
  have hR1 : 2 * (coverScale * r * ρ) ≤ 1 := by linarith
  have hc (k) : tube (normalizedRadius r s) (z (rep k)) (u (rep k)) ⊆ tube ρ (Z (b k)) (U (b k)) := by
    simpa only [(hrep k).2] using hcover (rep k) (hS (hrep k).1)
  have hf (k) : normalize e y w r hr '' tube s (X k) (V k) ⊆ tube ρ (Z (b k)) (U (b k)) :=
    (hforward (rep k)).trans (hc k)
  have hmidt (k) (i) (hi : i ∈ S') (hik : f i = b k) :
      ‖normalize e y w r hr (x (j i) + (1 / 2 : ℝ) • v (j i)) -
        normalize e y w r hr (X k + (1 / 2 : ℝ) • V k)‖ ≤ 6 * ρ := by
    have hh₀ := tube_midpoints_close (normalizedRadius_pos hr hs) (hu i) (hU (b k))
      (by simpa only [hik] using hcover i (hS hi))
    have hh₁ := tube_midpoints_close (normalizedRadius_pos hr hs) (hu (rep k)) (hU (b k)) (hc k)
    rw [hmid i] at hh₀
    rw [hmid (rep k)] at hh₁
    have hh₁' : dist (normalize e y w r hr (X k + (1 / 2 : ℝ) • V k))
        (Z (b k) + (1 / 2 : ℝ) • U (b k)) < 3 * ρ := hh₁
    have hh := dist_triangle_right
      (normalize e y w r hr (x (j i) + (1 / 2 : ℝ) • v (j i)))
      (normalize e y w r hr (X k + (1 / 2 : ℝ) • V k))
      (Z (b k) + (1 / 2 : ℝ) • U (b k))
    rw [dist_eq_norm] at hh
    linarith only [hh, hh₀, hh₁']
  have hchild (i) (hi : i ∈ S') : tube s (x (j i)) (v (j i)) ⊆
      doubled (coverScale * r * ρ) (X (g i)) (V (g i)) := by
    apply child_in_physical_cover e hew hr hr1 hs hs1 hρ hρsmall
      (hv (j (rep (g i)))) (hv (j i)) hw (hU (b (g i))) (hT (j (rep (g i)))) (hf (g i))
      ((hforward i).trans (by simpa only [hbg i hi] using hcover i (hS hi)))
    simpa only [dist_eq_norm] using hmidt (g i) i hi (hbg i hi).symm
  have hfilter (k) : S'.filter (fun i => g i = k) = S'.filter (fun i => f i = b k) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hik⟩
      exact ⟨hi, by rw [← hbg i hi, hik]⟩
    · rintro ⟨hi, hif⟩
      exact ⟨hi, hb ((hbg i hi).trans hif)⟩
  have hbal' (k l) : ((S'.filter (fun i => g i = k)).card : ℝ) ≤ B * (S'.filter (fun i => g i = l)).card := by
    rw [hfilter, hfilter]
    simpa only [(hrep k).2, (hrep l).2] using hbal (rep k) (hrep k).1 (rep l) (hrep l).1
  refine ⟨N', X, V, g, hN', ?_, hchild, ?_, ?_, ?_⟩
  · intro k
    exact ⟨hv (j (rep k)), tube_enlarge_inside_parent hs (hRr.trans (by linarith only [hr])) (hT (j (rep k)))⟩
  · apply reverse_convex_count e y w hr hρ hLc X V (Z ∘ b) (U ∘ b)
    · intro k
      exact (tube_subset_doubled hρ.le (Z (b k)) (U (b k))).trans
        (normalized_coarse_expansion e hew hr hr1 hs hρ hρk (hv (j (rep k))) hw (hU (b k)) (hT (j (rep k))) (hf k))
    · exact convexCount_subfamily (s := ρ) (L := Lc)
        (U := fun k => tube ρ (Z k) (U k)) b hb hK
  · apply parent_cover_slab hr (by positivity) hn S' g j hj hB hH hL₀ hret hbal' y w x v X V hT
      (fun k => hT (j (rep k)) (self_subset_thickening hs _
        (by simpa using centered_segment (X k) (V k) (a := 0) (by norm_num)))) hchild hSb
  · intro k
    have hpred' : (fun i => i ∈ S' ∧ g i = k) = (fun i => i ∈ S ∧ f i = b k) :=
      funext fun i => propext (hpred k i)
    apply physical_fibre_slab e hew hr hr1 hs hρ hρk hsmall hR1 (hv (j (rep k))) hw (hU (b k)) (hT (j (rep k))) (hf k)
      (fun i => i ∈ S' ∧ g i = k) (x ∘ j) (v ∘ j) z u
      (fun i _ => hv (j i)) (fun i _ => hu i) (fun i _ => hT (j i)) (fun i _ => hforward i)
    · intro i hi
      have hh := (hpred k i).mp hi
      simpa only [hh.2] using hcover i hh.1
    · intro i hi
      exact hmidt k i hi.1 ((hpred k i).mp hi).2
    · rw [hpred']
      exact hSf (b k)

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
