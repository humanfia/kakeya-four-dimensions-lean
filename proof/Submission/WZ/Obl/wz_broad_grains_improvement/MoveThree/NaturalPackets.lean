-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NaturalPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NaturalPackets.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainCoefficient
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (boxAxis inner_boxAxis confined_prism_anchor_cover)

noncomputable section

/-- Each confined packet has a uniformly bounded palette of anchors at the
natural expanded-plate scale. The original indices serve as anchors. -/
theorem confined_packet_anchors {L K A : ℕ} {a ρ c s : ℝ}
    (hL : 0 < L) (hA : 1 ≤ A) (ha : 0 < a) (hρ : 0 < ρ) (hc : 0 < c)
    (hac : a ≤ ρ * c) (hs : 0 < s) (hsA : s ≤ A * (a / ρ / c))
    (q : Fin L → Fin K) (ref : Fin K → Fin L) (href : ∀ k, q (ref k) = k)
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V)
    (hgeom : ∀ i j, q i = q j →
      ‖boxAxis (e i) 0 - boxAxis (e j) 0‖ ≤ s / 100 ∧
      ‖z i - z j‖ ≤ c / 100 ∧
      |inner ℝ (boxAxis (e j) 0) (z i - z j)| ≤ s * c / 100) :
    ∃ anchor : Fin K → Fin ((128 * A ^ 2 + 1) ^ 6) → Fin L,
      (∀ k t, q (anchor k t) = k) ∧
      ∀ i, ∃ t, grainNear a ρ c z e (anchor (q i) t) i := by
  classical
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hac' : a / ρ ≤ c := (div_le_iff₀ hρ).mpr (by simpa only [mul_comm] using hac)
  have hsc : s * c ≤ A * (a / ρ) := by
    have hm := mul_le_mul_of_nonneg_right hsA hc.le
    convert hm using 1 <;> field_simp
  have hs0 : 0 ≤ s := hs.le
  have H (k : Fin K) :
      ∃ anchor : Fin ((128 * A ^ 2 + 1) ^ 6) → Fin L,
        (∀ t, q (anchor t) = k) ∧
        ∀ i, q i = k → ∃ t, grainNear a ρ c z e (anchor t) i := by
    let g : Fin L → Fin L := fun i => if q i = k then i else ref k
    have hg (i : Fin L) : q (g i) = k := by
      dsimp [g]
      split_ifs with h
      · exact h
      · exact href k
    have hgi (i : Fin L) (hi : q i = k) : g i = i := by simp [g, hi]
    have hpair (i : Fin L) := hgeom (g i) (ref k) ((hg i).trans (href k).symm)
    obtain ⟨M, hM, aidx, hcover⟩ := confined_prism_anchor_cover hL hA
      (div_pos ha hρ) hc hac' (fun i => z (g i)) (fun i => e (g i))
      (fun i => boxAxis (e (g i)) 0) (z (ref k)) (e (ref k))
      (fun _ => Or.inl rfl)
      (by intro i; exact (hpair i).2.1.trans (by nlinarith))
      (by intro i; rw [← inner_boxAxis]; exact (hpair i).2.2.trans (by nlinarith))
      (by intro i; exact (hpair i).1.trans (by linarith))
    subst M
    refine ⟨fun t => g (aidx t), fun t => hg (aidx t), ?_⟩
    intro i hi
    obtain ⟨t, ht⟩ := hcover i
    refine ⟨t, ?_⟩
    simpa only [grainNear, hgi i hi, show 2 * (a / ρ) = 2 * a / ρ by ring] using ht
  choose anchor hanchor hcover using H
  exact ⟨anchor, hanchor, fun i => hcover (q i) i rfl⟩

/-- Choosing one anchor color globally retains inverse-palette mass, while
every packet then lies in one of the exact local-count neighborhoods. -/
theorem select_natural_packet_color {L K M : ℕ} (hM : 0 < M)
    {a ρ c : ℝ} (q : Fin L → Fin K) (z : Fin L → V)
    (e : Fin L → V ≃ₗᵢ[ℝ] V) (Hg : Fin L → Set V)
    (anchor : Fin K → Fin M → Fin L)
    (hcover : ∀ i, ∃ t, grainNear a ρ c z e (anchor (q i) t) i) :
    ∃ (Q : Finset (Fin L)) (r : Fin K → Fin L),
      (∑ j, μ (Hg j)) ≤ (M : ENNReal) * ∑ j ∈ Q, μ (Hg j) ∧
      ∀ i ∈ Q, grainNear a ρ c z e (r (q i)) i := by
  classical
  choose color hcolor using hcover
  obtain ⟨t, hmass⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color
    hM Finset.univ color (fun j => μ (Hg j))
  refine ⟨Finset.univ.filter (fun j => color j = t), fun k => anchor k t, hmass, ?_⟩
  intro i hi
  have ht := (Finset.mem_filter.mp hi).2
  simpa only [ht] using hcolor i

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
