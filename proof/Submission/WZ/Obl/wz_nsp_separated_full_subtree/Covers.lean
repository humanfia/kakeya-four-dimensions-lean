-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_separated_full_subtree.Covers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_separated_full_subtree.Selection

namespace WangZahlLot.Obl.wz_nsp_separated_full_subtree

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

lemma local_count_transfer {δ r L K c a N : ℝ} {V : ENNReal}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hL : L ≤ K * c)
    (hfull : c * r ^ 2 ≤ N * δ ^ 2)
    (hcount : ENNReal.ofReal (a * δ ^ 2) ≤ ENNReal.ofReal L * V) :
    ENNReal.ofReal (a * r ^ 2) ≤ ENNReal.ofReal (K * N) * V := by
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hcoef : r ^ 2 / δ ^ 2 * L ≤ K * N := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ2]
    have h1 := mul_le_mul_of_nonneg_right hL (sq_nonneg r)
    have h2 := mul_le_mul_of_nonneg_left hfull hK
    nlinarith only [h1, h2]
  calc
    ENNReal.ofReal (a * r ^ 2) =
        ENNReal.ofReal (r ^ 2 / δ ^ 2) * ENNReal.ofReal (a * δ ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal (r ^ 2 / δ ^ 2) * (ENNReal.ofReal L * V) :=
      mul_le_mul' le_rfl hcount
    _ = ENNReal.ofReal (r ^ 2 / δ ^ 2 * L) * V := by
      rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ ENNReal.ofReal (K * N) * V := mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl

/-- Reindex the occupied parents of a separated, balanced, full selection. -/
theorem selected_cover {δ r L K c R : ℝ} {m k : ℕ}
    (hδ : 0 < δ) (hr : 0 < r) (hK : 0 ≤ K) (hRK : R ≤ K) (hL : L ≤ K * c)
    (x v : Fin m → Space) (z w : Fin k → Space) (f : Fin m → Fin k)
    (hv : ∀ s, ‖v s‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (hcount : ConvexCount δ L x v)
    (hcontain : ∀ s, Tube δ (x s) (v s) ⊆ Tube r (z (f s)) (w (f s)))
    (S : Finset (Fin m)) (hS : S.Nonempty)
    (hnear : ∀ s ∈ S, ∀ t ∈ S, f s ≠ f t → ¬Near r (z (f s)) (w (f s)) (z (f t)) (w (f t)))
    (hbal : Balanced S f R)
    (hfull : ∀ s ∈ S, c * r ^ 2 ≤ ((S.filter (fun t => f t = f s)).card : ℝ) * δ ^ 2) :
    ∃ k' : ℕ, 0 < k' ∧ ∃ z' w' : Fin k' → Space,
      WangZahlLot.Obl.wz_separated_cover_refinement.CoverAt δ K r
        (fun s => x (WangZahlLot.Obl.wz_separated_cover_refinement.enumerate S s))
        (fun s => v (WangZahlLot.Obl.wz_separated_cover_refinement.enumerate S s)) z' w' := by
  classical
  let G := S.image f
  let e := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate S
  let b := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate G
  have hemem : ∀ s, e s ∈ S := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_mem S
  have hbmem : ∀ j, b j ∈ G := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_mem G
  have hbinj : Function.Injective b := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_injective G
  have hG : 0 < G.card := Finset.card_pos.mpr (hS.image f)
  have hf : ∀ s ∈ S, ∀ i ∈ G, Tube δ (x s) (v s) ⊆ Tube r (z i) (w i) ↔ f s = i := by
    intro s hs i hi
    constructor
    · intro hsi
      obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hi
      by_contra hne
      have hn := hnear s hs t ht (by simpa only [hti] using hne)
      apply hn
      rw [hti]
      exact near_of_common_child hδ hr (hv s) (hw (f s)) (hw i) (hcontain s) hsi
    · rintro rfl
      exact hcontain s
  have hparent : ∀ s, ∃ j, f (e s) = b j := by
    intro s
    obtain ⟨j, hj⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_surjective G
      (Finset.mem_image.mpr ⟨e s, hemem s, rfl⟩)
    exact ⟨j, hj.symm⟩
  have hoccupied : ∀ j, ∃ s ∈ S, f s = b j := by
    intro j
    exact Finset.mem_image.mp (hbmem j)
  have hnew : ∀ j, ncard {s | Tube δ (x (e s)) (v (e s)) ⊆ Tube r (z (b j)) (w (b j))} =
      (S.filter (fun s => f s = b j)).card := by
    intro j
    rw [WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_count S
      (fun s => Tube δ (x s) (v s) ⊆ Tube r (z (b j)) (w (b j)))]
    congr 1
    ext s
    simp only [Finset.mem_filter]
    exact and_congr_right fun hs => hf s hs (b j) (hbmem j)
  refine ⟨G.card, hG, (fun j => z (b j)), (fun j => w (b j)), ?_⟩
  refine ⟨(fun j => hw (b j)), ?_, ?_, ?_, ?_, ?_⟩
  · intro j j' hjj'
    apply separated_of_not_near hr (hw (b j)) (hw (b j'))
    obtain ⟨s, hs, hsj⟩ := hoccupied j
    obtain ⟨t, ht, htj⟩ := hoccupied j'
    have hn := hnear s hs t ht (by simpa only [hsj, htj] using hbinj.ne hjj')
    simpa only [hsj, htj] using hn
  · intro s
    obtain ⟨j, hj⟩ := hparent s
    refine ⟨j, (hf (e s) (hemem s) (b j) (hbmem j)).mpr hj, ?_⟩
    intro j' hj'
    exact hbinj (((hf (e s) (hemem s) (b j') (hbmem j')).mp hj').symm.trans hj)
  · intro j
    obtain ⟨s, hs, hsj⟩ := hoccupied j
    obtain ⟨a, rfl⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_surjective S hs
    exact ⟨a, (hf _ (hemem a) _ (hbmem j)).mpr hsj⟩
  · intro j j'
    rw [hnew, hnew]
    obtain ⟨s, hs, hsj⟩ := hoccupied j
    obtain ⟨t, ht, htj⟩ := hoccupied j'
    have hb := hbal s hs t ht
    dsimp only [WangZahlLot.Obl.wz_tower_balanced_refinement.leafFiber] at hb
    rw [hsj, htj] at hb
    have hR' : R * ((S.filter (fun a => f a = b j')).card : ℝ) ≤
        K * ((S.filter (fun a => f a = b j')).card : ℝ) :=
      mul_le_mul_of_nonneg_right hRK (Nat.cast_nonneg _)
    apply le_trans ?_ hR'
    convert hb using 1 <;> congr 2 <;> (try apply congrArg Finset.card) <;> ext a <;> simp
  · intro j W hW
    let M := ncard {s | Tube δ (x (e s)) (v (e s)) ⊆ Tube r (z (b j)) (w (b j)) ∧
      Tube δ (x (e s)) (v (e s)) ⊆ W}
    have hM : M ≤ ncard {s | Tube δ (x s) (v s) ⊆ W} := by
      dsimp [M, e]
      rw [WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_count S
        (fun s => Tube δ (x s) (v s) ⊆ Tube r (z (b j)) (w (b j)) ∧ Tube δ (x s) (v s) ⊆ W),
        WangZahlLot.Obl.wz_separated_cover_refinement.ncard_setOf]
      apply Finset.card_le_card
      intro s hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2.2⟩
    have hMc : ENNReal.ofReal ((M : ℝ) * δ ^ 2) ≤ ENNReal.ofReal L * volume W := by
      apply le_trans _ (hcount W hW)
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hM) (sq_nonneg δ))
    have hF : c * r ^ 2 ≤ ((S.filter (fun a => f a = b j)).card : ℝ) * δ ^ 2 := by
      obtain ⟨s, hs, hsj⟩ := hoccupied j
      have hh := hfull s hs
      rw [hsj] at hh
      exact hh
    rw [hnew]
    exact local_count_transfer hδ hK hL hF hMc

end WangZahlLot.Obl.wz_nsp_separated_full_subtree
