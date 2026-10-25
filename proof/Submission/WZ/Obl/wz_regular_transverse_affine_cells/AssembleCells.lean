-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.AssembleCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PacketData
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Indexing

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal

lemma select_common_cell_shape {n K : ℕ} {δ h τ : ℝ} {x v : Fin n → E} {Y : Fin n → Set E}
    (L : List (AffineCell n K)) (hL : ∀ G ∈ L, G.Valid δ h x v Y)
    (hdisj : L.Pairwise (fun G G' => Disjoint G.support G'.support))
    (hτ : τ * (K + 1 : ℕ) ^ 2 ≤ 1) :
    ∃ (k l : Fin (K + 1)) (m : ℕ) (G : Fin m → AffineCell n K),
      (∀ j, (G j).Valid δ h x v Y) ∧
      (∀ j, (G j).first = k ∧ (G j).second = l) ∧
      Pairwise (fun j j' => Disjoint (G j).support (G j').support) ∧
      τ * (L.map fun C => (C.indices.card : ℝ)).sum ≤ ∑ j, ((G j).indices.card : ℝ) := by
  classical
  let color : Fin L.length → Fin (K + 1) × Fin (K + 1) := fun j => ((L.get j).first, (L.get j).second)
  let w : Fin L.length → ℝ := fun j => (L.get j).indices.card
  have hw : (0 : ℝ) ≤ ∑ j, w j := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hsum : ∑ j, w j = (L.map fun C => (C.indices.card : ℝ)).sum := by
    have he := congrArg List.sum (List.map_ofFn (f := L.get)
      (g := fun C : AffineCell n K => (C.indices.card : ℝ)))
    simpa only [List.ofFn_get, List.sum_ofFn, Function.comp_apply, w] using he.symm
  have hbudget : Fintype.card (Fin (K + 1) × Fin (K + 1)) • (τ * ∑ j, w j) ≤ ∑ j, w j := by
    simp only [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    have hh := mul_le_mul_of_nonneg_right hτ hw
    nlinarith [hh]
  obtain ⟨kl, hkl⟩ := Fintype.exists_le_sum_fiber_of_nsmul_le_sum (f := color) (w := w) hbudget
  let F := Finset.univ.filter fun j => color j = kl
  let G : Fin F.card → AffineCell n K := fun j => L.get (enumerate F j)
  refine ⟨kl.1, kl.2, F.card, G, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hL _ (List.get_mem L _)
  · intro j
    have hc := (Finset.mem_filter.mp (enumerate_mem F j)).2
    exact ⟨congrArg Prod.fst hc, congrArg Prod.snd hc⟩
  · intro j k hjk
    have hne : enumerate F j ≠ enumerate F k := fun h => hjk ((enumerate F).injective h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact List.pairwise_iff_get.mp hdisj _ _ hlt
    · exact (List.pairwise_iff_get.mp hdisj _ _ hgt).symm
  · rw [← hsum]
    have hs := sum_enumerate F w
    exact hkl.trans hs.symm.le

lemma cells_of_uniform_affine_cells {n K m : ℕ} {δ h : ℝ} {x v : Fin n → E} {Y : Fin n → Set E}
    (hn : 0 < n) (hnmax : (n : ℝ) ≤ δ ^ (-100 : ℝ)) (hm : 0 < m)
    (G : Fin m → AffineCell n K) (k l : Fin (K + 1))
    (hG : ∀ j, (G j).Valid δ h x v Y)
    (hshape : ∀ j, (G j).first = k ∧ (G j).second = l)
    (hdisj : Pairwise (fun j j' => Disjoint (G j).support (G j').support))
    (hmass : h * (n : ℝ) ≤ ∑ j, ((G j).indices.card : ℝ)) : Cells δ h n x v Y := by
  let a : ℝ := (1 / 2 : ℝ) ^ k.val
  let b : ℝ := (1 / 2 : ℝ) ^ l.val
  have ha (j : Fin m) : (G j).a = a := by simp only [AffineCell.a, (hshape j).1, a]
  have hb (j : Fin m) : (G j).b = b := by simp only [AffineCell.b, (hshape j).2, b]
  have hbody (j : Fin m) (i : Fin n) : (G j).body i = prism a b ((G j).center i) ((G j).axes i) := by
    rw [AffineCell.body, ha, hb]
  have hfirst := hG ⟨0, hm⟩
  obtain ⟨_, hamin, hab, hbmax, hδb, _, _, _, _, _, _, _, _, _, _, _⟩ := hfirst
  rw [ha] at hamin
  rw [ha, hb] at hab
  rw [hb] at hbmax hδb
  refine ⟨hn, hnmax, m, hm, (fun j => (G j).indices), (fun j => (G j).affine),
    (fun j => (G j).jacobian), a, b, (fun j => (G j).center),
    (fun j i => ((G j).axes i : Fin 3 → E)), (fun j => (G j).shading),
    hamin, hab, hbmax, hδb, (fun j => (hG j).1), hmass, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨(hG j).2.2.2.2.2.1, (hG j).2.2.2.2.2.2.1⟩
  · intro j
    exact (hG j).2.2.2.2.2.2.2.1
  · intro j i hi
    exact ((G j).axes i).orthonormal
  · intro j i hi
    rw [← hbody]
    exact (hG j).2.2.2.2.2.2.2.2.1 i hi
  · intro j i hi
    rw [← hbody]
    exact (hG j).2.2.2.2.2.2.2.2.2.1 i hi
  · intro j i hi
    exact (hG j).2.2.2.2.2.2.2.2.2.2.1 i hi
  · intro j i hi
    rw [← hbody]
    exact (hG j).2.2.2.2.2.2.2.2.2.2.2.1 i hi
  · intro j i hi
    rw [← hbody]
    exact (hG j).2.2.2.2.2.2.2.2.2.2.2.2.1 i hi
  · intro j i hi p hp r hra hr1
    rw [← hbody]
    exact (hG j).2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi p hp r (by rwa [ha]) hr1
  · intro j p hp
    obtain ⟨i, hi, i', hi', hpi, hpi', hangle⟩ := (hG j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp
    exact ⟨i, i', hi, hi', hpi, hpi', by simpa only [ha, hb] using hangle⟩
  · intro j ν s r hν hr
    have hslab := (hG j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ν s r hν hr
    simpa only [hbody, slab, innerSL_apply_apply] using hslab
  · intro j k hjk
    exact hdisj hjk

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
