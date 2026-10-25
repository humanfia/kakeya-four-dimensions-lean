-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Restriction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Chains
import Submission.WZ.Obl.wz_tower_balanced_refinement.Tower

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- A local tower survives any nonempty injective selection of its bottom family. -/
theorem Tower.restrict {d L g : ℝ} {B n m : ℕ} {x v : Fin n → Space}
    (h : Tower false d L g B n x v) (hn : 0 < n) (hm : 0 < m)
    (e : Fin m → Fin n) (he : Function.Injective e) :
    Tower false d L g B m (x ∘ e) (v ∘ e) := by
  classical
  obtain ⟨J, hJ, hJB, r, N, y, w, f, hr0, hrJ, hN0, ⟨u, hu⟩, hw, hedge, hcount⟩ := h
  have hNpos : ∀ j, j ≤ J → 0 < N j := by
    intro j hj
    let i := WangZahlLot.Obl.wz_tower_balanced_refinement.ancestor f hj (u ⟨0, hn⟩)
    exact (Nat.zero_le i.val).trans_lt i.isLt
  let layer : Fin (J + 1) → Layer := fun j => {
    radius := r j
    card := N j
    card_pos := hNpos j (Nat.le_of_lt_succ j.isLt)
    position := y j
    direction := w j
    unit := hw j (Nat.le_of_lt_succ j.isLt) }
  have hlink : ∀ j : Fin J, LocalEdge (d ^ g) L (layer j.castSucc) (layer j.succ) := by
    intro j
    exact ⟨(hedge j j.isLt).1, (hedge j j.isLt).2.1, (hedge j j.isLt).2.2.1,
      f j, (hedge j j.isLt).2.2.2, hcount j j.isLt⟩
  have hchain := Chain.of_fin_sequence J layer hlink
  let a : Fin m → Fin (layer (Fin.last J)).card := u ∘ e
  have ha : Function.Injective a := u.injective.comp he
  have hchain' := hchain.restrict_bottom hJ hm a ha
  have htower := tower_of_chain
    (show (layer 0).radius = 1 from hr0)
    (show (layer 0).card = 1 from hN0)
    (show ((layer (Fin.last J)).select hm a).radius = d from hrJ)
    hJ hJB hchain'
  have hx : ((layer (Fin.last J)).select hm a).position = x ∘ e := by
    funext i
    exact (hu (e i)).1
  have hv : ((layer (Fin.last J)).select hm a).direction = v ∘ e := by
    funext i
    exact (hu (e i)).2
  change Tower false d L g B m ((layer (Fin.last J)).select hm a).position
    ((layer (Fin.last J)).select hm a).direction at htower
  rwa [hx, hv] at htower

end WangZahlLot.Obl.wz_multiscale_finite_tower
