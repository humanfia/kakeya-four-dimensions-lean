-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CellEnergyCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.PaletteCaps

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
  {tb : ℕ → E2 × E2 → E2 × E2}

/-- The full coarse class/cell energy is bounded by the reflected point
and angular counts of the actual configuration. -/
theorem HighConfig.cell_energy_count
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) {h a : ℕ} (hha : h ≤ a) (han : a ≤ n)
    (hRsmall : palScale r n a ≤ 1 / 8)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) :
    (∑ j ∈ S.image (fun q => tb a (cls q)),
      ∑ c ∈ (S.image Prod.fst).image (cellOf (palScale r n h)),
        ((Columns.cellPins S (fun q => tb a (cls q)) (S.image Prod.fst)
          (cellOf (palScale r n h)) j c).card : ℝ) ^ 2) ≤
      4829760000000 * (palBase r n) ^ (2 : ℕ) * r ^ (-4 * ε) *
        ((S.image Prod.fst).card : ℝ) ^ (2 : ℕ) *
        cellCount (bushOf S p₀) (palScale r n a) *
        ∑ i ∈ Finset.Icc h a,
          1 / ((cellCount (S.image Prod.fst) (palScale r n i) : ℝ) *
            cellCount (bushOf S p₀) (palScale r n (a - i))) := by
  have hr := H.fail.r_pos
  have hR := palScale_pos (n := n) hr a
  have hK := Real.rpow_pos_of_pos hr (-ε)
  let A (i : ℕ) : ℝ := cellCount (bushOf S p₀) (palScale r n i)
  let N (i : ℕ) : ℝ := cellCount (S.image Prod.fst) (palScale r n i)
  let Nb : ℝ := (bushOf S p₀).card
  let Np : ℝ := (S.image Prod.fst).card
  let m := Nb / (67080 * r ^ (-ε) * A a)
  let V (i : ℕ) := 1000000 * (palBase r n) ^ (2 : ℕ) * r ^ (-ε) * Nb / A (a - i)
  let M (i : ℕ) := 36 * r ^ (-2 * ε) * Np / N i
  have hA : ∀ i, 0 < A i := fun i =>
    Nat.cast_pos.mpr (cellCount_pos (H.bush_nonempty hp₀) _)
  have hNb : 0 < Nb := Nat.cast_pos.mpr (H.bush_nonempty hp₀).card_pos
  have hAa := hA a
  have hm : 0 < m := by dsimp [m]; positivity
  have henergy := Columns.coarse_cell_energy_le_palette
    (r := r) (R := 2 * palScale r n a) (m := m)
    ((r_le_palScale hr hr1 hn han).trans (by linarith)) (by positivity) (by linarith) hm
    S (S.image (fun q => tb a (cls q))) (fun q => tb a (cls q))
    (S.image Prod.fst) (cellOf (palScale r n h)) (fun i => 2 * palScale r n i) M V hha
    (fun q hq => (H.failS.D_mem q hq).2)
    (by
      intro q hq
      have hg := H.coarse_class_geo hr1 hn han hq
      exact ⟨hg.1.trans (by linarith), hg.2⟩)
    H.failS.P_norm (fun _ _ _ _ heq => dist_le_of_cellOf_eq (palScale_pos hr h) heq)
    (fun i _ => by dsimp [V]; positivity)
    (by
      intro p hp i hi
      have hh := H.point_ball_count ((Finset.mem_Icc.mp hi).2.trans han) p
      convert hh using 1
      congr 2
      ext q
      simp only [Finset.mem_filter, dist_comm])
    (by
      intro p hp i hi u hu
      exact H.reflected_cap_count hr1 hn (Finset.mem_Icc.mp hi).2 han hp₀ p u)
    (by
      intro p hp j hj hpj
      have hh := Columns.coarse_pin_class_min hR hRsmall hK
        (fun j hj => H.coarse_classes_norm han hj)
        (fun _ hj _ hj' hne => H.coarse_classes_sep han hj hj' hne)
        (fun q hq => Finset.mem_image_of_mem _ hq)
        (fun q hq => (H.failS.D_mem q hq).2)
        (fun q hq => H.coarse_class_geo hr1 hn han hq)
        (H.bal_pin_tube a han) p₀ (H.failS.P_norm p₀ hp₀) (H.bush_nonempty hp₀) hpj
      convert hh using 1 <;> rfl)
  have hK2 : r ^ (-ε) * r ^ (-ε) = r ^ (-2 * ε) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hK4 : r ^ (-2 * ε) * r ^ (-2 * ε) = r ^ (-4 * ε) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hVratio (i : ℕ) : 2 * V i / m =
      134160000000 * (palBase r n) ^ (2 : ℕ) * r ^ (-2 * ε) * A a / A (a - i) := by
    dsimp [V, m]
    rw [← hK2]
    field_simp
    ring
  apply henergy.trans_eq
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hVratio]
  dsimp only [M, Np, N, A]
  rw [← hK4]
  ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
