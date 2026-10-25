-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.EnergyWeights.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.EnergyGeometry
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.TubeWeights

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
  {tb : ℕ → E2 × E2 → E2 × E2}

/-- The actual coarse representative family lies in the separated family
chosen at that palette scale. -/
theorem HighConfig.coarse_classes_subset
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {a : ℕ} (ha : a ≤ n) :
    S.image (fun q => tb a (cls q)) ⊆ J₁ a := by
  intro j hj
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
  exact H.tube_mem a ha (cls q) (H.cls_mem q (H.sub hq))

theorem HighConfig.coarse_classes_norm
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {a : ℕ} (ha : a ≤ n)
    {j : E2 × E2} (hj : j ∈ S.image (fun q => tb a (cls q))) :
    ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1 := by
  have hjD := H.lines_sub (H.tubes_sub a (H.coarse_classes_subset ha hj))
  exact ⟨H.fail.P_norm j.1 (H.fail.D_mem j hjD).1, (H.fail.D_mem j hjD).2⟩

theorem HighConfig.coarse_classes_sep
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {a : ℕ} (ha : a ≤ n)
    {j j' : E2 × E2} (hj : j ∈ S.image (fun q => tb a (cls q)))
    (hj' : j' ∈ S.image (fun q => tb a (cls q))) (hne : j ≠ j') :
    StripSep (palScale r n a) j j' :=
  H.tubes_sep a ha j (H.coarse_classes_subset ha hj) j'
    (H.coarse_classes_subset ha hj') hne

/-- Angular errors in the fine and coarse assignments add, with either
orientation allowed at each step. -/
theorem HighConfig.coarse_class_angle
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) {a : ℕ} (ha : a ≤ n)
    {q : E2 × E2} (hq : q ∈ S) :
    dist q.2 (tb a (cls q)).2 < 2 * palScale r n a ∨
      dist q.2 (-(tb a (cls q)).2) < 2 * palScale r n a := by
  have hf := (H.cls_geo q (H.sub hq)).2
  have hc := (H.tube_geo a ha (cls q) (H.cls_mem q (H.sub hq))).2
  have hrR := r_le_palScale H.fail.r_pos hr1 hn ha
  have hb : r + palScale r n a ≤ 2 * palScale r n a := by linarith
  rcases hf with hf | hf <;> rcases hc with hc | hc
  · exact Or.inl (((dist_triangle _ _ _).trans_lt (add_lt_add hf hc)).trans_le hb)
  · exact Or.inr (((dist_triangle _ _ _).trans_lt (add_lt_add hf hc)).trans_le hb)
  · exact Or.inr (((dist_triangle _ _ _).trans_lt
      (add_lt_add hf (by simpa only [dist_neg_neg] using hc))).trans_le hb)
  · exact Or.inl (((dist_triangle _ _ _).trans_lt
      (add_lt_add hf (by simpa only [dist_neg_neg, neg_neg] using
        (show dist (-(cls q).2) (-(-(tb a (cls q)).2)) < palScale r n a by
          rwa [dist_neg_neg])))).trans_le hb)

theorem HighConfig.coarse_class_geo
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) {a : ℕ} (ha : a ≤ n)
    {q : E2 × E2} (hq : q ∈ S) :
    |inner ℝ (q.1 - (tb a (cls q)).1) (tb a (cls q)).2| < 32 * palScale r n a ∧
    (dist q.2 (tb a (cls q)).2 < 2 * palScale r n a ∨
      dist q.2 (-(tb a (cls q)).2) < 2 * palScale r n a) := by
  refine ⟨?_, H.coarse_class_angle hr1 hn ha hq⟩
  have hh := H.coarse_class_incidence hr1 hn ha hq
  have hR := palScale_pos (n := n) H.fail.r_pos a
  linarith

theorem HighConfig.bush_nonempty
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) : (bushOf S p₀).Nonempty := by
  obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp₀
  refine ⟨q.2, ?_⟩
  rw [mem_bushOf, ← hqp]
  exact hq

/-- The actual incidence degree inside a larger tube is the ratio of
measured angular counts, up to the explicit balance loss. -/
theorem HighConfig.pin_tube_incidence_le
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) {h a : ℕ} (hha : h ≤ a) (han : a ≤ n)
    (hRsmall : palScale r n a ≤ 1 / 8)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) (p : E2) (t : E2 × E2) :
    ((((S.image (fun q => tb a (cls q))).filter (fun j => tb h j = t)).filter
      (fun j => p ∈ pinsOf S (fun q => tb a (cls q)) j)).card : ℝ) ≤
      8586240 * r ^ (-2 * ε) * cellCount (bushOf S p₀) (palScale r n a) /
        cellCount (bushOf S p₀) (palScale r n h) := by
  have hr := H.fail.r_pos
  have hhn := hha.trans han
  have hh := Columns.coarse_pin_tube_incidence_le (palScale_pos hr a) hRsmall
    (palScale_antitone hr hr1 hn hha) (Real.rpow_pos_of_pos hr (-ε))
    (fun j hj => H.coarse_classes_norm han hj)
    (fun _ hj _ hj' hne => H.coarse_classes_sep han hj hj' hne)
    (fun q hq => Finset.mem_image_of_mem _ hq)
    (fun q hq => (H.failS.D_mem q hq).2)
    (fun q hq => H.coarse_class_geo hr1 hn han hq)
    (fun j hj => (H.tube_geo h hhn j (H.tubes_sub a (H.coarse_classes_subset han hj))).2)
    (H.bal_pin_tube a han) (H.bal_pin_arc h hhn)
    p₀ (H.failS.P_norm p₀ hp₀) (H.bush_nonempty hp₀) p t
  have heq : (r ^ (-ε)) ^ (2 : ℕ) = r ^ (-2 * ε) := by
    rw [← Real.rpow_mul_natCast hr.le]
    congr 1
    norm_num
    ring
  rw [heq] at hh
  convert hh <;> rfl

/-- The cell weight in the cubic incidence energy, now with every input
supplied by the concrete regularized configuration. -/
theorem HighConfig.cell_tube_incidence_le
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) {h a : ℕ} (hha : h ≤ a) (han : a ≤ n)
    (hRsmall : palScale r n a ≤ 1 / 8)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) (c : ℤ × ℤ) (t : E2 × E2) :
    (∑ j ∈ (S.image (fun q => tb a (cls q))).filter (fun j => tb h j = t),
        ((Columns.cellPins S (fun q => tb a (cls q)) (S.image Prod.fst)
          (cellOf (palScale r n h)) j c).card : ℝ)) ≤
      8586240 * r ^ (-4 * ε) * (S.image Prod.fst).card *
        cellCount (bushOf S p₀) (palScale r n a) /
        (cellCount (S.image Prod.fst) (palScale r n h) *
          cellCount (bushOf S p₀) (palScale r n h)) := by
  have hr := H.fail.r_pos
  have hh := Columns.cell_incidence_mass_le S
    ((S.image (fun q => tb a (cls q))).filter (fun j => tb h j = t))
    (fun q => tb a (cls q)) (S.image Prod.fst) (cellOf (palScale r n h)) c
    (by positivity : 0 ≤ 8586240 * r ^ (-2 * ε) *
      cellCount (bushOf S p₀) (palScale r n a) / cellCount (bushOf S p₀) (palScale r n h))
    (Columns.balanced_cell_fiber_le (S.image Prod.fst) (cellOf (palScale r n h))
      (Real.rpow_nonneg hr.le _) H.failS.P_ne (H.pin_cell_balanced (hha.trans han)) c)
    (fun p _ => H.pin_tube_incidence_le hr1 hn hha han hRsmall hp₀ p t)
  have heq : r ^ (-2 * ε) * r ^ (-2 * ε) = r ^ (-4 * ε) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  convert hh using 1
  dsimp only [cellCount]
  rw [← heq]
  ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
