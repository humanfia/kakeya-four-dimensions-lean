-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WindowTwoEnded.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/WindowTwoEnded.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseAObjects
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TwoEndedColumns
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.GridCounts

/-!
# Two-ended `δ`-lines at a window

For a `HighConfig` at the window `(a, h)` and a `δ`-line `j` (`δ = palScale a`):

* `deltaLine_frostman`: the labels of `j` (`tb a (cls q) = j`) are `(1 - s)`-Frostman along it,
  `#{q : dist q.1 q₀.1 ≤ R} ≤ r^-κ (3 R)^(1-s) #labels`, summing `line_frostman` over the fine
  classes of `j`;
* `frame_norm_le`: `‖u‖ ≤ |⟨u, v⟩| + |⟨u, perp v⟩|` for a unit `v`;
* `window_pins_close`: two labels of a line of the coarse tube `T` whose columns differ by at
  most `D` have pins within `2 D + 4 w + 108 δ`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

attribute [local instance 10] Classical.propDecidable

noncomputable section

/-- **The labels of a `δ`-line are `(1 - s)`-Frostman along it.** -/
theorem deltaLine_frostman {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2}
    {D S J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
    {tb : ℕ → E2 × E2 → E2 × E2}
    (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) (a : ℕ) (j : E2 × E2)
    (q₀ : E2 × E2) {R : ℝ} (hR : r ≤ R) :
    (((S.filter (fun q => tb a (cls q) = j)).filter (fun q => dist q.1 q₀.1 ≤ R)).card : ℝ) ≤
      r ^ (-κ) * (3 * R) ^ (1 - s) * (S.filter (fun q => tb a (cls q) = j)).card := by
  classical
  set Lj := S.filter (fun q => tb a (cls q) = j) with hLj
  have hr0 : 0 < r := hC.fail.r_pos
  have hR0 : 0 < R := lt_of_lt_of_le hr0 hR
  set W := r ^ (-κ) * (3 * R) ^ (1 - s) with hW
  have hW0 : 0 ≤ W := by positivity
  -- fibrewise over the fine classes
  have hcls_full : ∀ ℓ ∈ Lj.image cls, S.filter (fun q => cls q = ℓ) = Lj.filter (fun q => cls q = ℓ) := by
    intro ℓ hℓ
    obtain ⟨q₁, hq₁, rfl⟩ := Finset.mem_image.mp hℓ
    ext q
    simp only [hLj, Finset.mem_filter]
    constructor
    · rintro ⟨hqS, hqc⟩
      exact ⟨⟨hqS, by rw [hqc]; exact (Finset.mem_filter.mp hq₁).2⟩, hqc⟩
    · rintro ⟨⟨hqS, -⟩, hqc⟩
      exact ⟨hqS, hqc⟩
  have hsum : ((Lj.filter (fun q => dist q.1 q₀.1 ≤ R)).card : ℝ) ≤
      ∑ ℓ ∈ Lj.image cls, W * ((Lj.filter (fun q => cls q = ℓ)).card : ℝ) := by
    apply cls_card_le_sum' (g := cls) (fun q hq => Finset.mem_image_of_mem cls (Finset.mem_filter.mp hq).1)
    intro ℓ hℓ
    rcases ((Lj.filter (fun q => dist q.1 q₀.1 ≤ R)).filter (fun q => cls q = ℓ)).eq_empty_or_nonempty
      with h0 | ⟨q₁, hq₁⟩
    · rw [h0, Finset.card_empty, Nat.cast_zero]; positivity
    obtain ⟨hq₁a, hq₁c⟩ := Finset.mem_filter.mp hq₁
    obtain ⟨hq₁L, hq₁d⟩ := Finset.mem_filter.mp hq₁a
    have hq₁S : q₁ ∈ S := (Finset.mem_filter.mp hq₁L).1
    have hsub : (Lj.filter (fun q => dist q.1 q₀.1 ≤ R)).filter (fun q => cls q = ℓ) ⊆
        (S.filter (fun q' => cls q' = cls q₁)).filter (fun q' => dist q'.1 q₁.1 < 3 * R) := by
      intro q hq
      obtain ⟨hqa, hqc⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqL, hqd⟩ := Finset.mem_filter.mp hqa
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqL).1,
        hqc.trans hq₁c.symm⟩, ?_⟩
      calc dist q.1 q₁.1 ≤ dist q.1 q₀.1 + dist q₀.1 q₁.1 := dist_triangle _ _ _
        _ ≤ R + R := by rw [dist_comm q₀.1]; linarith
        _ < 3 * R := by linarith
    have h1 := hC.line_frostman q₁ hq₁S (3 * R) (by linarith)
    rw [hq₁c, hcls_full ℓ hℓ] at h1
    have h2 := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
    rw [hq₁c, hcls_full ℓ hℓ] at h2
    exact h2.trans h1
  rw [← Finset.mul_sum] at hsum
  have hfib : ∑ ℓ ∈ Lj.image cls, ((Lj.filter (fun q => cls q = ℓ)).card : ℝ) = Lj.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := cls) (s := Lj) (t := Lj.image cls)
      (fun q hq => Finset.mem_image_of_mem cls hq)]
    push_cast; rfl
  rw [hfib] at hsum
  exact hsum

/-- The norm in an orthonormal frame. -/
theorem frame_norm_le {v : Plane} (hv : ‖v‖ = 1) (u : Plane) :
    ‖u‖ ≤ |inner ℝ u v| + |inner ℝ u (perp v)| := by
  have h := inner_frame hv u u
  have hsq : ‖u‖ ^ 2 = inner ℝ u (perp v) ^ 2 + inner ℝ u v ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, h]; ring
  have h0 : 0 ≤ |inner ℝ u v| + |inner ℝ u (perp v)| := by positivity
  have hle : ‖u‖ ^ 2 ≤ (|inner ℝ u v| + |inner ℝ u (perp v)|) ^ 2 := by
    rw [hsq]
    nlinarith [sq_abs (inner ℝ u v), sq_abs (inner ℝ u (perp v)),
      mul_nonneg (abs_nonneg (inner ℝ u v)) (abs_nonneg (inner ℝ u (perp v)))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg u) h0 two_ne_zero).mp hle

/-- `palScale` of a difference of indices is the ratio of the scales. -/
theorem palScale_sub {r : ℝ} (hr : 0 < r) (n : ℕ) {a h : ℕ} (hha : h ≤ a) :
    palScale r n (a - h) = palScale r n a / palScale r n h := by
  unfold palScale
  have hB : 0 < palBase r n := Real.rpow_pos_of_pos hr _
  rw [← Real.rpow_sub hB, Nat.cast_sub hha]
  ring_nf

/-- **Pins of a window line with close columns are close.** -/
theorem window_pins_close {T j q q' : E2 × E2} {ρ δ w D : ℝ} (hT2 : ‖T.2‖ = 1)
    (hρ12 : ρ ≤ 1 / 2) (hw : 0 < w)
    (hang : dist j.2 T.2 ≤ ρ ∨ dist j.2 (-T.2) ≤ ρ)
    (hq : |inner ℝ (q.1 - j.1) j.2| ≤ 27 * δ) (hq' : |inner ℝ (q'.1 - j.1) j.2| ≤ 27 * δ)
    (hcol : |tubeCol (tubeAxis T) w q.1 - tubeCol (tubeAxis T) w q'.1| ≤ D) :
    dist q.1 q'.1 ≤ 2 * D + (4 * w + 108 * δ) := by
  set v := tubeAxis T with hv
  have hv1 : ‖v‖ = 1 := tubeAxis_norm hT2
  set u := q.1 - q'.1 with hu
  -- along the axis
  have halong : |inner ℝ u v| ≤ D + 2 * w := by
    have h1 := tubeCol_close v hw q.1
    have h2 := tubeCol_close v hw q'.1
    simp only [pointChart] at h1 h2
    have he : inner ℝ u v = inner ℝ q.1 v - inner ℝ q'.1 v := by rw [hu, inner_sub_left]
    rw [he]
    calc |inner ℝ q.1 v - inner ℝ q'.1 v|
        = |(inner ℝ q.1 v - tubeCol v w q.1) + (tubeCol v w q.1 - tubeCol v w q'.1) +
            (tubeCol v w q'.1 - inner ℝ q'.1 v)| := by ring_nf
      _ ≤ |inner ℝ q.1 v - tubeCol v w q.1| + |tubeCol v w q.1 - tubeCol v w q'.1| +
            |tubeCol v w q'.1 - inner ℝ q'.1 v| := abs_add_three _ _ _
      _ ≤ w + D + w := by
          rw [abs_sub_comm (inner ℝ q.1 v)]
          linarith
      _ = D + 2 * w := by ring
  -- across the line
  have hacross : |inner ℝ u j.2| ≤ 54 * δ := by
    have he : inner ℝ u j.2 = inner ℝ (q.1 - j.1) j.2 - inner ℝ (q'.1 - j.1) j.2 := by
      rw [hu, ← inner_sub_left]; congr 1; abel
    rw [he]
    calc |inner ℝ (q.1 - j.1) j.2 - inner ℝ (q'.1 - j.1) j.2|
        ≤ |inner ℝ (q.1 - j.1) j.2| + |inner ℝ (q'.1 - j.1) j.2| := abs_sub _ _
      _ ≤ 54 * δ := by linarith
  -- across the tube
  have hperp : |inner ℝ u (perp v)| ≤ 54 * δ + ρ * ‖u‖ := by
    rw [perp_tubeAxis]
    rcases hang with h1 | h1
    · have he : inner ℝ u T.2 = inner ℝ u j.2 - inner ℝ u (j.2 - T.2) := by
        rw [inner_sub_right]; ring
      rw [he]
      have h2 : |inner ℝ u (j.2 - T.2)| ≤ ‖u‖ * ρ := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [show ‖j.2 - T.2‖ = dist j.2 T.2 from (dist_eq_norm _ _).symm]
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg u)
      calc |inner ℝ u j.2 - inner ℝ u (j.2 - T.2)|
          ≤ |inner ℝ u j.2| + |inner ℝ u (j.2 - T.2)| := abs_sub _ _
        _ ≤ 54 * δ + ρ * ‖u‖ := by linarith
    · have he : inner ℝ u T.2 = -(inner ℝ u j.2 - inner ℝ u (j.2 - -T.2)) := by
        rw [inner_sub_right, inner_neg_right]; ring
      rw [he, abs_neg]
      have h2 : |inner ℝ u (j.2 - -T.2)| ≤ ‖u‖ * ρ := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [show ‖j.2 - -T.2‖ = dist j.2 (-T.2) from (dist_eq_norm _ _).symm]
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg u)
      calc |inner ℝ u j.2 - inner ℝ u (j.2 - -T.2)|
          ≤ |inner ℝ u j.2| + |inner ℝ u (j.2 - -T.2)| := abs_sub _ _
        _ ≤ 54 * δ + ρ * ‖u‖ := by linarith
  have hn := frame_norm_le hv1 u
  rw [dist_eq_norm]
  have hρu : ρ * ‖u‖ ≤ ‖u‖ / 2 := by nlinarith [norm_nonneg u]
  nlinarith [norm_nonneg u]

/-- The constant of `window_two_ended`. -/
def twoEndedConst (r κ ε : ℝ) : ℝ := 11 * (3 * r ^ (-κ) * 72 * (r ^ (-ε)) ^ 2 * 13225)

/-- **The `δ`-lines of a window tube are two-ended in column form** (the hypothesis `htwo` of
`caseA_window_two_ends_false`). -/
theorem window_two_ended {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2}
    {D S J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
    {tb : ℕ → E2 × E2 → E2 × E2}
    (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {a h : ℕ} (ha : a ≤ n) (hh : h ≤ n)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hrδ : r ≤ palScale r n a) (hρ12 : palScale r n h ≤ 1 / 2)
    (hδρ : 2 * palScale r n a ≤ palScale r n h) (hρδ : palScale r n h ^ 2 ≤ palScale r n a)
    (T : E2 × E2) (hT2 : ‖T.2‖ = 1) :
    ∀ j ∈ windowLines S cls tb a h T, ∀ z ρ' : ℝ,
      WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.tubeTol (27 * palScale r n a) (16 * palScale r n h) (palScale r n h / 2) ≤ ρ' →
      ((((windowPins S cls tb a h T).image
          (tubeCol (tubeAxis T) (palScale r n h / 2))).filter
        (fun y => (∃ x ∈ windowPins S cls tb a h T, windowPin S cls tb a h T j x ∧
          tubeCol (tubeAxis T) (palScale r n h / 2) x = y) ∧
          |y - z| ≤ ρ')).card : ℝ) ≤
      twoEndedConst r κ ε * ρ' ^ (1 - s) *
        ((((windowPins S cls tb a h T).image
          (tubeCol (tubeAxis T) (palScale r n h / 2))).filter
        (fun y => ∃ x ∈ windowPins S cls tb a h T, windowPin S cls tb a h T j x ∧
          tubeCol (tubeAxis T) (palScale r n h / 2) x = y)).card :
          ℝ) := by
  intro j hj z ρ' hρ'
  set δ := palScale r n a with hδ
  set ρ := palScale r n h with hρ
  set v := tubeAxis T with hv
  set w := ρ / 2 with hw
  set col := tubeCol v w with hcol
  set U := windowPins S cls tb a h T with hU
  set Lj := S.filter (fun q => tb a (cls q) = j) with hLj
  have hr0 : 0 < r := hC.fail.r_pos
  have hδ0 : 0 < δ := lt_of_lt_of_le hr0 hrδ
  have hρ0 : 0 < ρ := by
    rw [hρ]; unfold palScale; exact Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hr0 _) _
  have hw0 : 0 < w := by positivity
  set c := ρ with hc
  have hc0 : 0 < c := hρ0
  have hwc : w = 1 / 2 * c := by rw [hw]; ring
  have hδc : δ ≤ c / 2 := by linarith
  have hcρ' : c ≤ ρ' := by
    rw [tubeTol_half hρ0] at hρ'
    have h1 : c ≤ (108 * δ + 8 * ρ ^ 2) / (64 * ρ) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  -- facts about the window
  obtain ⟨hgeoJ, -, hpinW, -⟩ := window_geometry hC ha hh hrδ T
  have hjT : tb h j = T := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact (mem_windowLabels.mp hq).2
  obtain ⟨-, -, -, hang⟩ := hgeoJ j hj
  -- labels of `j` are labels of the window
  have hLjW : ∀ q ∈ Lj, q ∈ windowLabels S cls tb a h T := by
    intro q hq
    obtain ⟨hqS, hqj⟩ := Finset.mem_filter.mp hq
    exact mem_windowLabels.mpr ⟨hqS, by rw [hqj, hjT]⟩
  have hLjpin : ∀ q ∈ Lj, |inner ℝ (q.1 - j.1) j.2| ≤ 27 * δ := by
    intro q hq
    have hqW := hLjW q hq
    exact hpinW j hj q.1 (Finset.mem_image_of_mem _ hqW)
      ⟨q, hqW, rfl, (Finset.mem_filter.mp hq).2⟩
  -- the columns of `j` among the window pins are the columns of its labels
  have hcols : ((U.image col).filter (fun y => ∃ x ∈ U, windowPin S cls tb a h T j x ∧
      col x = y)) = Lj.image (fun q => col q.1) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, x, -, ⟨q, hqW, rfl, hqj⟩, rfl⟩
      exact ⟨q, Finset.mem_filter.mpr ⟨(mem_windowLabels.mp hqW).1, hqj⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      have hqW := hLjW q hq
      exact ⟨⟨q.1, Finset.mem_image_of_mem _ hqW, rfl⟩, q.1, Finset.mem_image_of_mem _ hqW,
        ⟨q, hqW, rfl, (Finset.mem_filter.mp hq).2⟩, rfl⟩
  have hcolsz : ((U.image col).filter (fun y => (∃ x ∈ U, windowPin S cls tb a h T j x ∧
      col x = y) ∧ |y - z| ≤ ρ')) = (Lj.image (fun q => col q.1)).filter (fun y => |y - z| ≤ ρ') := by
    rw [← hcols]
    ext y
    simp only [Finset.mem_filter]
    tauto
  rw [hcols, hcolsz]
  set K := r ^ (-ε) with hK
  have hK0 : 0 < K := Real.rpow_pos_of_pos hr0 _
  -- a label of `j`
  obtain ⟨q₀, hq₀W, hq₀j⟩ : ∃ q₀ ∈ windowLabels S cls tb a h T, tb a (cls q₀) = j := by
    obtain ⟨q, hq, hqj⟩ := Finset.mem_image.mp hj
    exact ⟨q, hq, hqj⟩
  have hq₀L : q₀ ∈ Lj := Finset.mem_filter.mpr ⟨(mem_windowLabels.mp hq₀W).1, hq₀j⟩
  -- fibres of the (cell, line) map on `Lj`
  have hbal := hC.bal_cell_tube h hh a ha
  have hfib : ∀ q ∈ Lj, Lj.filter (fun q' => cellOf c q'.1 = cellOf c q.1) =
      WangZahlLot.Obl.wz_tower_balanced_refinement.leafFiber S
        (fun q => (cellOf (palScale r n h) q.1, tb a (cls q))) q := by
    intro q hq
    have hqj := (Finset.mem_filter.mp hq).2
    ext q'
    simp only [WangZahlLot.Obl.wz_tower_balanced_refinement.leafFiber, hLj, Finset.mem_filter,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hq'S, hq'j⟩, hcell⟩; exact ⟨hq'S, hcell, hq'j.trans hqj.symm⟩
    · rintro ⟨hq'S, hcell, hq'j⟩; exact ⟨⟨hq'S, hq'j.trans hqj⟩, hcell⟩
  set Nst := ((Lj.filter (fun q' => cellOf c q'.1 = cellOf c q₀.1)).card : ℝ) with hNst
  have hNst0 : 0 < Nst := by
    have hmem : q₀ ∈ Lj.filter (fun q' => cellOf c q'.1 = cellOf c q₀.1) :=
      Finset.mem_filter.mpr ⟨hq₀L, rfl⟩
    rw [hNst]; exact_mod_cast Finset.card_pos.mpr ⟨q₀, hmem⟩
  have hlo : ∀ q ∈ Lj, Nst / K ≤ ((Lj.filter (fun q' => cellOf c q'.1 = cellOf c q.1)).card : ℝ) := by
    intro q hq
    have h1 := hbal q₀ (Finset.mem_filter.mp hq₀L).1 q (Finset.mem_filter.mp hq).1
    rw [← hfib q₀ hq₀L, ← hfib q hq] at h1
    rw [div_le_iff₀ hK0]; linarith [h1]
  have hhi : ∀ q ∈ Lj, ((Lj.filter (fun q' => cellOf c q'.1 = cellOf c q.1)).card : ℝ) ≤ K * Nst := by
    intro q hq
    have h1 := hbal q (Finset.mem_filter.mp hq).1 q₀ (Finset.mem_filter.mp hq₀L).1
    rw [← hfib q₀ hq₀L, ← hfib q hq] at h1
    exact h1
  -- pins of `j` with close columns are close
  have hcl : ∀ q ∈ Lj, ∀ q' ∈ Lj, ∀ D : ℝ, |col q.1 - col q'.1| ≤ D →
      dist q.1 q'.1 ≤ 2 * D + (4 * w + 108 * δ) := by
    intro q hq q' hq' D hD
    exact window_pins_close hT2 hρ12 hw0 hang (hLjpin q hq) (hLjpin q' hq') hD
  -- a grid cell meets few columns
  have hcells_col : ∀ q ∈ Lj, (((Lj.filter (fun q' => cellOf c q'.1 = cellOf c q.1)).image
      (fun q' => col q'.1)).card : ℝ) ≤ 2 * (2 * c + w) / w + 1 := by
    intro q _
    have himg : (Lj.filter (fun q' => cellOf c q'.1 = cellOf c q.1)).image (fun q' => col q'.1) =
        ((Lj.filter (fun q' => cellOf c q'.1 = cellOf c q.1)).image
          (fun q' => inner ℝ q'.1 v)).image (roundZero w) := by
      rw [Finset.image_image]; rfl
    rw [himg]
    apply roundZero_image_card_le hw0 (by positivity) (t₀ := inner ℝ q.1 v)
    intro t ht
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp ht
    have hd := dist_le_of_cellOf_eq hc0 (Finset.mem_filter.mp hq').2
    have hv1 : ‖v‖ = 1 := tubeAxis_norm hT2
    have h1 : |inner ℝ (q'.1 - q.1) v| ≤ ‖q'.1 - q.1‖ := by
      have := abs_real_inner_le_norm (q'.1 - q.1) v
      rwa [hv1, mul_one] at this
    rw [← inner_sub_left]
    rw [← dist_eq_norm] at h1
    linarith
  -- a column meets few grid cells
  have hcol_cells : ∀ q ∈ Lj, (((Lj.filter (fun q' => col q'.1 = col q.1)).image
      (fun q' => cellOf c q'.1)).card : ℝ) ≤ (2 * ((4 * w + 108 * δ) + c) / c + 1) ^ 2 := by
    intro q hq
    have himg : (Lj.filter (fun q' => col q'.1 = col q.1)).image (fun q' => cellOf c q'.1) =
        ((Lj.filter (fun q' => col q'.1 = col q.1)).image Prod.fst).image (cellOf c) := by
      rw [Finset.image_image]; rfl
    rw [himg]
    apply cellOf_image_card_le hc0 (by positivity) q.1
    intro x hx
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hq'L, hq'c⟩ := Finset.mem_filter.mp hq'
    have h := hcl q' hq'L q hq 0 (by rw [hq'c, sub_self, abs_zero])
    linarith
  -- labels in one cell have close columns
  have hext : ∀ q ∈ Lj, ∀ q' ∈ Lj, cellOf c q.1 = cellOf c q'.1 →
      |col q.1 - col q'.1| ≤ 2 * c + 2 * w := by
    intro q _ q' _ hcell
    have hd := dist_le_of_cellOf_eq hc0 hcell
    have hv1 : ‖v‖ = 1 := tubeAxis_norm hT2
    have h1 := tubeCol_close v hw0 q.1
    have h2 := tubeCol_close v hw0 q'.1
    simp only [pointChart] at h1 h2
    have h3 : |inner ℝ q.1 v - inner ℝ q'.1 v| ≤ 2 * c := by
      rw [← inner_sub_left]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [hv1, mul_one, ← dist_eq_norm]; exact hd
    calc |col q.1 - col q'.1|
        = |(tubeCol v w q.1 - inner ℝ q.1 v) + (inner ℝ q.1 v - inner ℝ q'.1 v) +
            (inner ℝ q'.1 v - tubeCol v w q'.1)| := by rw [hcol]; ring_nf
      _ ≤ |tubeCol v w q.1 - inner ℝ q.1 v| + |inner ℝ q.1 v - inner ℝ q'.1 v| +
            |inner ℝ q'.1 v - tubeCol v w q'.1| := abs_add_three _ _ _
      _ ≤ w + 2 * c + w := by rw [abs_sub_comm (inner ℝ q'.1 v)]; linarith
      _ = 2 * c + 2 * w := by ring
  -- the line Frostman bound
  have hFr : ∀ q₁ ∈ Lj, ∀ R : ℝ, r ≤ R →
      ((Lj.filter (fun q => dist q.1 q₁.1 ≤ R)).card : ℝ) ≤
        (r ^ (-κ) * 3 ^ (1 - s)) * R ^ (1 - s) * Lj.card := by
    intro q₁ _ R hR
    have h := deltaLine_frostman hC a j q₁ hR
    have hR0 : 0 ≤ R := hr0.le.trans hR
    rw [Real.mul_rpow (by norm_num) hR0] at h
    linarith
  have hmain := columns_two_ended Lj col (cellOf c) (z := z) (ρ := ρ') (R₀ := r)
    (α := 2) (α' := 4 * w + 108 * δ) (Nlo := Nst / K) (Nhi := K * Nst)
    (B := r ^ (-κ) * 3 ^ (1 - s)) (β := 1 - s)
    (A₁ := 2 * (2 * c + w) / w + 1) (A₂ := (2 * ((4 * w + 108 * δ) + c) / c + 1) ^ 2)
    (E := 2 * c + 2 * w) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) hr0.le (by nlinarith) hFr hcl hlo hhi hcells_col hcol_cells hext
  refine hmain.trans ?_
  -- the constants
  have hA₁ : 2 * (2 * c + w) / w + 1 ≤ 11 := by
    have he : 2 * (2 * c + 1 / 2 * c) / (1 / 2 * c) + 1 = 11 := by
      field_simp; ring
    rw [hwc, he]
  have hA₂ : (2 * ((4 * w + 108 * δ) + c) / c + 1) ^ 2 ≤ 13225 := by
    have hb : 2 * ((4 * w + 108 * δ) + c) / c + 1 ≤ 115 := by
      rw [div_add_one hc0.ne', div_le_iff₀ hc0]; rw [hwc]; linarith
    have hb0 : 0 ≤ 2 * ((4 * w + 108 * δ) + c) / c + 1 := by positivity
    nlinarith
  have hB : r ^ (-κ) * 3 ^ (1 - s) ≤ 3 * r ^ (-κ) := by
    have h3 : (3 : ℝ) ^ (1 - s) ≤ 3 := by
      calc (3 : ℝ) ^ (1 - s) ≤ 3 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 3 := Real.rpow_one 3
    have hr' := Real.rpow_nonneg hr0.le (-κ)
    calc r ^ (-κ) * 3 ^ (1 - s) ≤ r ^ (-κ) * 3 := mul_le_mul_of_nonneg_left h3 hr'
      _ = 3 * r ^ (-κ) := by ring
  have hX : (2 * (2 * (ρ' + (2 * c + 2 * w))) + (4 * w + 108 * δ)) ^ (1 - s) ≤ 72 * ρ' ^ (1 - s) := by
    have hρ'0 : 0 ≤ ρ' := hc0.le.trans hcρ'
    have hle : 2 * (2 * (ρ' + (2 * c + 2 * w))) + (4 * w + 108 * δ) ≤ 72 * ρ' := by
      rw [hwc]; linarith
    calc (2 * (2 * (ρ' + (2 * c + 2 * w))) + (4 * w + 108 * δ)) ^ (1 - s)
        ≤ (72 * ρ') ^ (1 - s) := Real.rpow_le_rpow (by positivity) hle (by linarith)
      _ = 72 ^ (1 - s) * ρ' ^ (1 - s) := Real.mul_rpow (by norm_num) hρ'0
      _ ≤ 72 * ρ' ^ (1 - s) := by
          have h72 : (72 : ℝ) ^ (1 - s) ≤ 72 := by
            calc (72 : ℝ) ^ (1 - s) ≤ 72 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 72 := Real.rpow_one 72
          exact mul_le_mul_of_nonneg_right h72 (Real.rpow_nonneg hρ'0 _)
  have hNK : K * Nst / (Nst / K) = K ^ 2 := by field_simp
  rw [hNK]
  have hcard0 : (0 : ℝ) ≤ ((Lj.image (fun q => col q.1)).card : ℝ) := Nat.cast_nonneg _
  have hρβ : 0 ≤ ρ' ^ (1 - s) := Real.rpow_nonneg (hc0.le.trans hcρ') _
  have hrκ : 0 ≤ r ^ (-κ) := Real.rpow_nonneg hr0.le _
  unfold twoEndedConst
  rw [← hK]
  have hρ'0 : 0 ≤ ρ' := hc0.le.trans hcρ'
  have hXnn : 0 ≤ (2 * (2 * (ρ' + (2 * c + 2 * w))) + (4 * w + 108 * δ)) ^ (1 - s) :=
    Real.rpow_nonneg (by linarith) _
  have hBnn : 0 ≤ r ^ (-κ) * 3 ^ (1 - s) := mul_nonneg hrκ (Real.rpow_nonneg (by norm_num) _)
  have hA₂nn : 0 ≤ (2 * ((4 * w + 108 * δ) + c) / c + 1) ^ 2 := sq_nonneg _
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hfac1 : 0 ≤ r ^ (-κ) * 3 ^ (1 - s) *
      (2 * (2 * (ρ' + (2 * c + 2 * w))) + (4 * w + 108 * δ)) ^ (1 - s) * K ^ 2 *
        (2 * ((4 * w + 108 * δ) + c) / c + 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hBnn hXnn) hK2) hA₂nn
  have hfac2 : 0 ≤ 3 * r ^ (-κ) * (72 * ρ' ^ (1 - s)) * K ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) hK2
  calc (2 * (2 * c + w) / w + 1) * (r ^ (-κ) * 3 ^ (1 - s) *
        (2 * (2 * (ρ' + (2 * c + 2 * w))) + (4 * w + 108 * δ)) ^ (1 - s) * K ^ 2 *
          (2 * ((4 * w + 108 * δ) + c) / c + 1) ^ 2) * ((Lj.image (fun q => col q.1)).card : ℝ)
      ≤ 11 * (3 * r ^ (-κ) * (72 * ρ' ^ (1 - s)) * K ^ 2 * 13225) *
          ((Lj.image (fun q => col q.1)).card : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hcard0
        apply mul_le_mul hA₁ _ hfac1 (by norm_num)
        apply mul_le_mul _ hA₂ hA₂nn hfac2
        apply mul_le_mul_of_nonneg_right _ hK2
        exact mul_le_mul hB hX hXnn (by linarith)
    _ = 11 * (3 * r ^ (-κ) * 72 * K ^ 2 * 13225) * ρ' ^ (1 - s) *
          ((Lj.image (fun q => col q.1)).card : ℝ) := by ring

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
