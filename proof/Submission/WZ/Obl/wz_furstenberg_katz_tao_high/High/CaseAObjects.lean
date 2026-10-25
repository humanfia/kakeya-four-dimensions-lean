-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CaseAObjects.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/CaseAObjects.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Leaves
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseAWindow
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CoarseWolff
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TubeUpper

/-!
# The objects of case A at a window

In a `HighConfig` at the palette window `(a, h)` (`δ = palScale a` the line resolution,
`ρ = palScale h` the tube scale), a coarse tube `T` gets

* its labels `windowLabels`: the `q ∈ S` whose composed tube `tb h (tb a (cls q))` is `T`
  (so they form whole classes of the `δ`-lines `tb a (cls q)`);
* its lines `windowLines`: the `δ`-lines `tb a (cls q)` of these labels;
* its pins `windowPins` and the pin relation `windowPin j x`: some label of `T` at `x` has the
  `δ`-line `j`.

`window_geometry` proves the geometric hypotheses of `caseA_window_false`: each line has a
unit normal, `‖j.1‖ ≤ 4`, offset `≤ 17 ρ` and angle `≤ ρ` to `T`; the lines are `StripSep δ`;
pins lie within `27 δ` of their lines; pins have norm `≤ 4`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

attribute [local instance 10] Classical.propDecidable

noncomputable section

/-- The labels of the coarse tube `T` at the window `(a, h)`. -/
def windowLabels (S : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (tb : ℕ → E2 × E2 → E2 × E2) (a h : ℕ) (T : E2 × E2) : Finset (E2 × E2) :=
  S.filter (fun q => tb h (tb a (cls q)) = T)

/-- The `δ`-lines of the coarse tube `T`. -/
def windowLines (S : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (tb : ℕ → E2 × E2 → E2 × E2) (a h : ℕ) (T : E2 × E2) : Finset (E2 × E2) :=
  (windowLabels S cls tb a h T).image (fun q => tb a (cls q))

/-- The pins of the coarse tube `T`. -/
def windowPins (S : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (tb : ℕ → E2 × E2 → E2 × E2) (a h : ℕ) (T : E2 × E2) : Finset E2 :=
  (windowLabels S cls tb a h T).image Prod.fst

/-- The pin relation of the coarse tube `T`. -/
def windowPin (S : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (tb : ℕ → E2 × E2 → E2 × E2) (a h : ℕ) (T : E2 × E2) (j : E2 × E2) (x : E2) : Prop :=
  ∃ q ∈ windowLabels S cls tb a h T, q.1 = x ∧ tb a (cls q) = j

theorem mem_windowLabels {S : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    {tb : ℕ → E2 × E2 → E2 × E2} {a h : ℕ} {T q : E2 × E2} :
    q ∈ windowLabels S cls tb a h T ↔ q ∈ S ∧ tb h (tb a (cls q)) = T := by
  unfold windowLabels; exact Finset.mem_filter

/-- **The geometry of the window objects.** -/
theorem window_geometry {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
    {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)} {tb : ℕ → E2 × E2 → E2 × E2}
    (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {a h : ℕ} (ha : a ≤ n) (hh : h ≤ n)
    (hrδ : r ≤ palScale r n a) (T : E2 × E2) :
    (∀ j ∈ windowLines S cls tb a h T, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧
      |inner ℝ (j.1 - T.1) j.2| ≤ 17 * palScale r n h ∧
      (dist j.2 T.2 ≤ palScale r n h ∨ dist j.2 (-T.2) ≤ palScale r n h)) ∧
    (∀ j ∈ windowLines S cls tb a h T, ∀ j' ∈ windowLines S cls tb a h T, j ≠ j' →
      StripSep (palScale r n a) j j') ∧
    (∀ j ∈ windowLines S cls tb a h T, ∀ x ∈ windowPins S cls tb a h T,
      windowPin S cls tb a h T j x → |inner ℝ (x - j.1) j.2| ≤ 27 * palScale r n a) ∧
    (∀ x ∈ windowPins S cls tb a h T, ‖x‖ ≤ 4) := by
  set δ := palScale r n a with hδ
  set ρ := palScale r n h with hρ
  have hr0 : 0 < r := hC.fail.r_pos
  -- norms of labels of `D`
  have hDn : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1 := fun q hq =>
    ⟨hC.fail.P_norm _ (hC.fail.D_mem q hq).1, (hC.fail.D_mem q hq).2⟩
  have hJ₀n : ∀ ℓ ∈ J₀, ‖ℓ.1‖ ≤ 4 ∧ ‖ℓ.2‖ = 1 := fun ℓ hℓ => hDn ℓ (hC.lines_sub hℓ)
  -- the lines of the window are `δ`-tubes in `J₀` whose `ρ`-tube is `T`
  have hline : ∀ j ∈ windowLines S cls tb a h T, j ∈ J₁ a ∧ j ∈ J₀ ∧ tb h j = T := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hqS, hqT⟩ := mem_windowLabels.mp hq
    have hcl : cls q ∈ J₀ := hC.cls_mem q (hC.sub hqS)
    have hj1 : tb a (cls q) ∈ J₁ a := hC.tube_mem a ha (cls q) hcl
    exact ⟨hj1, hC.tubes_sub a hj1, hqT⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨-, hj0, hjT⟩ := hline j hj
    obtain ⟨hj4, hj1⟩ := hJ₀n j hj0
    have hg := hC.tube_geo h hh j hj0
    rw [hjT] at hg
    have hT0 : T ∈ J₀ := by
      rw [← hjT]; exact hC.tubes_sub h (hC.tube_mem h hh j hj0)
    obtain ⟨hT4, -⟩ := hJ₀n T hT0
    have hv8 : ‖j.1 - T.1‖ ≤ 8 := by
      calc ‖j.1 - T.1‖ ≤ ‖j.1‖ + ‖T.1‖ := norm_sub_le _ _
        _ ≤ 8 := by linarith
    have hoff : |inner ℝ (j.1 - T.1) j.2| < 9 * ρ + 8 * ρ := by
      have h1 : |inner ℝ (j.1 - T.1) T.2| < 9 * ρ := hg.1
      exact inner_le_of_close hv8 h1 hg.2
    refine ⟨hj1, hj4, by linarith, ?_⟩
    rcases hg.2 with h2 | h2
    · exact Or.inl h2.le
    · exact Or.inr h2.le
  · intro j hj j' hj' hne
    exact hC.tubes_sep a ha j (hline j hj).1 j' (hline j' hj').1 hne
  · intro j _ x _ hpin
    obtain ⟨q, hq, rfl, rfl⟩ := hpin
    obtain ⟨hqS, -⟩ := mem_windowLabels.mp hq
    have hqD := hC.sub hqS
    have hcl : cls q ∈ J₀ := hC.cls_mem q hqD
    have hj0 : tb a (cls q) ∈ J₀ := hC.tubes_sub a (hC.tube_mem a ha (cls q) hcl)
    have hg := coarse_cls_geom (r := r) (ρ := δ) hr0.le hrδ (q := q) (ℓ := cls q)
      (j := tb a (cls q)) (hDn q hqD).1 (hJ₀n _ hcl).1 (hJ₀n _ hcl).2 (hJ₀n _ hj0).2
      (hC.cls_geo q hqD) (hC.tube_geo a ha (cls q) hcl)
    linarith [hg.1]
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    exact (hDn q (hC.sub (mem_windowLabels.mp hq).1)).1

/-- **Pin degree at the window.** With the (pin, composed tube) map balanced (ratio `K`) and at
least `Marc / K` normals in every (pin, `ρ`-arc), every pin of the coarse tube `T` lies on many
of its `δ`-lines: `Marc / (K² C) ≤ 2 r^-ε (3 δ / r)^s · #lines through x`. -/
theorem window_pin_degree {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2}
    {D S J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
    {tb : ℕ → E2 × E2 → E2 × E2}
    (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {a h : ℕ} (ha : a ≤ n) (hh : h ≤ n)
    (hrδ : r ≤ palScale r n a) (h30 : 10 * (3 * palScale r n a) ≤ palScale r n h)
    (h142 : 142 * palScale r n h ≤ 1 / 2) {K Marc : ℝ} (hK : 0 < K)
    (hbal2 : WangZahlLot.Obl.wz_tower_balanced_refinement.Balanced S
      (fun q => (q.1, tb h (tb a (cls q)))) K)
    (harc : ∀ p ∈ S.image Prod.fst, ∀ e ∈ bushOf S p,
      Marc ≤ K * ((arcNormals (palScale r n h) S p e).card : ℝ))
    (T : E2 × E2) {x : E2} (hx : x ∈ windowPins S cls tb a h T) :
    Marc / (K ^ 2 * arcTubeConst) ≤
      2 * (r ^ (-ε) * (3 * palScale r n a / r) ^ s) *
        (((windowLines S cls tb a h T).filter
          (fun j => windowPin S cls tb a h T j x)).card : ℝ) := by
  set δ := palScale r n a with hδ
  set ρ := palScale r n h with hρ
  have hr0 : 0 < r := hC.fail.r_pos
  have hδ0 : 0 < δ := lt_of_lt_of_le hr0 hrδ
  have hDn : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1 := fun q hq =>
    ⟨hC.fail.P_norm _ (hC.fail.D_mem q hq).1, (hC.fail.D_mem q hq).2⟩
  have hJ₀n : ∀ ℓ ∈ J₀, ‖ℓ.1‖ ≤ 4 ∧ ‖ℓ.2‖ = 1 := fun ℓ hℓ => hDn ℓ (hC.lines_sub hℓ)
  have hclsJ : ∀ q ∈ S, cls q ∈ J₀ := fun q hq => hC.cls_mem q (hC.sub hq)
  have hlineJ : ∀ q ∈ S, tb a (cls q) ∈ J₀ := fun q hq =>
    hC.tubes_sub a (hC.tube_mem a ha (cls q) (hclsJ q hq))
  have htubeJ : ∀ q ∈ S, tb h (tb a (cls q)) ∈ J₁ h := fun q hq =>
    hC.tube_mem h hh (tb a (cls q)) (hlineJ q hq)
  -- the composed line geometry `27 δ / 3 δ`
  have hgeo3 : ∀ q ∈ S, |inner ℝ (q.1 - (tb a (cls q)).1) (tb a (cls q)).2| < 9 * (3 * δ) ∧
      (dist q.2 (tb a (cls q)).2 < 3 * δ ∨ dist q.2 (-(tb a (cls q)).2) < 3 * δ) := by
    intro q hq
    exact coarse_cls_geom hr0.le hrδ (hDn q (hC.sub hq)).1 (hJ₀n _ (hclsJ q hq)).1
      (hJ₀n _ (hclsJ q hq)).2 (hJ₀n _ (hlineJ q hq)).2 (hC.cls_geo q (hC.sub hq))
      (hC.tube_geo a ha (cls q) (hclsJ q hq))
  obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hq₀S, hq₀T⟩ := mem_windowLabels.mp hq₀
  -- labels of the pin in the tube
  set Lx := S.filter (fun a' => a'.1 = q₀.1 ∧ tb h (tb a (cls a')) = tb h (tb a (cls q₀)))
    with hLx
  have hL : Marc / (K ^ 2 * arcTubeConst) ≤ (Lx.card : ℝ) := by
    refine pin_tube_labels_ge (r := 3 * δ) (ρ := ρ) (by positivity) h30 h142 hK
      (Q := S.image Prod.fst) (S := S) (cls := fun q => tb a (cls q)) (tb := tb h)
      (fun q hq => ⟨Finset.mem_image_of_mem _ hq, (hDn q (hC.sub hq)).2⟩)
      (fun p hp => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        exact (hDn q (hC.sub hq)).1)
      harc (fun q hq => (hJ₀n _ (hlineJ q hq)).1) hgeo3
      (fun q hq => hJ₀n _ (hC.tubes_sub h (htubeJ q hq)))
      (fun q hq => hC.tube_geo h hh (tb a (cls q)) (hlineJ q hq))
      (fun y hy z hz hne => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hz
        exact hC.tubes_sep h hh _ (htubeJ q hq) _ (htubeJ q' hq') hne)
      hbal2 hq₀S
  -- the lines through the pin
  have hsub : Lx.image (fun q => tb a (cls q)) ⊆
      (windowLines S cls tb a h T).filter (fun j => windowPin S cls tb a h T j q₀.1) := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hqS, hq1, hqT⟩ := Finset.mem_filter.mp hq
    have hqW : q ∈ windowLabels S cls tb a h T :=
      mem_windowLabels.mpr ⟨hqS, hqT.trans hq₀T⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hqW, q, hqW, hq1, rfl⟩
  -- each line holds few labels of the pin
  have hfib : ∀ j ∈ Lx.image (fun q => tb a (cls q)),
      ((Lx.filter (fun q => tb a (cls q) = j)).card : ℝ) ≤
        2 * (r ^ (-ε) * (3 * δ / r) ^ s) := by
    intro j hj
    obtain ⟨q₁, hq₁, rfl⟩ := Finset.mem_image.mp hj
    have hq₁S := (Finset.mem_filter.mp hq₁).1
    have hj1 : ‖(tb a (cls q₁)).2‖ = 1 := (hJ₀n _ (hlineJ q₁ hq₁S)).2
    have hjn : ‖-(tb a (cls q₁)).2‖ = 1 := by rw [norm_neg, hj1]
    have hp₀ : q₀.1 ∈ S.image Prod.fst := Finset.mem_image_of_mem _ hq₀S
    have hinj : Set.InjOn Prod.snd
        ((Lx.filter (fun q => tb a (cls q) = tb a (cls q₁)) : Finset (E2 × E2)) : Set (E2 × E2)) := by
      intro y hy z hz hyz
      have hy1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2.1
      have hz1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2.1
      exact Prod.ext (hy1.trans hz1.symm) hyz
    have himg : (Lx.filter (fun q => tb a (cls q) = tb a (cls q₁))).image Prod.snd ⊆
        (bushOf S q₀.1).filter (fun f => dist f (tb a (cls q₁)).2 ≤ 3 * δ) ∪
          (bushOf S q₀.1).filter (fun f => dist f (-(tb a (cls q₁))).2 ≤ 3 * δ) := by
      intro f hf
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
      obtain ⟨hqL, hqj⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqS, hq1, -⟩ := Finset.mem_filter.mp hqL
      have hb : q.2 ∈ bushOf S q₀.1 := by
        rw [mem_bushOf, ← hq1]; exact hqS
      have hg := (hgeo3 q hqS).2
      rw [hqj] at hg
      rcases hg with h1 | h1
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, h1.le⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, h1.le⟩)
    have h3 : r ≤ 3 * δ := by linarith
    have hk1 := hC.failS.D_kt q₀.1 hp₀ _ hj1 (3 * δ) h3
    have hk2 := hC.failS.D_kt q₀.1 hp₀ _ hjn (3 * δ) h3
    calc ((Lx.filter (fun q => tb a (cls q) = tb a (cls q₁))).card : ℝ)
        = (((Lx.filter (fun q => tb a (cls q) = tb a (cls q₁))).image Prod.snd).card : ℝ) := by
          rw [Finset.card_image_of_injOn hinj]
      _ ≤ (((bushOf S q₀.1).filter (fun f => dist f (tb a (cls q₁)).2 ≤ 3 * δ) ∪
          (bushOf S q₀.1).filter (fun f => dist f (-(tb a (cls q₁))).2 ≤ 3 * δ)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card himg
      _ ≤ (((bushOf S q₀.1).filter (fun f => dist f (tb a (cls q₁)).2 ≤ 3 * δ)).card : ℝ) +
          (((bushOf S q₀.1).filter (fun f => dist f (-(tb a (cls q₁))).2 ≤ 3 * δ)).card : ℝ) := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ 2 * (r ^ (-ε) * (3 * δ / r) ^ s) := by
          refine (add_le_add hk1 hk2).trans (le_of_eq (by ring))
  have hsum := cls_card_le_sum (s := Lx) (t := Lx.image (fun q => tb a (cls q)))
    (g := fun q => tb a (cls q)) (fun q hq => Finset.mem_image_of_mem _ hq)
    (fun _ => 2 * (r ^ (-ε) * (3 * δ / r) ^ s)) hfib
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
  have hc0 : 0 ≤ 2 * (r ^ (-ε) * (3 * δ / r) ^ s) := by positivity
  calc Marc / (K ^ 2 * arcTubeConst) ≤ (Lx.card : ℝ) := hL
    _ ≤ ((Lx.image (fun q => tb a (cls q))).card : ℝ) * (2 * (r ^ (-ε) * (3 * δ / r) ^ s)) :=
        hsum
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hcard hc0

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
