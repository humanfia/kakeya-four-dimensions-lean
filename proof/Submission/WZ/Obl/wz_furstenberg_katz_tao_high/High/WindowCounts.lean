-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WindowCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/WindowCounts.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Leaves
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TubeDictionary
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.SharedAssembly

/-!
# Counts of a `HighConfig` at the palette scales

* `HighConfig.label_facts`, `HighConfig.tube_facts`: norms, memberships and geometry of the
  labels, lines and tubes.
* `HighConfig.arc_le_avg`, `HighConfig.avg_le_arc`: the normals of one pin in one
  `palScale j`-arc lie within the ratio `K = r^(-ε)` of the average `|bush p₀| / #arcs(p₀)` of any
  reference pin `p₀` (`bal_pin_arc`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

attribute [local instance] Classical.propDecidable

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)} {tb : ℕ → E2 × E2 → E2 × E2}

/-- Norms, memberships and the class geometry of the labels of `S`. -/
theorem HighConfig.label_facts (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {q : E2 × E2} (hq : q ∈ S) :
    q ∈ D ∧ ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1 ∧ cls q ∈ J₀ ∧ ‖(cls q).1‖ ≤ 4 ∧ ‖(cls q).2‖ = 1 ∧
      (|inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
        (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r)) := by
  have hqD := hC.sub hq
  have hcl := hC.cls_mem q hqD
  have hclD := hC.lines_sub hcl
  exact ⟨hqD, hC.fail.P_norm _ (hC.fail.D_mem q hqD).1, (hC.fail.D_mem q hqD).2, hcl,
    hC.fail.P_norm _ (hC.fail.D_mem _ hclD).1, (hC.fail.D_mem _ hclD).2, hC.cls_geo q hqD⟩

/-- Norms, memberships and geometry of the tubes at a palette index `j ≤ n`. -/
theorem HighConfig.tube_facts (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {j : ℕ} (hj : j ≤ n) :
    (∀ ℓ ∈ J₀, tb j ℓ ∈ J₁ j) ∧ (∀ ℓ ∈ J₀, tb j ℓ ∈ J₀) ∧ (∀ ℓ ∈ J₀, ‖ℓ.1‖ ≤ 4) ∧
      (∀ k ∈ J₁ j, ‖k.1‖ ≤ 4 ∧ ‖k.2‖ = 1) ∧
      (∀ x ∈ J₁ j, ∀ y ∈ J₁ j, x ≠ y → StripSep (palScale r n j) x y) ∧
      (∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tb j ℓ).1) (tb j ℓ).2| < 9 * palScale r n j ∧
        (dist ℓ.2 (tb j ℓ).2 < palScale r n j ∨ dist ℓ.2 (-(tb j ℓ).2) < palScale r n j)) := by
  have hDn : ∀ q ∈ D, ‖q.1‖ ≤ 4 ∧ ‖q.2‖ = 1 := fun q hq =>
    ⟨hC.fail.P_norm _ (hC.fail.D_mem q hq).1, (hC.fail.D_mem q hq).2⟩
  refine ⟨fun ℓ hℓ => hC.tube_mem j hj ℓ hℓ,
    fun ℓ hℓ => hC.tubes_sub j (hC.tube_mem j hj ℓ hℓ),
    fun ℓ hℓ => (hDn ℓ (hC.lines_sub hℓ)).1,
    fun k hk => hDn k (hC.lines_sub (hC.tubes_sub j hk)),
    hC.tubes_sep j hj, hC.tube_geo j hj⟩

/-- The average number of normals of `p₀` per occupied `ρ`-arc. -/
noncomputable def arcAvg (ρ : ℝ) (S : Finset (E2 × E2)) (p₀ : E2) : ℝ :=
  ((bushOf S p₀).card : ℝ) / ((bushOf S p₀).image (arcOf ρ)).card

/-- Some arc of `p₀` holds at most the average, some at least the average. -/
theorem exists_arc_le_avg (ρ : ℝ) {S : Finset (E2 × E2)} {p₀ : E2}
    (hne : (bushOf S p₀).Nonempty) :
    (∃ e ∈ bushOf S p₀, ((arcNormals ρ S p₀ e).card : ℝ) ≤ arcAvg ρ S p₀) ∧
      (∃ e ∈ bushOf S p₀, arcAvg ρ S p₀ ≤ ((arcNormals ρ S p₀ e).card : ℝ)) := by
  classical
  set B := bushOf S p₀ with hB
  set A := B.image (arcOf ρ) with hA
  have hApos : (0 : ℝ) < A.card := by
    obtain ⟨e, he⟩ := hne
    exact_mod_cast Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ he⟩
  have hsum : (B.card : ℝ) = ∑ a ∈ A, ((B.filter (fun e => arcOf ρ e = a)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (arcOf ρ) B
  have hfib : ∀ e ∈ B, (B.filter (fun f => arcOf ρ f = arcOf ρ e)) = arcNormals ρ S p₀ e := by
    intro e _; rfl
  have hAne : A.Nonempty := by
    obtain ⟨e, he⟩ := hne
    exact ⟨_, Finset.mem_image_of_mem _ he⟩
  constructor
  · obtain ⟨a, ha, hmin⟩ := A.exists_min_image (fun a => ((B.filter (fun e => arcOf ρ e = a)).card : ℝ))
      hAne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨e, he, ?_⟩
    rw [← hfib e he, arcAvg, ← hB, le_div_iff₀ hApos, hsum]
    calc ((B.filter (fun f => arcOf ρ f = arcOf ρ e)).card : ℝ) * A.card
        = ∑ _a ∈ A, ((B.filter (fun f => arcOf ρ f = arcOf ρ e)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ a ∈ A, ((B.filter (fun f => arcOf ρ f = a)).card : ℝ) :=
          Finset.sum_le_sum (fun a ha => hmin a ha)
  · obtain ⟨a, ha, hmax⟩ := A.exists_max_image (fun a => ((B.filter (fun e => arcOf ρ e = a)).card : ℝ))
      hAne
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    refine ⟨e, he, ?_⟩
    rw [← hfib e he, arcAvg, ← hB, div_le_iff₀ hApos, hsum]
    calc ∑ a ∈ A, ((B.filter (fun f => arcOf ρ f = a)).card : ℝ)
        ≤ ∑ _a ∈ A, ((B.filter (fun f => arcOf ρ f = arcOf ρ e)).card : ℝ) :=
          Finset.sum_le_sum (fun a ha => hmax a ha)
      _ = ((B.filter (fun f => arcOf ρ f = arcOf ρ e)).card : ℝ) * A.card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Arc counts against the average of a reference pin** (`bal_pin_arc`): every occupied
(pin, `palScale j`-arc) holds between `avg / K` and `K · avg` normals, `K = r^(-ε)`. -/
theorem HighConfig.arc_avg_bounds (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {j : ℕ} (hj : j ≤ n) {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) :
    ∀ q ∈ S, ((arcNormals (palScale r n j) S q.1 q.2).card : ℝ) ≤
        r ^ (-ε) * arcAvg (palScale r n j) S p₀ ∧
      arcAvg (palScale r n j) S p₀ ≤ r ^ (-ε) * (arcNormals (palScale r n j) S q.1 q.2).card := by
  classical
  intro q hq
  set ρ := palScale r n j with hρ
  have hbal := hC.bal_pin_arc j hj
  obtain ⟨q₀, hq₀S, hq₀p⟩ := Finset.mem_image.mp hp₀
  have hne : (bushOf S p₀).Nonempty := ⟨q₀.2, by rw [mem_bushOf, ← hq₀p]; exact hq₀S⟩
  obtain ⟨⟨e₁, he₁, hle⟩, ⟨e₂, he₂, hge⟩⟩ := exists_arc_le_avg ρ hne
  -- the fiber of a label `(p, e)` of the (pin, arc) map has the size of `arcNormals ρ S p e`
  have hfib : ∀ x ∈ S, ((leafFiber S (fun q => (q.1, arcOf ρ q.2)) x).card : ℝ) =
      (arcNormals ρ S x.1 x.2).card := by
    intro x _
    have := card_arc_fiber ρ S x.1 x.2
    have heq : leafFiber S (fun q => (q.1, arcOf ρ q.2)) x =
        S.filter (fun a => a.1 = x.1 ∧ arcOf ρ a.2 = arcOf ρ x.2) := by
      ext a; simp [leafFiber, Prod.ext_iff]
    rw [heq]; exact_mod_cast this
  have hm₁ : (p₀, e₁) ∈ S := by rw [← mem_bushOf]; exact he₁
  have hm₂ : (p₀, e₂) ∈ S := by rw [← mem_bushOf]; exact he₂
  have h1 := hbal q hq (p₀, e₁) hm₁
  have h2 := hbal (p₀, e₂) hm₂ q hq
  rw [hfib q hq, hfib _ hm₁] at h1
  rw [hfib q hq, hfib _ hm₂] at h2
  have hK : 0 ≤ r ^ (-ε) := Real.rpow_nonneg hC.fail.r_pos.le _
  constructor
  · calc ((arcNormals ρ S q.1 q.2).card : ℝ) ≤ r ^ (-ε) * (arcNormals ρ S p₀ e₁).card := h1
      _ ≤ r ^ (-ε) * arcAvg ρ S p₀ := mul_le_mul_of_nonneg_left hle hK
  · calc arcAvg ρ S p₀ ≤ (arcNormals ρ S p₀ e₂).card := hge
      _ ≤ r ^ (-ε) * (arcNormals ρ S q.1 q.2).card := h2

/-- The quadratic constant of `tube_quadratic_of_fail` at ratio `K` and two-ends radius `c`. -/
noncomputable def quadConst (r s ε K c : ℝ) : ℝ :=
  2 * ((⌈4 * r ^ (-ε)⌉₊ : ℕ) : ℝ) ^ 2 * K ^ 3 * (2 * r ^ (-ε) * ((52 : ℝ) ^ s * c ^ (-s)))

theorem quadConst_nonneg {r s ε K c : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hc : 0 < c) :
    0 ≤ quadConst r s ε K c := by
  unfold quadConst
  have h1 : 0 ≤ r ^ (-ε) := Real.rpow_nonneg hr.le _
  have h2 : 0 ≤ (52 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) _
  have h3 : 0 ≤ c ^ (-s) := Real.rpow_nonneg hc.le _
  positivity

/-- **Upper count of the occupied tubes at a palette index** (`coarse_lines_count`): with the
two-ends radius `c` of `line_frostman` (`r^(-κ) c^(1-s) ≤ 1/2`), the occupied `palScale j`-tubes
satisfy `#tubes · (avg / (K² arcTubeConst))² ≤ quadConst · #lines`, where `avg` is the
average number of normals of a reference pin per occupied arc. -/
theorem HighConfig.tubes_upper (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {j : ℕ} (hj : j ≤ n)
    (hrρ : 10 * r ≤ palScale r n j) (hρ2 : 142 * palScale r n j ≤ 1 / 2)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) {c : ℝ} (hrc : r ≤ c)
    (hcfar : r ^ (-κ) * c ^ (1 - s) ≤ 1 / 2) :
    ((S.image (fun q => tb j (cls q))).card : ℝ) *
        (arcAvg (palScale r n j) S p₀ / ((r ^ (-ε)) ^ 2 * arcTubeConst)) ^ 2 ≤
      quadConst r s ε (r ^ (-ε)) c * (S.image cls).card := by
  classical
  have hr := hC.fail.r_pos
  have hK : 0 < r ^ (-ε) := Real.rpow_pos_of_pos hr _
  have hc : 0 < c := lt_of_lt_of_le hr hrc
  obtain ⟨htbJ₁, htbJ₀, hJ₀4, hJ₁n, hJ₁sep, htbgeo⟩ := hC.tube_facts hj
  have hS : ∀ q ∈ S, q.1 ∈ S.image Prod.fst ∧ ‖q.2‖ = 1 := fun q hq =>
    ⟨Finset.mem_image_of_mem _ hq, (hC.label_facts hq).2.2.1⟩
  have hQ4 : ∀ p ∈ S.image Prod.fst, ‖p‖ ≤ 4 := fun p hp => hC.failS.P_norm p hp
  have harcmin : ∀ p ∈ S.image Prod.fst, ∀ e ∈ bushOf S p,
      arcAvg (palScale r n j) S p₀ ≤ r ^ (-ε) * (arcNormals (palScale r n j) S p e).card := by
    intro p _ e he
    have hpe : (p, e) ∈ S := by rw [← mem_bushOf]; exact he
    exact (hC.arc_avg_bounds hj hp₀ (p, e) hpe).2
  have hcls4 : ∀ q ∈ S, ‖(cls q).1‖ ≤ 4 := fun q hq => (hC.label_facts hq).2.2.2.2.1
  have hgeo : ∀ q ∈ S, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r) := fun q hq =>
    (hC.label_facts hq).2.2.2.2.2.2
  have htb4 : ∀ q ∈ S, ‖(tb j (cls q)).1‖ ≤ 4 ∧ ‖(tb j (cls q)).2‖ = 1 := fun q hq =>
    hJ₁n _ (htbJ₁ _ (hC.label_facts hq).2.2.2.1)
  have htb : ∀ q ∈ S, |inner ℝ ((cls q).1 - (tb j (cls q)).1) (tb j (cls q)).2| <
      9 * palScale r n j ∧ (dist (cls q).2 (tb j (cls q)).2 < palScale r n j ∨
        dist (cls q).2 (-(tb j (cls q)).2) < palScale r n j) := fun q hq =>
    htbgeo _ (hC.label_facts hq).2.2.2.1
  have hsep : ∀ x ∈ S.image (fun a => tb j (cls a)), ∀ y ∈ S.image (fun a => tb j (cls a)),
      x ≠ y → StripSep (palScale r n j) x y := by
    intro x hx y hy hxy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hy
    exact hJ₁sep _ (htbJ₁ _ (hC.label_facts hq).2.2.2.1) _ (htbJ₁ _ (hC.label_facts hq').2.2.2.1) hxy
  have hlow : ∀ q ∈ S, arcAvg (palScale r n j) S p₀ / ((r ^ (-ε)) ^ 2 * arcTubeConst) ≤
      ((S.filter (fun a => a.1 = q.1 ∧ tb j (cls a) = tb j (cls q))).card : ℝ) :=
    fun q hq => pin_tube_labels_ge hr hrρ hρ2 hK hS hQ4 harcmin hcls4 hgeo htb4 htb hsep
      (hC.bal_pin_tube j hj) hq
  have hcls1D : ∀ q ∈ D, ‖(cls q).2‖ = 1 := fun q hq =>
    (hC.fail.D_mem _ (hC.lines_sub (hC.cls_mem q hq))).2
  have hfar : ∀ q ∈ S, 2 * ((((S.filter (fun q' => cls q' = cls q)).filter
      (fun q' => dist q'.1 q.1 < c)).card : ℝ)) ≤ (S.filter (fun q' => cls q' = cls q)).card := by
    intro q hq
    have h1 := hC.line_frostman q hq c hrc
    have h0 : (0 : ℝ) ≤ (S.filter (fun q' => cls q' = cls q)).card := Nat.cast_nonneg _
    nlinarith
  have hquad : ∀ q₀ ∈ S,
      ((S.filter (fun q => q.1 = q₀.1 ∧ tb j (cls q) = tb j (cls q₀))).card : ℝ) ^ 2 ≤
        quadConst r s ε (r ^ (-ε)) c *
          ((S.filter (fun q => tb j (cls q) = tb j (cls q₀))).image cls).card := by
    intro q₀ hq₀
    have := tube_quadratic_of_fail (tb := tb j) hC.fail hs0 hs1 hc hK hcls1D hC.cls_geo hC.sub
      (hC.bal_pin_tube j hj) hC.bal_cls hfar hq₀
    unfold quadConst
    exact this
  have hm0 : 0 ≤ arcAvg (palScale r n j) S p₀ / ((r ^ (-ε)) ^ 2 * arcTubeConst) := by
    unfold arcAvg
    have : 0 < arcTubeConst := by rw [arcTubeConst]; norm_num
    positivity
  exact coarse_lines_count hm0 (quadConst_nonneg hr hK.le hc) hlow hquad

/-- **Lower count of the occupied tubes at a palette index** (`occupied_tubes_ge`): every pin
meets at least `r^(ε-s) / (98 K avg)` tubes (`pinTubes_ge_of_caps`, arcs at most `K avg`), so
`(r^(ε-s) / (98 K avg))² ≤ pinConst · #tubes`. -/
theorem HighConfig.tubes_lower (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {j : ℕ} (hj : j ≤ n) (hrw : 2 * r ≤ palScale r n j) (hw2 : 26 * palScale r n j ≤ 1 / 2)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) (KY : ℕ)
    (hKY : ((S.image Prod.fst).card : ℝ) ≤ 2 ^ KY) :
    (r ^ (ε - s) / (2 * (49 * (r ^ (-ε) * arcAvg (palScale r n j) S p₀)))) ^ 2 ≤
      pinConst (palScale r n j) (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY *
        (S.image (fun q => tb j (cls q))).card := by
  classical
  have hr := hC.fail.r_pos
  have hw : 0 < palScale r n j := by linarith
  obtain ⟨htbJ₁, htbJ₀, hJ₀4, hJ₁n, hJ₁sep, htbgeo⟩ := hC.tube_facts hj
  set M := r ^ (-ε) * arcAvg (palScale r n j) S p₀ with hM
  have hM0 : 0 ≤ M := by
    rw [hM]; unfold arcAvg
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (by positivity)
  have hgeo : ∀ q ∈ S, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r) := fun q hq =>
    (hC.label_facts hq).2.2.2.2.2.2
  have htb : ∀ q ∈ S, |inner ℝ ((cls q).1 - (tb j (cls q)).1) (tb j (cls q)).2| <
      9 * palScale r n j ∧ (dist (cls q).2 (tb j (cls q)).2 < palScale r n j ∨
        dist (cls q).2 (-(tb j (cls q)).2) < palScale r n j) := fun q hq =>
    htbgeo _ (hC.label_facts hq).2.2.2.1
  have harc : ∀ p ∈ S.image Prod.fst, ∀ e ∈ bushOf S p,
      ((arcNormals (palScale r n j) S p e).card : ℝ) ≤ M := by
    intro p _ e he
    have hpe : (p, e) ∈ S := by rw [← mem_bushOf]; exact he
    exact (hC.arc_avg_bounds hj hp₀ (p, e) hpe).1
  have hBpin : ∀ p ∈ S.image Prod.fst,
      r ^ (ε - s) / (2 * (49 * M)) ≤ ((pinTubes S cls (tb j) p).card : ℝ) := by
    intro p hp
    have h1 := pinTubes_ge_of_caps hr.le (by linarith) hw hM0 p hgeo htb (harc p hp)
    have h2 := hC.failS.D_card p hp
    by_cases hMpos : 0 < M
    · rw [div_le_iff₀ (by positivity)]
      linarith
    · have hM0' : M = 0 := le_antisymm (not_lt.mp hMpos) hM0
      rw [hM0', mul_zero, mul_zero, div_zero]
      exact Nat.cast_nonneg _
  have hB0 : 0 ≤ r ^ (ε - s) / (2 * (49 * M)) := by
    have : 0 ≤ r ^ (ε - s) := Real.rpow_nonneg hr.le _
    positivity
  exact occupied_tubes_ge (by linarith) hw2 hB0 hC.failS
    (fun q hq => (hC.label_facts hq).2.2.2.2.1) (fun q hq => (hC.label_facts hq).2.2.2.2.2.1)
    hgeo (fun q hq => htbJ₁ _ (hC.label_facts hq).2.2.2.1) hJ₁n hJ₁sep htb hBpin KY hKY

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
