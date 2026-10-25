-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.Charts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/Charts.lean (82de8bd).
-- Copied from workspace o222, branch x0658 (commit 1206391), Charts.lean; namespace renamed.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.ChartedEndgame

/-!
# Four charts for arbitrary columns

Codes `(u, v)` are heights of a tube line at the normalized anchor positions `0`
and `1`; its height at position `τ` is `(1 - τ) u + τ v`. Every `τ` lies in one of
four regions on which a signed coordinate swap `φ` and a slope `t ∈ [0, 1]` give
`(1 - τ) u + τ v = λ (φ(u,v).1 + t φ(u,v).2)` with `λ ≥ 1/2`. The region holding at
least a quarter of the columns is used, which reduces arbitrary columns to the
charted endgame. (Written for o222; x0603's o214 FourCharts is a related idea.)
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open Set Metric

/-- The heights of the line with codes `w` at position `τ`. -/
def hgt (w : ℝ × ℝ) (τ : ℝ) : ℝ := (1 - τ) * w.1 + τ * w.2

/-- The four regions: `0 : [0,1/2]`, `1 : (1/2,1]`, `2 : (1,∞)`, `3 : (-∞,0)`. -/
def region : Fin 4 → ℝ → Prop
  | 0, τ => 0 ≤ τ ∧ τ ≤ 1 / 2
  | 1, τ => 1 / 2 < τ ∧ τ ≤ 1
  | 2, τ => 1 < τ
  | 3, τ => τ < 0

/-- The signed coordinate swaps. -/
def chartMap : Fin 4 → ℝ × ℝ → ℝ × ℝ
  | 0, w => (w.1, w.2)
  | 1, w => (w.2, w.1)
  | 2, w => (w.2, -w.1)
  | 3, w => (w.1, -w.2)

/-- The slope parameter in each chart. -/
noncomputable def chartSlope : Fin 4 → ℝ → ℝ
  | 0, τ => τ / (1 - τ)
  | 1, τ => (1 - τ) / τ
  | 2, τ => (τ - 1) / τ
  | 3, τ => -τ / (1 - τ)

/-- The interpolation factor in each chart. -/
def chartScale : Fin 4 → ℝ → ℝ
  | 0, τ => 1 - τ
  | 1, τ => τ
  | 2, τ => τ
  | 3, τ => 1 - τ

lemma region_cover (τ : ℝ) : ∃ c : Fin 4, region c τ := by
  by_cases h0 : τ < 0
  · exact ⟨3, h0⟩
  by_cases h1 : τ ≤ 1 / 2
  · exact ⟨0, le_of_not_gt h0, h1⟩
  by_cases h2 : τ ≤ 1
  · exact ⟨1, lt_of_not_ge h1, h2⟩
  · exact ⟨2, lt_of_not_ge h2⟩

lemma chartScale_ge (c : Fin 4) {τ : ℝ} (h : region c τ) : 1 / 2 ≤ chartScale c τ := by
  fin_cases c <;> simp only [region, chartScale] at h ⊢ <;>
    first | linarith [h.1, h.2] | linarith [h]

lemma chart_identity (c : Fin 4) {τ : ℝ} (h : region c τ) (w : ℝ × ℝ) :
    hgt w τ = chartScale c τ * ((chartMap c w).1 + chartSlope c τ * (chartMap c w).2) := by
  fin_cases c <;> simp only [region] at h <;>
    simp only [hgt, chartScale, chartMap, chartSlope]
  · have : (1 - τ) ≠ 0 := by linarith [h.2]
    field_simp
  · have : τ ≠ 0 := by linarith [h.1]
    field_simp
    ring
  · have : τ ≠ 0 := by linarith
    field_simp
    ring
  · have : (1 - τ) ≠ 0 := by linarith
    field_simp

lemma chartSlope_mem (c : Fin 4) {τ : ℝ} (h : region c τ) :
    chartSlope c τ ∈ Icc (0 : ℝ) 1 := by
  fin_cases c <;> simp only [region] at h <;> simp only [chartSlope, mem_Icc]
  · have h1 : 0 < 1 - τ := by linarith [h.2]
    constructor
    · exact div_nonneg h.1 h1.le
    · rw [div_le_one h1]; linarith [h.2]
  · have h1 : 0 < τ := by linarith [h.1]
    constructor
    · exact div_nonneg (by linarith [h.2]) h1.le
    · rw [div_le_one h1]; linarith [h.1]
  · have h1 : 0 < τ := by linarith
    constructor
    · exact div_nonneg (by linarith) h1.le
    · rw [div_le_one h1]; linarith
  · have h1 : 0 < 1 - τ := by linarith
    constructor
    · exact div_nonneg (by linarith) h1.le
    · rw [div_le_one h1]; linarith

/-- Inverse Lipschitz bound for the slope on a bounded part of a region. -/
lemma chartSlope_dist (c : Fin 4) {B τ τ' : ℝ} (hB : 1 ≤ B) (h : region c τ)
    (h' : region c τ') (hb : |τ| ≤ B) (hb' : |τ'| ≤ B) :
    |τ - τ'| ≤ (1 + B) ^ 2 * |chartSlope c τ - chartSlope c τ'| := by
  rw [abs_le] at hb hb'
  have hBB : (1 : ℝ) ≤ (1 + B) ^ 2 := by nlinarith
  fin_cases c <;> simp only [region] at h h' <;> simp only [chartSlope]
  · have h1 : 0 < 1 - τ := by linarith [h.2]
    have h1' : 0 < 1 - τ' := by linarith [h'.2]
    have e : τ / (1 - τ) - τ' / (1 - τ') = (τ - τ') / ((1 - τ) * (1 - τ')) := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos (mul_pos h1 h1')]
    have hp : (1 - τ) * (1 - τ') ≤ 1 := by nlinarith [h.1, h'.1]
    rw [mul_div_assoc']
    rw [le_div_iff₀ (mul_pos h1 h1')]
    nlinarith [abs_nonneg (τ - τ')]
  · have h1 : 0 < τ := by linarith [h.1]
    have h1' : 0 < τ' := by linarith [h'.1]
    have e : (1 - τ) / τ - (1 - τ') / τ' = (τ' - τ) / (τ * τ') := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos (mul_pos h1 h1'), abs_sub_comm τ' τ]
    have hp : τ * τ' ≤ 1 := by nlinarith [h.2, h'.2]
    rw [mul_div_assoc', le_div_iff₀ (mul_pos h1 h1')]
    nlinarith [abs_nonneg (τ - τ')]
  · have h1 : 0 < τ := by linarith
    have h1' : 0 < τ' := by linarith
    have e : (τ - 1) / τ - (τ' - 1) / τ' = (τ - τ') / (τ * τ') := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos (mul_pos h1 h1')]
    have hp : τ * τ' ≤ (1 + B) ^ 2 := by nlinarith
    rw [mul_div_assoc', le_div_iff₀ (mul_pos h1 h1')]
    nlinarith [abs_nonneg (τ - τ')]
  · have h1 : 0 < 1 - τ := by linarith
    have h1' : 0 < 1 - τ' := by linarith
    have e : -τ / (1 - τ) - -τ' / (1 - τ') = (τ' - τ) / ((1 - τ) * (1 - τ')) := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos (mul_pos h1 h1'), abs_sub_comm τ' τ]
    have hp : (1 - τ) * (1 - τ') ≤ (1 + B) ^ 2 := by nlinarith
    rw [mul_div_assoc', le_div_iff₀ (mul_pos h1 h1')]
    nlinarith [abs_nonneg (τ - τ')]

lemma chartMap_dist (c : Fin 4) (w w' : ℝ × ℝ) :
    dist (chartMap c w) (chartMap c w') = dist w w' := by
  fin_cases c <;> simp only [chartMap, Prod.dist_eq, Real.dist_eq]
  · rw [max_comm]
  · rw [max_comm, show -w.1 - -w'.1 = -(w.1 - w'.1) by ring, abs_neg]
  · rw [show -w.2 - -w'.2 = -(w.2 - w'.2) by ring, abs_neg]

lemma chartMap_injective (c : Fin 4) : Function.Injective (chartMap c) := by
  intro w w' h
  have := chartMap_dist c w w'
  rw [h, dist_self] at this
  exact dist_eq_zero.mp this.symm

/-- The preimage of a coordinate square under a chart map is a coordinate square. -/
lemma chartMap_square (c : Fin 4) (x y ρ : ℝ) :
    ∃ x' y' : ℝ, ∀ w : ℝ × ℝ,
      (|(chartMap c w).1 - x| ≤ ρ ∧ |(chartMap c w).2 - y| ≤ ρ) ↔
        (|w.1 - x'| ≤ ρ ∧ |w.2 - y'| ≤ ρ) := by
  fin_cases c <;> simp only [chartMap]
  · exact ⟨x, y, fun w => Iff.rfl⟩
  · exact ⟨y, x, fun w => And.comm⟩
  · refine ⟨-y, x, fun w => ?_⟩
    rw [show -w.1 - y = -(w.1 - -y) by ring, abs_neg, And.comm]
  · refine ⟨x, -y, fun w => ?_⟩
    rw [show -w.2 - y = -(w.2 - -y) by ring, abs_neg]

/-- Fibers of chart coordinates. -/
lemma chartMap_fibers (c : Fin 4) {δ F : ℝ} (W : Finset (ℝ × ℝ)) (Y0 Y1 : Finset ℝ)
    (hY0 : (Y0.card : ℝ) ≤ F) (hY1 : (Y1.card : ℝ) ≤ F)
    (hW0 : ∀ w ∈ W, ∃ y ∈ Y0, |w.1 - y| ≤ δ) (hW1 : ∀ w ∈ W, ∃ y ∈ Y1, |w.2 - y| ≤ δ) :
    ∃ Z0 Z1 : Finset ℝ, (Z0.card : ℝ) ≤ F ∧ (Z1.card : ℝ) ≤ F ∧
      (∀ w ∈ W, ∃ y ∈ Z0, |(chartMap c w).1 - y| ≤ δ) ∧
      (∀ w ∈ W, ∃ y ∈ Z1, |(chartMap c w).2 - y| ≤ δ) := by
  classical
  have hneg : ∀ (Y : Finset ℝ), (∀ w ∈ W, ∃ y ∈ Y, |w.1 - y| ≤ δ) →
      ∀ w ∈ W, ∃ y ∈ Y.image Neg.neg, |-w.1 - y| ≤ δ := by
    intro Y hY w hw
    obtain ⟨y, hy, h⟩ := hY w hw
    refine ⟨-y, Finset.mem_image_of_mem _ hy, ?_⟩
    rw [show -w.1 - -y = -(w.1 - y) by ring, abs_neg]; exact h
  have hneg2 : ∀ (Y : Finset ℝ), (∀ w ∈ W, ∃ y ∈ Y, |w.2 - y| ≤ δ) →
      ∀ w ∈ W, ∃ y ∈ Y.image Neg.neg, |-w.2 - y| ≤ δ := by
    intro Y hY w hw
    obtain ⟨y, hy, h⟩ := hY w hw
    refine ⟨-y, Finset.mem_image_of_mem _ hy, ?_⟩
    rw [show -w.2 - -y = -(w.2 - y) by ring, abs_neg]; exact h
  have hc0 : ((Y0.image Neg.neg).card : ℝ) ≤ F :=
    le_trans (by exact_mod_cast Finset.card_image_le) hY0
  have hc1 : ((Y1.image Neg.neg).card : ℝ) ≤ F :=
    le_trans (by exact_mod_cast Finset.card_image_le) hY1
  fin_cases c <;> simp only [chartMap]
  · exact ⟨Y0, Y1, hY0, hY1, hW0, hW1⟩
  · exact ⟨Y1, Y0, hY1, hY0, hW1, hW0⟩
  · exact ⟨Y1, Y0.image Neg.neg, hY1, hc0, hW1, hneg Y0 hW0⟩
  · exact ⟨Y0, Y1.image Neg.neg, hY0, hc1, hW0, hneg2 Y1 hW1⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open Set Metric

attribute [local instance] Classical.propDecidable

lemma chartMap_bound (c : Fin 4) {w : ℝ × ℝ} (h : |w.1| ≤ 7 / 2 ∧ |w.2| ≤ 7 / 2) :
    |(chartMap c w).1| ≤ 7 / 2 ∧ |(chartMap c w).2| ≤ 7 / 2 := by
  fin_cases c <;> simp only [chartMap, abs_neg] <;> first | exact h | exact ⟨h.2, h.1⟩

/-- Some chart holds at least a quarter of a finite set of positions. -/
lemma exists_popular_chart (X : Finset ℝ) :
    ∃ c : Fin 4, (X.card : ℝ) ≤ 4 * ((X.filter (fun τ => region c τ)).card : ℝ) := by
  classical
  have hsub : X ⊆ Finset.univ.biUnion (fun c : Fin 4 => X.filter (fun τ => region c τ)) := by
    intro τ hτ
    obtain ⟨c, hc⟩ := region_cover τ
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hτ, hc⟩⟩
  have hsum : X.card ≤ ∑ c : Fin 4, (X.filter (fun τ => region c τ)).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  by_contra hcon
  push Not at hcon
  have : ∀ c : Fin 4, 4 * (X.filter (fun τ => region c τ)).card < X.card := by
    intro c
    have := hcon c
    exact_mod_cast this
  have h4 : 4 * ∑ c : Fin 4, (X.filter (fun τ => region c τ)).card < 4 * X.card := by
    rw [Finset.mul_sum]
    calc ∑ c : Fin 4, 4 * (X.filter (fun τ => region c τ)).card
        < ∑ _c : Fin 4, X.card := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          (fun c _ => this c)
      _ = 4 * X.card := by simp
  omega

theorem positions_endgame {δ F K γ β B : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hK : 1 ≤ K)
    (hγ : 0 ≤ γ) (hβ : 0 ≤ β) (hB : 1 ≤ B)
    (W : Finset (ℝ × ℝ)) (hWne : W.Nonempty)
    (hWb : ∀ w ∈ W, |w.1| ≤ 7 / 2 ∧ |w.2| ≤ 7 / 2)
    (hWsep : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → δ ≤ dist w w')
    (Y0 Y1 : Finset ℝ) (hY0 : (Y0.card : ℝ) ≤ F) (hY1 : (Y1.card : ℝ) ≤ F)
    (hW0 : ∀ w ∈ W, ∃ y ∈ Y0, |w.1 - y| ≤ δ) (hW1 : ∀ w ∈ W, ∃ y ∈ Y1, |w.2 - y| ≤ δ)
    (hsq : ∀ x y ρ : ℝ, δ ≤ ρ →
      ((W.filter (fun w => |w.1 - x| ≤ ρ ∧ |w.2 - y| ≤ ρ)).card : ℝ) ≤
        K * ρ ^ γ * W.card)
    (hWbig : F ^ 2 ≤ K * W.card)
    (X : Finset ℝ) (hXne : X.Nonempty) (hXB : ∀ τ ∈ X, |τ| ≤ B)
    (hXfr : ∀ x ρ : ℝ, δ ≤ ρ →
      ((X.filter (fun τ => dist τ x ≤ ρ)).card : ℝ) ≤ K * ρ ^ β * X.card)
    (Wx : ℝ → Finset (ℝ × ℝ)) (hWx : ∀ τ ∈ X, Wx τ ⊆ W)
    (hWxbig : ∀ τ ∈ X, (W.card : ℝ) ≤ K * (Wx τ).card)
    (Yx : ℝ → Finset ℝ) (hYx : ∀ τ ∈ X, ((Yx τ).card : ℝ) ≤ F)
    (hcovx : ∀ τ ∈ X, ∀ w ∈ Wx τ, ∃ y ∈ Yx τ, |hgt w τ - y| ≤ δ) :
    ∃ (G : Set (ℝ × ℝ)) (S : Set ℝ), G.Finite ∧ G.Nonempty ∧ S.Finite ∧ S.Nonempty ∧
      (∀ p ∈ G, |p.1| ≤ 4 ∧ |p.2| ≤ 4) ∧
      (∀ x y ρ : ℝ, δ ≤ ρ →
        ({p ∈ G | dist p.1 x ≤ ρ ∧ dist p.2 y ≤ ρ}.ncard : ℝ) ≤
          ((4 * K * (2 * (1 + B) ^ 2) ^ β) * 2 ^ γ) * ρ ^ γ * G.ncard) ∧
      (∀ x ρ : ℝ, δ ≤ ρ → ((S ∩ closedBall x ρ).ncard : ℝ) ≤
          (4 * K * (2 * (1 + B) ^ 2) ^ β) * ρ ^ β * S.ncard) ∧
      (∀ t ∈ S, t ∈ Icc (0 : ℝ) 1) ∧
      (∀ a ∈ Prod.fst '' G, ∀ a' ∈ Prod.fst '' G, a ≠ a' → δ ≤ dist a a') ∧
      (∀ a ∈ Prod.snd '' G, ∀ a' ∈ Prod.snd '' G, a ≠ a' → δ ≤ dist a a') ∧
      ((Prod.fst '' G).ncard : ℝ) ≤ 3 * F ∧ ((Prod.snd '' G).ncard : ℝ) ≤ 3 * F ∧
      F ^ 2 ≤ (4 * K * (2 * (1 + B) ^ 2) ^ β) * G.ncard ∧
      (∀ t ∈ S, ∃ H : Set (ℝ × ℝ), H ⊆ G ∧
        (G.ncard : ℝ) ≤ (4 * K * (2 * (1 + B) ^ 2) ^ β) * H.ncard ∧
        ∃ (m : ℕ) (cc : Fin m → ℝ),
          (fun p : ℝ × ℝ => p.1 + t * p.2) '' H ⊆ (⋃ j, closedBall (cc j) δ) ∧
          (m : ℝ) ≤ 4 * F) := by
  classical
  set K₁ : ℝ := 4 * K * (2 * (1 + B) ^ 2) ^ β with hK₁
  have hBB : (1 : ℝ) ≤ 2 * (1 + B) ^ 2 := by nlinarith
  have hpow : (1 : ℝ) ≤ (2 * (1 + B) ^ 2) ^ β := Real.one_le_rpow hBB hβ
  have hKK₁ : K ≤ K₁ := by
    rw [hK₁]; nlinarith
  have hK₁1 : 1 ≤ K₁ := hK.trans hKK₁
  obtain ⟨c, hc⟩ := exists_popular_chart X
  set Xc : Finset ℝ := X.filter (fun τ => region c τ) with hXc
  have hXcne : Xc.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty, Nat.cast_zero, mul_zero] at hc
    have : (0 : ℝ) < X.card := by exact_mod_cast hXne.card_pos
    linarith
  have hXcX : Xc ⊆ X := Finset.filter_subset _ _
  have hXcreg : ∀ τ ∈ Xc, region c τ := fun τ hτ => (Finset.mem_filter.mp hτ).2
  have hslope_inj : Set.InjOn (chartSlope c) (Xc : Set ℝ) := by
    intro τ hτ τ' hτ' he
    have := chartSlope_dist c hB (hXcreg τ hτ) (hXcreg τ' hτ') (hXB τ (hXcX hτ))
      (hXB τ' (hXcX hτ'))
    rw [he, sub_self, abs_zero, mul_zero] at this
    exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
  set T : Finset ℝ := Xc.image (chartSlope c) with hT
  have hTcard : T.card = Xc.card := Finset.card_image_of_injOn hslope_inj
  -- the column of a slope
  have hpre : ∀ t ∈ T, ∃ τ ∈ Xc, chartSlope c τ = t := fun t ht => Finset.mem_image.mp ht
  let g : ℝ → ℝ := fun t => if h : ∃ τ ∈ Xc, chartSlope c τ = t then Classical.choose h else 0
  have hg : ∀ t ∈ T, g t ∈ Xc ∧ chartSlope c (g t) = t := by
    intro t ht
    have h := hpre t ht
    simp only [g, dif_pos h]
    exact Classical.choose_spec h
  set W' : Finset (ℝ × ℝ) := W.image (chartMap c) with hW'
  have hW'card : W'.card = W.card :=
    Finset.card_image_of_injective _ (chartMap_injective c)
  obtain ⟨Z0, Z1, hZ0, hZ1, hWZ0, hWZ1⟩ := chartMap_fibers c (δ := δ) W Y0 Y1 hY0 hY1 hW0 hW1
  have key := charted_endgame (K := K₁) (γ := γ) (β := β) (F := F) hδ hδ2 hK₁1 hγ W'
    (hWne.image _)
    (by
      intro w' hw'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hw'
      exact chartMap_bound c (hWb w hw))
    (by
      intro w' hw' w'' hw'' hne
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hw'
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw''
      rw [chartMap_dist]
      exact hWsep w hw v hv (fun h => hne (by rw [h])))
    Z0 Z1 hZ0 hZ1
    (by
      intro w' hw'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hw'
      exact hWZ0 w hw)
    (by
      intro w' hw'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hw'
      exact hWZ1 w hw)
    (by
      intro x y ρ hρ
      obtain ⟨x', y', hxy⟩ := chartMap_square c x y ρ
      have hfil : W'.filter (fun w => |w.1 - x| ≤ ρ ∧ |w.2 - y| ≤ ρ) =
          (W.filter (fun w => |w.1 - x'| ≤ ρ ∧ |w.2 - y'| ≤ ρ)).image (chartMap c) := by
        rw [hW']
        ext z
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨w, hw, rfl⟩, hz⟩
          exact ⟨w, ⟨hw, (hxy w).mp hz⟩, rfl⟩
        · rintro ⟨w, ⟨hw, hz⟩, rfl⟩
          exact ⟨⟨w, hw, rfl⟩, (hxy w).mpr hz⟩
      rw [hfil, Finset.card_image_of_injective _ (chartMap_injective c), hW'card]
      have hρ0 : 0 ≤ ρ ^ γ := Real.rpow_nonneg (hδ.le.trans hρ) _
      calc _ ≤ K * ρ ^ γ * W.card := hsq x' y' ρ hρ
        _ ≤ K₁ * ρ ^ γ * W.card := by gcongr)
    (by rw [hW'card]; linarith [mul_le_mul_of_nonneg_right hKK₁ (Nat.cast_nonneg (α := ℝ) W.card)])
    T (hXcne.image _)
    (by
      intro t ht
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp ht
      exact chartSlope_mem c (hXcreg τ hτ))
    (by
      intro x ρ hρ
      have hρ0 : 0 < ρ := hδ.trans_le hρ
      rw [hTcard]
      have hsub : T.filter (fun t => dist t x ≤ ρ) ⊆
          (Xc.filter (fun τ => dist (chartSlope c τ) x ≤ ρ)).image (chartSlope c) := by
        intro t ht
        obtain ⟨htT, htx⟩ := Finset.mem_filter.mp ht
        obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp htT
        exact Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨hτ, htx⟩, rfl⟩
      have h1 : ((T.filter (fun t => dist t x ≤ ρ)).card : ℝ) ≤
          ((Xc.filter (fun τ => dist (chartSlope c τ) x ≤ ρ)).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
      by_cases hemp : (Xc.filter (fun τ => dist (chartSlope c τ) x ≤ ρ)).Nonempty
      · obtain ⟨τ₀, hτ₀⟩ := hemp
        obtain ⟨hτ₀X, hτ₀x⟩ := Finset.mem_filter.mp hτ₀
        have hsub2 : Xc.filter (fun τ => dist (chartSlope c τ) x ≤ ρ) ⊆
            X.filter (fun τ => dist τ τ₀ ≤ 2 * (1 + B) ^ 2 * ρ) := by
          intro τ hτ
          obtain ⟨hτX, hτx⟩ := Finset.mem_filter.mp hτ
          refine Finset.mem_filter.mpr ⟨hXcX hτX, ?_⟩
          have hd := chartSlope_dist c hB (hXcreg τ hτX) (hXcreg τ₀ hτ₀X) (hXB τ (hXcX hτX))
            (hXB τ₀ (hXcX hτ₀X))
          rw [Real.dist_eq] at hτx hτ₀x ⊢
          have : |chartSlope c τ - chartSlope c τ₀| ≤ 2 * ρ := by
            calc |chartSlope c τ - chartSlope c τ₀|
                = |(chartSlope c τ - x) - (chartSlope c τ₀ - x)| := by ring_nf
              _ ≤ |chartSlope c τ - x| + |chartSlope c τ₀ - x| := abs_sub _ _
              _ ≤ 2 * ρ := by linarith
          have hBp : 0 ≤ (1 + B) ^ 2 := by positivity
          nlinarith
        have h2 : ((Xc.filter (fun τ => dist (chartSlope c τ) x ≤ ρ)).card : ℝ) ≤
            ((X.filter (fun τ => dist τ τ₀ ≤ 2 * (1 + B) ^ 2 * ρ)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub2
        have hρ' : δ ≤ 2 * (1 + B) ^ 2 * ρ := by nlinarith
        have h3 := hXfr τ₀ (2 * (1 + B) ^ 2 * ρ) hρ'
        have h4 : (2 * (1 + B) ^ 2 * ρ) ^ β = (2 * (1 + B) ^ 2) ^ β * ρ ^ β :=
          Real.mul_rpow (by positivity) hρ0.le
        rw [h4] at h3
        have hXc4 : (X.card : ℝ) ≤ 4 * (Xc.card : ℝ) := hc
        have hρb : 0 ≤ ρ ^ β := Real.rpow_nonneg hρ0.le _
        have hK0 : 0 ≤ K := by linarith
        calc ((T.filter (fun t => dist t x ≤ ρ)).card : ℝ)
            ≤ K * ((2 * (1 + B) ^ 2) ^ β * ρ ^ β) * X.card := h1.trans (h2.trans h3)
          _ ≤ K * ((2 * (1 + B) ^ 2) ^ β * ρ ^ β) * (4 * Xc.card) := by gcongr
          _ = K₁ * ρ ^ β * Xc.card := by rw [hK₁]; ring
      · rw [Finset.not_nonempty_iff_eq_empty] at hemp
        rw [hemp, Finset.card_empty, Nat.cast_zero] at h1
        have : 0 ≤ K₁ * ρ ^ β * (Xc.card : ℝ) := by
          have := Real.rpow_nonneg hρ0.le β
          positivity
        linarith)
    (fun t => (Wx (g t)).image (chartMap c))
    (by
      intro t ht
      exact Finset.image_subset_image (hWx (g t) (hXcX (hg t ht).1)))
    (by
      intro t ht
      rw [hW'card, Finset.card_image_of_injective _ (chartMap_injective c)]
      have h1 := hWxbig (g t) (hXcX (hg t ht).1)
      have : K * ((Wx (g t)).card : ℝ) ≤ K₁ * ((Wx (g t)).card : ℝ) :=
        mul_le_mul_of_nonneg_right hKK₁ (Nat.cast_nonneg _)
      linarith)
    (fun t => (Yx (g t)).image (fun y => y / chartScale c (g t)))
    (by
      intro t ht
      exact le_trans (by exact_mod_cast Finset.card_image_le) (hYx (g t) (hXcX (hg t ht).1)))
    (by
      intro t ht w' hw'
      obtain ⟨hgX, hgs⟩ := hg t ht
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hw'
      obtain ⟨y, hy, hwy⟩ := hcovx (g t) (hXcX hgX) w hw
      refine ⟨y / chartScale c (g t), Finset.mem_image_of_mem _ hy, ?_⟩
      have hreg := hXcreg (g t) hgX
      have hlam := chartScale_ge c hreg
      have hlam0 : 0 < chartScale c (g t) := by linarith
      have hid := chart_identity c hreg w
      rw [hgs] at hid
      have e : (chartMap c w).1 + t * (chartMap c w).2 - y / chartScale c (g t) =
          (hgt w (g t) - y) / chartScale c (g t) := by
        rw [hid]; field_simp
      rw [e, abs_div, abs_of_pos hlam0, div_le_iff₀ hlam0]
      nlinarith)
  exact key

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
