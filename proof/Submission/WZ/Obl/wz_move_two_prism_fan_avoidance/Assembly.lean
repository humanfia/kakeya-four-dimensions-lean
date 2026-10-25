-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_prism_fan_avoidance.Assembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_prism_fan_avoidance.Geometry
import Submission.WZ.Obl.wz_move_two_prism_fan_avoidance.Coloring
import Submission.WZ.Obl.wz_move_two_prism_fan_avoidance.Trim
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Extraction

/-!
# From normalized prisms to cross-prism avoidance at the same scales

Given `R δ (ε/4) ρ c … 1`, colour the prisms by a local optimum of the same-coarse box
overlaps (`coloring_own_le`) with `⌈4 C δ^(-ε/2)⌉` colours, where `C δ^(-ε/4) |U|` bounds each
overlap row (`overlap_row`); keep the colour class of largest incidence mass and remove from
every kept piece the other kept boxes of its coarse tube (`trim_selected`). This gives
`R δ ε ρ c … 2` for all small `δ`; the volume-gain alternative is never needed.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_prism_fan_avoidance

open Set MeasureTheory

/-- Real form of the overlap of two boxes of a prism family. -/
private def ov {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (D : NData ω ζ δ h ρ c n x v Y) (j j' : Fin D.L) : ℝ :=
  (μ (P D.a (ρ * c) c (D.z j) (D.e j) ∩ P D.a (ρ * c) c (D.z j') (D.e j'))).toReal

private theorem ov_symm {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (D : NData ω ζ δ h ρ c n x v Y) (j j' : Fin D.L) : ov D j j' = ov D j' j := by
  unfold ov
  rw [Set.inter_comm]

private theorem ov_nonneg {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (D : NData ω ζ δ h ρ c n x v Y) (j j' : Fin D.L) : 0 ≤ ov D j j' :=
  ENNReal.toReal_nonneg

/-- The incidence mass of one prism is finite. -/
private theorem prism_mass_ne_top {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} (hδ : 0 < δ) (D : NData ω ζ δ h ρ c n x v Y) (j : Fin D.L) :
    ∑ i, μ (D.W i j) ≠ ⊤ := by
  have ha : 0 < D.a := hδ.trans_le D.lower
  have hrc : 0 < ρ * c := ha.trans_le D.middle
  have hc : 0 < c := hrc.trans_le D.upper
  refine ENNReal.sum_ne_top.mpr fun i _ => ?_
  refine ne_top_of_le_ne_top ?_ (measure_mono ((D.pieces i j).2.1.trans inter_subset_right))
  rw [volume_P ha.le hrc.le hc.le]
  exact ENNReal.ofReal_ne_top

/-- One step of the construction at a fixed scale: an explicit smallness condition on
`t = δ^(ε/4)` turns `R δ (ε/4) ρ c … 1` into `R δ ε ρ c … 2`. -/
theorem avoidance_step {ω ζ δ ε ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε)
    (hsmall : 122880000 * (Real.logb 2 (1 / δ) + 2) ≤ δ ^ (-(ε / 4)))
    (hR : R ω ζ δ (ε / 4) ρ c n x v Y 1) : R ω ζ δ ε ρ c n x v Y 2 := by
  classical
  obtain ⟨D⟩ := ndata_of_R hR
  set η : ℝ := ε / 4 with hη
  have ha : 0 < D.a := hδ.trans_le D.lower
  have hrc : 0 < ρ * c := ha.trans_le D.middle
  have hc : 0 < c := hrc.trans_le D.upper
  have hv0 : 0 < D.a * (ρ * c) * c := by positivity
  set v0 : ℝ := D.a * (ρ * c) * c with hv0def
  -- the small parameter `t = δ^η`
  set t : ℝ := δ ^ η with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos hδ η
  have hneg : δ ^ (-η) = t⁻¹ := Real.rpow_neg hδ.le η
  have hlog : 0 ≤ Real.logb 2 (1 / δ) :=
    Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hδ]; linarith)
  have hsmall' : 122880000 * (Real.logb 2 (1 / δ) + 2) ≤ t⁻¹ := by
    rw [← hneg]; exact hsmall
  have ht2 : t ≤ 1 / 2 := by
    have h2 : 2 ≤ t⁻¹ := le_trans (by nlinarith) hsmall'
    rw [le_inv_comm₀ (by norm_num) ht] at h2
    linarith
  have hε4 : δ ^ ε = t ^ 4 := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    rw [hη]; push_cast; ring
  -- the overlap-row constant
  set Kd : ℕ := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.dyExp 1
    (D.a / (ρ * c)) with hKd
  set Crow : ℝ := 15360000 * ((Kd : ℝ) + 2) with hCrow
  have hKdle : (Kd : ℝ) ≤ Real.logb 2 (1 / δ) := overlap_exp_le hδ D
  have hCrow_pos : 0 < Crow := by positivity
  have hCrow_t : Crow * t ≤ 1 / 8 := by
    have h1 : Crow ≤ 15360000 * (Real.logb 2 (1 / δ) + 2) := by
      rw [hCrow]; gcongr
    have h2 : 8 * Crow ≤ t⁻¹ := by linarith
    have h3 : 8 * Crow * t ≤ t⁻¹ * t := mul_le_mul_of_nonneg_right h2 ht.le
    rw [inv_mul_cancel₀ ht.ne'] at h3
    linarith
  -- each overlap row
  have hrow : ∀ j₀ : Fin D.L,
      ∑ j ∈ Finset.univ.filter (fun j => D.γ j = D.γ j₀), ov D j₀ j ≤ Crow * t⁻¹ * v0 := by
    intro j₀
    have h := overlap_row hδ D j₀
    rw [hneg] at h
    exact h
  -- the colouring
  let wt : Fin D.L → Fin D.L → ℝ := fun j j' => if D.γ j = D.γ j' then ov D j j' else 0
  have hwt_symm : ∀ j j', wt j j' = wt j' j := by
    intro j j'
    simp only [wt]
    by_cases hg : D.γ j = D.γ j'
    · rw [if_pos hg, if_pos hg.symm, ov_symm]
    · rw [if_neg hg, if_neg (Ne.symm hg)]
  set Kcol : ℕ := ⌈4 * Crow / t ^ 2⌉₊ with hKcol
  have hKcol_ge : 4 * Crow / t ^ 2 ≤ Kcol := Nat.le_ceil _
  have hKcol_pos : 0 < Kcol := by
    have : (0 : ℝ) < Kcol := lt_of_lt_of_le (by positivity) hKcol_ge
    exact_mod_cast this
  have hKcol_le : (Kcol : ℝ) ≤ 4 * Crow / t ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  obtain ⟨col, hcol⟩ := coloring_own_le Kcol hKcol_pos wt hwt_symm
  -- the own overlap of every prism is small
  have hown_all : ∀ j, ∑ j' ∈ Finset.univ.filter (fun j' => j' ≠ j ∧ col j' = col j), wt j j' ≤
      t / 4 * v0 := by
    intro j
    have h1 := hcol j
    have h2 : ∑ j' ∈ Finset.univ.filter (fun j' => j' ≠ j), wt j j' ≤
        ∑ j' ∈ Finset.univ.filter (fun j' => D.γ j' = D.γ j), ov D j j' := by
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro j' _
      simp only [wt]
      by_cases hne : j' ≠ j
      · by_cases hg : D.γ j = D.γ j'
        · rw [if_pos hne, if_pos hg, if_pos hg.symm]
        · rw [if_pos hne, if_neg hg]
          split_ifs <;> first | exact le_rfl | exact ov_nonneg D j j'
      · rw [if_neg hne]
        split_ifs <;> first | exact le_rfl | exact ov_nonneg D j j'
    have h3 := (h1.trans h2).trans (hrow j)
    set own := ∑ j' ∈ Finset.univ.filter (fun j' => j' ≠ j ∧ col j' = col j), wt j j'
    have hown_nn : 0 ≤ own :=
      Finset.sum_nonneg fun j' _ => by
        simp only [wt]; split_ifs <;> first | exact le_rfl | exact ov_nonneg D j j'
    -- `Kcol * own ≤ Crow t⁻¹ v0` and `Kcol ≥ 4 Crow / t²`
    have h4 : 4 * Crow / t ^ 2 * own ≤ Crow * t⁻¹ * v0 :=
      (mul_le_mul_of_nonneg_right hKcol_ge hown_nn).trans h3
    have h5 : 4 * Crow / t ^ 2 * own = (4 * Crow) * (own / t ^ 2) := by ring
    rw [h5] at h4
    have h6 : own / t ^ 2 ≤ t⁻¹ * v0 / 4 := by
      have := h4
      have hpos : 0 < 4 * Crow := by positivity
      nlinarith [this]
    have h7 : own ≤ t⁻¹ * v0 / 4 * t ^ 2 := by
      rwa [div_le_iff₀ (by positivity)] at h6
    have h8 : t⁻¹ * v0 / 4 * t ^ 2 = t / 4 * v0 := by
      field_simp
    linarith
  -- the heaviest colour class
  let wgt : Fin D.L → ℝ := fun j => (∑ i, μ (D.W i j)).toReal
  obtain ⟨κ, hκ⟩ := WangZahlLot.Obl.wz_move_two_dense_broad_prisms.weighted_scale_selection
    hKcol_pos Finset.univ col wgt
  set J : Finset (Fin D.L) := Finset.univ.filter (fun j => col j = κ) with hJ
  have hfin := prism_mass_ne_top hδ D
  have hsumJ : ∑ j ∈ J, ∑ i, μ (D.W i j) = ENNReal.ofReal (∑ j ∈ J, wgt j) := by
    rw [ENNReal.ofReal_sum_of_nonneg (f := wgt) (fun j _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_toReal (hfin j)).symm
  have hsumall : ∑ j, ∑ i, μ (D.W i j) = ENNReal.ofReal (∑ j, wgt j) := by
    rw [ENNReal.ofReal_sum_of_nonneg (f := wgt) (fun j _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_toReal (hfin j)).symm
  have hwgtJ : 0 ≤ ∑ j ∈ J, wgt j := Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
  -- the hypotheses of the trimming
  have hown : ∀ j ∈ J, ∑ j' ∈ J.filter (fun j' => j' ≠ j ∧ D.γ j' = D.γ j),
      (μ (P D.a (ρ * c) c (D.z j) (D.e j) ∩ P D.a (ρ * c) c (D.z j') (D.e j'))).toReal ≤
        δ ^ η / 4 * (D.a * (ρ * c) * c) := by
    intro j hj
    have hjκ : col j = κ := (Finset.mem_filter.mp hj).2
    have heq : ∑ j' ∈ J.filter (fun j' => j' ≠ j ∧ D.γ j' = D.γ j),
        (μ (P D.a (ρ * c) c (D.z j) (D.e j) ∩ P D.a (ρ * c) c (D.z j') (D.e j'))).toReal =
        ∑ j' ∈ Finset.univ.filter (fun j' => j' ≠ j ∧ col j' = col j), wt j j' := by
      rw [hJ, Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j' _
      simp only [wt]
      rw [hjκ]
      by_cases h1 : j' ≠ j
      · by_cases h2 : col j' = κ
        · by_cases h3 : D.γ j' = D.γ j
          · rw [if_pos ⟨h2, h1, h3⟩, if_pos ⟨h1, h2⟩, if_pos h3.symm]; rfl
          · rw [if_neg (fun h => h3 h.2.2), if_pos ⟨h1, h2⟩, if_neg (fun h => h3 h.symm)]
        · rw [if_neg (fun h => h2 h.1), if_neg (fun h => h2 h.2)]
      · rw [if_neg (fun h => h1 h.2.1), if_neg (fun h => h1 h.1)]
    rw [heq]
    exact hown_all j
  have hmass : O (δ ^ ε) * ∑ i, μ (Y i) ≤ O (3 / 4) * ∑ j ∈ J, ∑ i, μ (D.W i j) := by
    have hD : O (δ ^ η) * ∑ i, μ (Y i) ≤ ∑ j, ∑ i, μ (D.W i j) := by
      rw [Finset.sum_comm]; exact D.mass
    have hκ' : O (∑ j, wgt j) ≤ O ((Kcol : ℝ) * ∑ j ∈ J, wgt j) := ENNReal.ofReal_le_ofReal hκ
    have hnum : t ^ 3 * Kcol ≤ 3 / 4 := by
      have h1 : t ^ 3 * Kcol ≤ t ^ 3 * (4 * Crow / t ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left hKcol_le (by positivity)
      have h2 : t ^ 3 * (4 * Crow / t ^ 2 + 1) = 4 * (Crow * t) + t ^ 3 := by
        field_simp
      have h3 : t ^ 3 ≤ 1 / 8 := by
        have := pow_le_pow_left₀ ht.le ht2 3
        linarith [show ((1 : ℝ) / 2) ^ 3 = 1 / 8 by norm_num]
      linarith
    calc O (δ ^ ε) * ∑ i, μ (Y i) = O (t ^ 3) * (O (δ ^ η) * ∑ i, μ (Y i)) := by
          rw [hε4, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
      _ ≤ O (t ^ 3) * ∑ j, ∑ i, μ (D.W i j) := mul_le_mul' le_rfl hD
      _ = O (t ^ 3) * O (∑ j, wgt j) := by rw [hsumall]
      _ ≤ O (t ^ 3) * O ((Kcol : ℝ) * ∑ j ∈ J, wgt j) := mul_le_mul' le_rfl hκ'
      _ = O (t ^ 3 * Kcol) * O (∑ j ∈ J, wgt j) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            mul_assoc]
      _ ≤ O (3 / 4) * O (∑ j ∈ J, wgt j) := mul_le_mul' (ENNReal.ofReal_le_ofReal hnum) le_rfl
      _ = O (3 / 4) * ∑ j ∈ J, ∑ i, μ (D.W i j) := by rw [hsumJ]
  have hh' : δ ^ ε ≤ 3 / 4 * δ ^ η := by
    rw [hε4, ← htdef]
    have h3 : t ^ 3 ≤ 1 / 8 := by
      have := pow_le_pow_left₀ ht.le ht2 3
      linarith [show ((1 : ℝ) / 2) ^ 3 = 1 / 8 by norm_num]
    nlinarith [mul_le_mul_of_nonneg_right h3 ht.le]
  obtain ⟨D', hav⟩ := trim_selected hδ hδ1 (by rw [hη]; linarith) D J hown hmass hh'
  exact R_of_ndata D' hav

/-- The construction for all small `δ`, with `η = ε/4`. -/
theorem avoidance_main {ω ζ ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n : ℕ) (x v : Fin n → V)
      (Y : Fin n → Set V) (ρ c : ℝ), R ω ζ δ (ε / 4) ρ c n x v Y 1 →
        R ω ζ δ ε ρ c n x v Y 2 := by
  obtain ⟨d₀, hd₀, hd₀1, hd⟩ := small_delta_log (s := ε / 4) (C := 122880000)
    (by positivity) (by norm_num)
  refine ⟨d₀, hd₀, fun δ hδ hδd n x v Y ρ c hR => ?_⟩
  exact avoidance_step hδ (hδd.trans hd₀1) hε (hd δ hδ hδd) hR

end WangZahlLot.Obl.wz_move_two_prism_fan_avoidance
