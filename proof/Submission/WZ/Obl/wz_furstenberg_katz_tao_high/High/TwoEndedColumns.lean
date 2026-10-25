-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.TwoEndedColumns.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/TwoEndedColumns.lean (c552951).
import Mathlib

/-!
# Two-ended classes in column form

The two-endedness hypothesis of x0665's `tube_two_ends_false` asks, for each line `j` of a coarse
tube, that the columns met by `j` in a window of length `ρ` are at most `A ρ^β` times all the
columns of `j`. `columns_two_ended` derives it from

* the `β`-Frostman bound of the labels of `j` (`#{q : dist (p q) (p q₀) ≤ R} ≤ B R^β #L` for
  `R ≥ R₀`; x0672's `LinePins` / `HighConfig.line_frostman`);
* "columns close ⟹ pins close" along the line (`|col - col'| ≤ D → dist ≤ α D + α'`);
* the balance of the labels of `j` per grid cell (`N_lo ≤ #(cell) ≤ N_hi` on occupied cells);
* the grid geometry: a cell meets at most `A₁` columns, a column meets at most `A₂` cells, and
  labels in one cell have columns within `E`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

/-- Counting a finset fibrewise against a real bound per fibre. -/
theorem cls_card_le_sum' {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    {g : α → β} (hg : ∀ a ∈ s, g a ∈ t) {w : β → ℝ}
    (hw : ∀ b ∈ t, ((s.filter (fun a => g a = b)).card : ℝ) ≤ w b) :
    (s.card : ℝ) ≤ ∑ b ∈ t, w b := by
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (fun a ha => hg a ha)]
  push_cast
  exact Finset.sum_le_sum hw

/-- **Two-ended columns.** -/
theorem columns_two_ended {X ι : Type*} [PseudoMetricSpace X] [DecidableEq ι]
    (L : Finset (X × X))
    (col : X → ℝ) (cell : X → ι) {B β R₀ α α' Nlo Nhi A₁ A₂ E ρ z : ℝ}
    (hB : 0 ≤ B) (hNlo : 0 < Nlo) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hE : 0 ≤ E)
    (hR0 : 0 ≤ R₀) (hR : R₀ ≤ α * (2 * (ρ + E)) + α')
    (hFr : ∀ q₀ ∈ L, ∀ R : ℝ, R₀ ≤ R →
      ((L.filter (fun q => dist q.1 q₀.1 ≤ R)).card : ℝ) ≤ B * R ^ β * L.card)
    (hcl : ∀ q ∈ L, ∀ q' ∈ L, ∀ D : ℝ, |col q.1 - col q'.1| ≤ D → dist q.1 q'.1 ≤ α * D + α')
    (hlo : ∀ q ∈ L, Nlo ≤ ((L.filter (fun q' => cell q'.1 = cell q.1)).card : ℝ))
    (hhi : ∀ q ∈ L, ((L.filter (fun q' => cell q'.1 = cell q.1)).card : ℝ) ≤ Nhi)
    (hcells_col : ∀ q ∈ L,
      (((L.filter (fun q' => cell q'.1 = cell q.1)).image (fun q' => col q'.1)).card : ℝ) ≤ A₁)
    (hcol_cells : ∀ q ∈ L,
      (((L.filter (fun q' => col q'.1 = col q.1)).image (fun q' => cell q'.1)).card : ℝ) ≤ A₂)
    (hext : ∀ q ∈ L, ∀ q' ∈ L, cell q.1 = cell q'.1 → |col q.1 - col q'.1| ≤ E) :
    (((L.image (fun q => col q.1)).filter (fun y => |y - z| ≤ ρ)).card : ℝ) ≤
      A₁ * (B * (α * (2 * (ρ + E)) + α') ^ β * (Nhi / Nlo) * A₂) *
        (L.image (fun q => col q.1)).card := by
  classical
  set cols := L.image (fun q => col q.1) with hcols
  set Yz := cols.filter (fun y => |y - z| ≤ ρ) with hYz
  set R := α * (2 * (ρ + E)) + α' with hRdef
  have hRnn : 0 ≤ R := hR0.trans hR
  rcases Yz.eq_empty_or_nonempty with hE0 | ⟨y₀, hy₀⟩
  · rw [hE0, Finset.card_empty, Nat.cast_zero]
    rcases L.eq_empty_or_nonempty with hL0 | ⟨q, hq⟩
    · rw [hcols, hL0, Finset.image_empty, Finset.card_empty, Nat.cast_zero, mul_zero]
    · have hNhi : 0 ≤ Nhi := (hNlo.le.trans (hlo q hq)).trans (hhi q hq)
      have := Real.rpow_nonneg hRnn β
      positivity
  obtain ⟨hy₀c, hy₀z⟩ := Finset.mem_filter.mp hy₀
  obtain ⟨q₀, hq₀, hq₀y⟩ := Finset.mem_image.mp hy₀c
  have hNhi : 0 ≤ Nhi := (hNlo.le.trans (hlo q₀ hq₀)).trans (hhi q₀ hq₀)
  -- step 1: the columns near `z` are covered by the columns of few cells
  set Cz := (L.filter (fun q => |col q.1 - z| ≤ ρ)).image (fun q => cell q.1) with hCz
  have hstep1 : (Yz.card : ℝ) ≤ (Cz.card : ℝ) * A₁ := by
    have hsub : Yz ⊆ Cz.biUnion
        (fun c => (L.filter (fun q' => cell q'.1 = c)).image (fun q' => col q'.1)) := by
      intro y hy
      obtain ⟨hyc, hyz⟩ := Finset.mem_filter.mp hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hyc
      exact Finset.mem_biUnion.mpr ⟨cell q.1, Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨hq, hyz⟩, rfl⟩,
        Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩, rfl⟩⟩
    have h1 := (Nat.cast_le (α := ℝ)).mpr ((Finset.card_le_card hsub).trans
      Finset.card_biUnion_le)
    push_cast at h1
    refine h1.trans ?_
    have : ∑ c ∈ Cz, (((L.filter (fun q' => cell q'.1 = c)).image
        (fun q' => col q'.1)).card : ℝ) ≤ ∑ _c ∈ Cz, A₁ := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
      exact hcells_col q (Finset.mem_filter.mp hq).1
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  -- step 2: each such cell holds at least `Nlo` labels, all with column within `ρ + E` of `z`
  set Lz := L.filter (fun q => |col q.1 - z| ≤ ρ + E) with hLz
  have hstep2 : (Cz.card : ℝ) * Nlo ≤ (Lz.card : ℝ) := by
    have hdisj : (Cz : Set ι).PairwiseDisjoint (fun c => L.filter (fun q' => cell q'.1 = c)) := by
      intro c _ c' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro q hq hq'
      exact hne ((Finset.mem_filter.mp hq).2.symm.trans (Finset.mem_filter.mp hq').2)
    have hsub : Cz.biUnion (fun c => L.filter (fun q' => cell q'.1 = c)) ⊆ Lz := by
      intro q hq
      obtain ⟨c, hc, hqc⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨q₁, hq₁, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨hq₁L, hq₁z⟩ := Finset.mem_filter.mp hq₁
      obtain ⟨hqL, hqcell⟩ := Finset.mem_filter.mp hqc
      refine Finset.mem_filter.mpr ⟨hqL, ?_⟩
      have he := hext q hqL q₁ hq₁L hqcell
      calc |col q.1 - z| = |(col q.1 - col q₁.1) + (col q₁.1 - z)| := by ring_nf
        _ ≤ |col q.1 - col q₁.1| + |col q₁.1 - z| := abs_add_le _ _
        _ ≤ ρ + E := by linarith
    have h1 := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
    rw [Finset.card_biUnion hdisj] at h1
    push_cast at h1
    refine le_trans ?_ h1
    have : ∑ _c ∈ Cz, Nlo ≤ ∑ c ∈ Cz, ((L.filter (fun q' => cell q'.1 = c)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
      exact hlo q (Finset.mem_filter.mp hq).1
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  -- step 3: these labels are all close to `q₀`
  have hstep3 : (Lz.card : ℝ) ≤ B * R ^ β * L.card := by
    have hsub : Lz ⊆ L.filter (fun q => dist q.1 q₀.1 ≤ R) := by
      intro q hq
      obtain ⟨hqL, hqz⟩ := Finset.mem_filter.mp hq
      refine Finset.mem_filter.mpr ⟨hqL, hcl q hqL q₀ hq₀ (2 * (ρ + E)) ?_⟩
      rw [hq₀y]
      calc |col q.1 - y₀| = |(col q.1 - z) - (y₀ - z)| := by ring_nf
        _ ≤ |col q.1 - z| + |y₀ - z| := abs_sub _ _
        _ ≤ 2 * (ρ + E) := by linarith
    exact ((Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)).trans (hFr q₀ hq₀ R hR)
  -- step 4: all labels lie in few cells per column
  have hstep4 : (L.card : ℝ) ≤ (cols.card : ℝ) * (A₂ * Nhi) := by
    have h1 : (L.card : ℝ) ≤ ∑ y ∈ cols, A₂ * Nhi := by
      refine cls_card_le_sum' (s := L) (t := cols) (g := fun q => col q.1)
        (fun q hq => Finset.mem_image_of_mem (fun q : X × X => col q.1) hq) ?_
      intro y hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      -- the labels of the column lie in at most `A₂` cells, each with at most `Nhi` labels
      have hsub : L.filter (fun q' => col q'.1 = col q.1) ⊆
          ((L.filter (fun q' => col q'.1 = col q.1)).image (fun q' => cell q'.1)).biUnion
            (fun c => L.filter (fun q'' => cell q''.1 = c)) := by
        intro q' hq'
        exact Finset.mem_biUnion.mpr ⟨cell q'.1, Finset.mem_image_of_mem _ hq',
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq').1, rfl⟩⟩
      have h2 := (Nat.cast_le (α := ℝ)).mpr ((Finset.card_le_card hsub).trans
        Finset.card_biUnion_le)
      push_cast at h2
      refine h2.trans ?_
      have h3 : ∑ c ∈ (L.filter (fun q' => col q'.1 = col q.1)).image (fun q' => cell q'.1),
          ((L.filter (fun q'' => cell q''.1 = c)).card : ℝ) ≤
          ∑ _c ∈ (L.filter (fun q' => col q'.1 = col q.1)).image (fun q' => cell q'.1), Nhi := by
        apply Finset.sum_le_sum
        intro c hc
        obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hc
        exact hhi q' (Finset.mem_filter.mp hq').1
      rw [Finset.sum_const, nsmul_eq_mul] at h3
      refine h3.trans ?_
      have h4 := hcol_cells q hq
      nlinarith
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    exact h1
  -- combine
  have hBR : 0 ≤ B * R ^ β := mul_nonneg hB (Real.rpow_nonneg hRnn β)
  have hchain : (Cz.card : ℝ) * Nlo ≤ B * R ^ β * ((cols.card : ℝ) * (A₂ * Nhi)) :=
    hstep2.trans (hstep3.trans (mul_le_mul_of_nonneg_left hstep4 hBR))
  have hCz : (Cz.card : ℝ) ≤ B * R ^ β * ((cols.card : ℝ) * (A₂ * Nhi)) / Nlo := by
    rw [le_div_iff₀ hNlo]; exact hchain
  calc (Yz.card : ℝ) ≤ (Cz.card : ℝ) * A₁ := hstep1
    _ ≤ (B * R ^ β * ((cols.card : ℝ) * (A₂ * Nhi)) / Nlo) * A₁ :=
        mul_le_mul_of_nonneg_right hCz hA₁
    _ = A₁ * (B * R ^ β * (Nhi / Nlo) * A₂) * (cols.card : ℝ) := by
        field_simp

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
