import Mathlib

/-!
# A common choice from local lists

Paper `tex-06-isotropic.tex`, Lemma `a05:common-local-choice` (Section 6, used in the
proof of Proposition `a05:qualification`), written here for an arbitrary measure.

Incidences `e` carry a world `wld e` (a countable discrete label), a coordinate
`Z e : Fin D → ℝ` and a value `Y e : Fin q → ℝ`; all norms are sup norms.  At each tested
width `s i` (`1 = s 0 > s 1 > ⋯ > s (L - 1) = r_*`) the values occurring in a half-open
`s i`-cell of `Z` (in one world) meet at most `K i` half-open `s i`-cells.  Then a
restriction of the incidence set keeps, in every world, at least `∏ (4 ^ D * K i)⁻¹` of
the mass, and any two retained incidences of the same world satisfy
`‖Y e - Y e'‖ ≤ 2 (A + B) (‖Z e - Z e'‖ + r_*)`, where `A` bounds the ratios of
consecutive widths and `B` bounds `‖Y‖`.  The retained set is described by the world, `Z`
and `Y` only (whole states are kept or removed), and no measure is renormalized.

The proof is the paper's: at each width, retain in every world the colour class
(cell index mod 4) of largest mass, then in each retained cell the value cell of largest
mass among its at most `K i` candidates.  Distinct cells of one colour are `3 s i`-separated,
so retained incidences at sup-distance at most `s i` lie in the same cell and hence in the
same value cell.
-/

namespace Submission.Lib.K4CommonLocalChoice

open MeasureTheory

noncomputable section

/-- The index of the half-open cell of width `s` containing `z`. -/
def cell {n : ℕ} (s : ℝ) (z : Fin n → ℝ) : Fin n → ℤ := fun j => ⌊z j / s⌋

/-- The colour of a cell index: its coordinates modulo 4. -/
def color {n : ℕ} (c : Fin n → ℤ) : Fin n → ZMod 4 := fun j => (c j : ZMod 4)

theorem measurable_cell {α : Type*} [MeasurableSpace α] {n : ℕ} (s : ℝ)
    {Z : α → Fin n → ℝ} (hZ : Measurable Z) : Measurable fun e => cell s (Z e) := by
  apply Measurable.of_eval
  intro j
  exact ((measurable_pi_apply j).comp hZ).div_const s |>.floor

/-- Two points whose cells have the same colour and which are at sup-distance at most `s`
lie in the same cell. -/
theorem cell_eq_of_color_eq {n : ℕ} {s : ℝ} (hs : 0 < s) {z z' : Fin n → ℝ}
    (hcol : color (cell s z) = color (cell s z')) (hdist : ‖z - z'‖ ≤ s) :
    cell s z = cell s z' := by
  funext j
  have hj : |z j - z' j| ≤ s := by
    have := norm_le_pi_norm (z - z') j
    simp only [Pi.sub_apply, Real.norm_eq_abs] at this
    linarith
  have hc : ((cell s z j : ℤ) : ZMod 4) = ((cell s z' j : ℤ) : ZMod 4) := congr_fun hcol j
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hc
  obtain ⟨k, hk⟩ := hc
  -- floor bounds
  have h1 := Int.floor_le (z j / s)
  have h2 := Int.lt_floor_add_one (z j / s)
  have h3 := Int.floor_le (z' j / s)
  have h4 := Int.lt_floor_add_one (z' j / s)
  simp only [cell] at hk ⊢
  have hzs : z j / s - z' j / s = (z j - z' j) / s := by ring
  have habs : |z j / s - z' j / s| ≤ 1 := by
    rw [hzs, abs_div, abs_of_pos hs, div_le_one hs]
    exact hj
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · exfalso
    have : k ≤ -1 := by omega
    have hdiff : ((⌊z' j / s⌋ - ⌊z j / s⌋ : ℤ) : ℝ) ≤ -4 := by
      rw [hk]; push_cast
      have : (k : ℝ) ≤ -1 := by exact_mod_cast this
      linarith
    push_cast at hdiff
    have := abs_le.mp habs
    linarith
  · rw [hk0] at hk
    simp at hk
    omega
  · exfalso
    have : 1 ≤ k := by omega
    have hdiff : (4 : ℝ) ≤ ((⌊z' j / s⌋ - ⌊z j / s⌋ : ℤ) : ℝ) := by
      rw [hk]; push_cast
      have : (1 : ℝ) ≤ k := by exact_mod_cast this
      linarith
    push_cast at hdiff
    have := abs_le.mp habs
    linarith

/-- Two points in the same cell of width `s` are at sup-distance less than `s`. -/
theorem norm_sub_lt_of_cell_eq {n : ℕ} {s : ℝ} (hs : 0 < s) {y y' : Fin n → ℝ}
    (h : cell s y = cell s y') : ‖y - y'‖ < s := by
  rw [pi_norm_lt_iff hs]
  intro j
  have hj : ⌊y j / s⌋ = ⌊y' j / s⌋ := congr_fun h j
  have h1 := Int.floor_le (y j / s)
  have h2 := Int.lt_floor_add_one (y j / s)
  have h3 := Int.floor_le (y' j / s)
  have h4 := Int.lt_floor_add_one (y' j / s)
  rw [hj] at h1 h2
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hlt : |y j / s - y' j / s| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hzs : y j / s - y' j / s = (y j - y' j) / s := by ring
  rw [hzs, abs_div, abs_of_pos hs, div_lt_one hs] at hlt
  exact hlt

section Selection

variable {α ι : Type*} [MeasurableSpace α] [Countable ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] {D q : ℕ}

/-- The per-world colour classes of a set partition it. -/
private theorem measure_le_card_mul_max_color (μ : Measure α) (Z : α → Fin D → ℝ)
    (hZ : Measurable Z) (s : ℝ) (U : Set α) (hU : MeasurableSet U) :
    ∃ c : Fin D → ZMod 4,
      μ U ≤ (4 : ENNReal) ^ D * μ (U ∩ {e | color (cell s (Z e)) = c}) := by
  classical
  have hmeas : ∀ c : Fin D → ZMod 4, MeasurableSet (U ∩ {e | color (cell s (Z e)) = c}) := by
    intro c
    refine hU.inter ?_
    have : Measurable fun e => color (cell s (Z e)) :=
      measurable_of_countable (color : (Fin D → ℤ) → Fin D → ZMod 4) |>.comp
        (measurable_cell s hZ)
    exact this (measurableSet_singleton c)
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin D → ZMod 4))
    (fun c => μ (U ∩ {e | color (cell s (Z e)) = c})) Finset.univ_nonempty
  refine ⟨c, ?_⟩
  have hU_eq : U = ⋃ c' : Fin D → ZMod 4, U ∩ {e | color (cell s (Z e)) = c'} := by
    ext e; simp
  calc μ U = μ (⋃ c' : Fin D → ZMod 4, U ∩ {e | color (cell s (Z e)) = c'}) := by
        rw [← hU_eq]
    _ ≤ ∑ c' : Fin D → ZMod 4, μ (U ∩ {e | color (cell s (Z e)) = c'}) :=
        measure_iUnion_fintype_le μ _
    _ ≤ ∑ _c' : Fin D → ZMod 4, μ (U ∩ {e | color (cell s (Z e)) = c}) :=
        Finset.sum_le_sum (fun c' _ => hc c' (Finset.mem_univ _))
    _ = (4 : ENNReal) ^ D * μ (U ∩ {e | color (cell s (Z e)) = c}) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp [ZMod.card, nsmul_eq_mul]

/-- In one cell, the value cells (at most `K` of them) partition the incidences. -/
private theorem measure_le_card_mul_max_value (μ : Measure α) (Y : α → Fin q → ℝ)
    (s : ℝ) (U : Set α) (K : ℕ)
    (F : Finset (Fin q → ℤ)) (hF : F.card ≤ K) (hUF : ∀ e ∈ U, cell s (Y e) ∈ F) :
    ∃ m : Fin q → ℤ, μ U ≤ (K : ENNReal) * μ (U ∩ {e | cell s (Y e) = m}) := by
  classical
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · refine ⟨0, ?_⟩
    have : U = ∅ := by
      ext e; simp only [Set.mem_empty_iff_false, iff_false]
      intro he; have := hUF e he; simp [hFe] at this
    simp [this]
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image F
    (fun m => μ (U ∩ {e | cell s (Y e) = m})) hFne
  refine ⟨m, ?_⟩
  have hU_eq : U = ⋃ m' ∈ F, U ∩ {e | cell s (Y e) = m'} := by
    ext e; constructor
    · intro he; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact ⟨cell s (Y e), hUF e he, he, rfl⟩
    · intro he; simp only [Set.mem_iUnion, Set.mem_inter_iff] at he
      obtain ⟨_, _, he, _⟩ := he; exact he
  calc μ U = μ (⋃ m' ∈ F, U ∩ {e | cell s (Y e) = m'}) := by rw [← hU_eq]
    _ ≤ ∑ m' ∈ F, μ (U ∩ {e | cell s (Y e) = m'}) := measure_biUnion_finset_le F _
    _ ≤ ∑ _m' ∈ F, μ (U ∩ {e | cell s (Y e) = m}) := Finset.sum_le_sum (fun m' hm' => hm m' hm')
    _ = (F.card : ENNReal) * μ (U ∩ {e | cell s (Y e) = m}) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K : ENNReal) * μ (U ∩ {e | cell s (Y e) = m}) := by
        gcongr

/-- One width of the selection: keep, in every world, the heaviest colour class of cells,
and in each kept cell the heaviest of its at most `K` value cells. -/
theorem one_scale (μ : Measure α) (wld : α → ι) (hwld : Measurable wld)
    (Z : α → Fin D → ℝ) (hZ : Measurable Z) (Y : α → Fin q → ℝ) (hY : Measurable Y)
    (T : Set α) (hT : MeasurableSet T) (s : ℝ) (K : ℕ)
    (hlist : ∀ (ω : ι) (n : Fin D → ℤ), ∃ F : Finset (Fin q → ℤ), F.card ≤ K ∧
        ∀ e ∈ T, wld e = ω → cell s (Z e) = n → cell s (Y e) ∈ F) :
    ∃ (c : ι → Fin D → ZMod 4) (m : ι → (Fin D → ℤ) → Fin q → ℤ),
      MeasurableSet {e | e ∈ T ∧ color (cell s (Z e)) = c (wld e) ∧
          cell s (Y e) = m (wld e) (cell s (Z e))} ∧
      ∀ ω, μ (T ∩ wld ⁻¹' {ω}) ≤ ((4 : ENNReal) ^ D * K) *
        μ ({e | e ∈ T ∧ color (cell s (Z e)) = c (wld e) ∧
          cell s (Y e) = m (wld e) (cell s (Z e))} ∩ wld ⁻¹' {ω}) := by
  classical
  have hcZ : Measurable fun e => cell s (Z e) := measurable_cell s hZ
  have hcY : Measurable fun e => cell s (Y e) := measurable_cell s hY
  have hW : ∀ ω, MeasurableSet (wld ⁻¹' {ω}) := fun ω => hwld (measurableSet_singleton ω)
  have hZn : ∀ n : Fin D → ℤ, MeasurableSet {e | cell s (Z e) = n} :=
    fun n => hcZ (measurableSet_singleton n)
  -- colour choice
  have hcol := fun ω => measure_le_card_mul_max_color μ Z hZ s (T ∩ wld ⁻¹' {ω})
    (hT.inter (hW ω))
  choose c hc using hcol
  -- value-cell choice
  have hval : ∀ (ω : ι) (n : Fin D → ℤ), ∃ m : Fin q → ℤ,
      μ (T ∩ wld ⁻¹' {ω} ∩ {e | cell s (Z e) = n}) ≤ (K : ENNReal) *
        μ (T ∩ wld ⁻¹' {ω} ∩ {e | cell s (Z e) = n} ∩ {e | cell s (Y e) = m}) := by
    intro ω n
    obtain ⟨F, hF, hFm⟩ := hlist ω n
    exact measure_le_card_mul_max_value μ Y s _ K F hF
      (fun e he => hFm e he.1.1 he.1.2 he.2)
  choose m hm using hval
  refine ⟨c, m, ?_, ?_⟩
  · -- measurability through the countable label `(wld, cell Z, cell Y)`
    have hΦ : Measurable fun e => (wld e, cell s (Z e), cell s (Y e)) :=
      hwld.prodMk (hcZ.prodMk hcY)
    have hG : MeasurableSet {p : ι × (Fin D → ℤ) × (Fin q → ℤ) |
        color p.2.1 = c p.1 ∧ p.2.2 = m p.1 p.2.1} :=
      (Set.to_countable _).measurableSet
    have hset : {e | e ∈ T ∧ color (cell s (Z e)) = c (wld e) ∧
        cell s (Y e) = m (wld e) (cell s (Z e))} = T ∩ (fun e => (wld e, cell s (Z e),
          cell s (Y e))) ⁻¹' {p | color p.2.1 = c p.1 ∧ p.2.2 = m p.1 p.2.1} := by
      ext e; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    rw [hset]; exact hT.inter (hΦ hG)
  · intro ω
    set T' := {e | e ∈ T ∧ color (cell s (Z e)) = c (wld e) ∧
          cell s (Y e) = m (wld e) (cell s (Z e))} with hT'
    -- the kept colour class carries a `4 ^ -D` fraction
    have h1 := hc ω
    -- the kept colour class is the disjoint union of its cells
    have h2 : μ (T ∩ wld ⁻¹' {ω} ∩ {e | color (cell s (Z e)) = c ω}) ≤
        (K : ENNReal) * μ (T' ∩ wld ⁻¹' {ω}) := by
      have hsplit : ∀ V : Set α, V = ⋃ n : Fin D → ℤ, V ∩ {e | cell s (Z e) = n} := by
        intro V; ext e; simp
      have hdisj : ∀ V : Set α, Pairwise (Function.onFun Disjoint
          fun n : Fin D → ℤ => V ∩ {e | cell s (Z e) = n}) := by
        intro V n n' hnn'
        refine Set.disjoint_left.mpr ?_
        intro e he he'
        exact hnn' (he.2.symm.trans he'.2)
      have hTc : MeasurableSet (T ∩ wld ⁻¹' {ω} ∩ {e | color (cell s (Z e)) = c ω}) := by
        refine (hT.inter (hW ω)).inter ?_
        have : Measurable fun e => color (cell s (Z e)) :=
          measurable_of_countable (color : (Fin D → ℤ) → Fin D → ZMod 4) |>.comp hcZ
        exact this (measurableSet_singleton _)
      have hT'm : MeasurableSet T' := by
        have hΦ : Measurable fun e => (wld e, cell s (Z e), cell s (Y e)) :=
          hwld.prodMk (hcZ.prodMk hcY)
        have hG : MeasurableSet {p : ι × (Fin D → ℤ) × (Fin q → ℤ) |
            color p.2.1 = c p.1 ∧ p.2.2 = m p.1 p.2.1} :=
          (Set.to_countable _).measurableSet
        have hset : T' = T ∩ (fun e => (wld e, cell s (Z e),
              cell s (Y e))) ⁻¹' {p | color p.2.1 = c p.1 ∧ p.2.2 = m p.1 p.2.1} := by
          ext e; simp only [hT', Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
        rw [hset]; exact hT.inter (hΦ hG)
      rw [hsplit (T ∩ wld ⁻¹' {ω} ∩ {e | color (cell s (Z e)) = c ω}),
        hsplit (T' ∩ wld ⁻¹' {ω}),
        measure_iUnion (hdisj _) (fun n => hTc.inter (hZn n)),
        measure_iUnion (hdisj _) (fun n => (hT'm.inter (hW ω)).inter (hZn n)),
        ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum (fun n => ?_)
      by_cases hn : color n = c ω
      · -- in a kept cell the retained incidences are those of the chosen value cell
        have hEq1 : T ∩ wld ⁻¹' {ω} ∩ {e | color (cell s (Z e)) = c ω} ∩
            {e | cell s (Z e) = n} = T ∩ wld ⁻¹' {ω} ∩ {e | cell s (Z e) = n} := by
          ext e
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
          · rintro ⟨h, h'⟩; exact ⟨⟨h, by rw [h']; exact hn⟩, h'⟩
        have hEq2 : T' ∩ wld ⁻¹' {ω} ∩ {e | cell s (Z e) = n} =
            T ∩ wld ⁻¹' {ω} ∩ {e | cell s (Z e) = n} ∩ {e | cell s (Y e) = m ω n} := by
          ext e
          simp only [hT', Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
            Set.mem_singleton_iff]
          constructor
          · rintro ⟨⟨⟨hT, _, hY⟩, hw⟩, hz⟩
            refine ⟨⟨⟨hT, hw⟩, hz⟩, ?_⟩
            rw [hY, hw, hz]
          · rintro ⟨⟨⟨hT, hw⟩, hz⟩, hY⟩
            refine ⟨⟨⟨hT, ?_, ?_⟩, hw⟩, hz⟩
            · rw [hw, hz]; exact hn
            · rw [hY, hw, hz]
        rw [hEq1, hEq2]
        exact hm ω n
      · -- a cell of another colour contributes nothing on the left
        have : T ∩ wld ⁻¹' {ω} ∩ {e | color (cell s (Z e)) = c ω} ∩
            {e | cell s (Z e) = n} = ∅ := by
          ext e
          constructor
          · rintro ⟨⟨_, hc'⟩, hz⟩
            simp only [Set.mem_ofPred_eq] at hc' hz
            rw [hz] at hc'
            exact absurd hc' hn
          · intro h; exact absurd h (Set.notMem_empty e)
        rw [this, measure_empty]
        exact zero_le
    calc μ (T ∩ wld ⁻¹' {ω})
        ≤ (4 : ENNReal) ^ D * μ (T ∩ wld ⁻¹' {ω} ∩ {e | color (cell s (Z e)) = c ω}) := h1
      _ ≤ (4 : ENNReal) ^ D * ((K : ENNReal) * μ (T' ∩ wld ⁻¹' {ω})) := by gcongr
      _ = ((4 : ENNReal) ^ D * K) * μ (T' ∩ wld ⁻¹' {ω}) := by ring

/-- The selection over the first `k` widths. -/
theorem first_scales (μ : Measure α) (wld : α → ι) (hwld : Measurable wld)
    (Z : α → Fin D → ℝ) (hZ : Measurable Z) (Y : α → Fin q → ℝ) (hY : Measurable Y)
    (Ω : Set α) (hΩ : MeasurableSet Ω) (s : ℕ → ℝ) (K : ℕ → ℕ)
    (hspos : ∀ i, 0 < s i)
    (hlist : ∀ (i : ℕ) (ω : ι) (n : Fin D → ℤ), ∃ F : Finset (Fin q → ℤ), F.card ≤ K i ∧
        ∀ e ∈ Ω, wld e = ω → cell (s i) (Z e) = n → cell (s i) (Y e) ∈ F) :
    ∀ k : ℕ, ∃ (S : Set α) (P : ι → (Fin D → ℝ) → (Fin q → ℝ) → Prop),
      MeasurableSet S ∧ (∀ e, e ∈ S ↔ e ∈ Ω ∧ P (wld e) (Z e) (Y e)) ∧
      (∀ ω, μ (Ω ∩ wld ⁻¹' {ω}) ≤
        (∏ i ∈ Finset.range k, ((4 : ENNReal) ^ D * K i)) * μ (S ∩ wld ⁻¹' {ω})) ∧
      (∀ i < k, ∀ e ∈ S, ∀ e' ∈ S, wld e = wld e' → ‖Z e - Z e'‖ ≤ s i →
        ‖Y e - Y e'‖ < s i) := by
  intro k
  induction k with
  | zero =>
    refine ⟨Ω, fun _ _ _ => True, hΩ, fun e => by simp, fun ω => by simp, ?_⟩
    intro i hi; omega
  | succ k ih =>
    obtain ⟨S, P, hS, hSP, hmass, hcmp⟩ := ih
    have hSΩ : ∀ e ∈ S, e ∈ Ω := fun e he => ((hSP e).mp he).1
    obtain ⟨c, m, hT'm, hT'mass⟩ := one_scale μ wld hwld Z hZ Y hY S hS (s k) (K k)
      (fun ω n => by
        obtain ⟨F, hF, hFm⟩ := hlist k ω n
        exact ⟨F, hF, fun e he => hFm e (hSΩ e he)⟩)
    refine ⟨{e | e ∈ S ∧ color (cell (s k) (Z e)) = c (wld e) ∧
          cell (s k) (Y e) = m (wld e) (cell (s k) (Z e))},
      fun ω z y => P ω z y ∧ color (cell (s k) z) = c ω ∧ cell (s k) y = m ω (cell (s k) z),
      hT'm, ?_, ?_, ?_⟩
    · intro e
      simp only [Set.mem_ofPred_eq, hSP e]
      tauto
    · intro ω
      calc μ (Ω ∩ wld ⁻¹' {ω})
          ≤ (∏ i ∈ Finset.range k, ((4 : ENNReal) ^ D * K i)) * μ (S ∩ wld ⁻¹' {ω}) :=
            hmass ω
        _ ≤ (∏ i ∈ Finset.range k, ((4 : ENNReal) ^ D * K i)) *
            (((4 : ENNReal) ^ D * K k) *
              μ ({e | e ∈ S ∧ color (cell (s k) (Z e)) = c (wld e) ∧
                cell (s k) (Y e) = m (wld e) (cell (s k) (Z e))} ∩ wld ⁻¹' {ω})) := by
            gcongr
            exact hT'mass ω
        _ = (∏ i ∈ Finset.range (k + 1), ((4 : ENNReal) ^ D * K i)) *
              μ ({e | e ∈ S ∧ color (cell (s k) (Z e)) = c (wld e) ∧
                cell (s k) (Y e) = m (wld e) (cell (s k) (Z e))} ∩ wld ⁻¹' {ω}) := by
            rw [Finset.prod_range_succ]; ring
    · intro i hi e he e' he' hw hd
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact hcmp i hi e he.1 e' he'.1 hw hd
      · subst hi
        have hcol : color (cell (s i) (Z e)) = color (cell (s i) (Z e')) := by
          rw [he.2.1, he'.2.1, hw]
        have hcell := cell_eq_of_color_eq (hspos i) hcol hd
        have hYc : cell (s i) (Y e) = cell (s i) (Y e') := by
          rw [he.2.2, he'.2.2, hw, hcell]
        exact norm_sub_lt_of_cell_eq (hspos i) hYc

/-- **A common choice from local lists** (paper Lemma `a05:common-local-choice`).

Widths `1 = s 0 > s 1 > ⋯ > s (L - 1)`, ratios `s i ≤ A * s (i + 1)` (`1 ≤ A`), values
bounded by `B` on the incidence set `Ω`, and at width `s i` the values in each half-open
`s i`-cell of `Z` (in each world) meet at most `K i` value cells.  There is a measurable
`S ⊆ Ω`, described by the world, `Z` and `Y` only, keeping in every world at least
`∏ (4 ^ D * K i)⁻¹` of the mass, on which values of one world are Lipschitz in `Z` up to
the finest width:
`‖Y e - Y e'‖ ≤ 2 * (A + B) * (‖Z e - Z e'‖ + s (L - 1))` (sup norms). -/
theorem common_local_choice (μ : Measure α) (wld : α → ι) (hwld : Measurable wld)
    (Z : α → Fin D → ℝ) (hZ : Measurable Z) (Y : α → Fin q → ℝ) (hY : Measurable Y)
    (Ω : Set α) (hΩ : MeasurableSet Ω) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ e ∈ Ω, ‖Y e‖ ≤ B)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (K : ℕ → ℕ) (A : ℝ) (hA1 : 1 ≤ A)
    (hs0 : s 0 = 1) (hspos : ∀ i, 0 < s i) (hA : ∀ i, i + 1 < L → s i ≤ A * s (i + 1))
    (hlist : ∀ i < L, ∀ (ω : ι) (n : Fin D → ℤ), ∃ F : Finset (Fin q → ℤ), F.card ≤ K i ∧
        ∀ e ∈ Ω, wld e = ω → cell (s i) (Z e) = n → cell (s i) (Y e) ∈ F) :
    ∃ (S : Set α) (P : ι → (Fin D → ℝ) → (Fin q → ℝ) → Prop),
      MeasurableSet S ∧ S ⊆ Ω ∧ (∀ e, e ∈ S ↔ e ∈ Ω ∧ P (wld e) (Z e) (Y e)) ∧
      (∀ ω, μ (Ω ∩ wld ⁻¹' {ω}) ≤
        (∏ i ∈ Finset.range L, ((4 : ENNReal) ^ D * K i)) * μ (S ∩ wld ⁻¹' {ω})) ∧
      (∀ e ∈ S, ∀ e' ∈ S, wld e = wld e' →
        ‖Y e - Y e'‖ ≤ 2 * (A + B) * (‖Z e - Z e'‖ + s (L - 1))) := by
  classical
  -- extend the list hypothesis trivially beyond `L` (those widths are not used)
  let K' : ℕ → ℕ := fun i => if i < L then K i else K 0
  have hlist' : ∀ (i : ℕ) (ω : ι) (n : Fin D → ℤ), ∃ F : Finset (Fin q → ℤ),
      F.card ≤ K' i ∧ ∀ e ∈ Ω, wld e = ω → cell (s (if i < L then i else 0)) (Z e) = n →
        cell (s (if i < L then i else 0)) (Y e) ∈ F := by
    intro i ω n
    by_cases hi : i < L
    · simpa [K', hi] using hlist i hi ω n
    · simpa [K', hi] using hlist 0 (by omega) ω n
  obtain ⟨S, P, hS, hSP, hmass, hcmp⟩ := first_scales μ wld hwld Z hZ Y hY Ω hΩ
    (fun i => s (if i < L then i else 0)) K' (fun i => hspos _) hlist' L
  have hprod : ∏ i ∈ Finset.range L, ((4 : ENNReal) ^ D * K' i) =
      ∏ i ∈ Finset.range L, ((4 : ENNReal) ^ D * K i) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have : i < L := Finset.mem_range.mp hi
    simp [K', this]
  have hcmp' : ∀ i < L, ∀ e ∈ S, ∀ e' ∈ S, wld e = wld e' → ‖Z e - Z e'‖ ≤ s i →
      ‖Y e - Y e'‖ < s i := by
    intro i hi e he e' he' hw hd
    have := hcmp i hi e he e' he' hw (by simpa [hi] using hd)
    simpa [hi] using this
  refine ⟨S, P, hS, fun e he => ((hSP e).mp he).1, hSP, fun ω => by rw [← hprod]; exact hmass ω,
    ?_⟩
  intro e he e' he' hw
  have hBe : ‖Y e‖ ≤ B := hB e ((hSP e).mp he).1
  have hBe' : ‖Y e'‖ ≤ B := hB e' ((hSP e').mp he').1
  set d := ‖Z e - Z e'‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hr : 0 < s (L - 1) := hspos _
  by_cases hd1 : d ≤ 1
  · -- the largest tested width still above `d`
    set i₀ := Nat.findGreatest (fun i => d ≤ s i) (L - 1) with hi₀
    have hP0 : d ≤ s 0 := by rw [hs0]; exact hd1
    have hspec : d ≤ s i₀ := Nat.findGreatest_spec (P := fun i => d ≤ s i) (Nat.zero_le _) hP0
    have hle : i₀ ≤ L - 1 := Nat.findGreatest_le _
    have hlt : ‖Y e - Y e'‖ < s i₀ := hcmp' i₀ (by omega) e he e' he' hw hspec
    rcases Nat.lt_or_ge i₀ (L - 1) with hlt' | hge
    · have hnot : ¬ d ≤ s (i₀ + 1) :=
        Nat.findGreatest_is_greatest (P := fun i => d ≤ s i) (Nat.lt_succ_self _)
          (by omega)
      push Not at hnot
      have hratio : s i₀ ≤ A * s (i₀ + 1) := hA i₀ (by omega)
      have : s i₀ ≤ A * d := hratio.trans (by gcongr)
      nlinarith
    · have : i₀ = L - 1 := le_antisymm hle hge
      rw [this] at hlt
      nlinarith
  · push Not at hd1
    have h2B : ‖Y e - Y e'‖ ≤ 2 * B := by
      calc ‖Y e - Y e'‖ ≤ ‖Y e‖ + ‖Y e'‖ := norm_sub_le _ _
        _ ≤ 2 * B := by linarith
    nlinarith

end Selection

end

end Submission.Lib.K4CommonLocalChoice
