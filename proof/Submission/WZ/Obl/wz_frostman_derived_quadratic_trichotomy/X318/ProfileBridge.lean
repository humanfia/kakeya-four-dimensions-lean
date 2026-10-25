-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.ProfileBridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.RoundBox
-- Copied from session x0338 (o070 branch, commit b25dfdc, file ProfileBridge.lean), namespace renamed.

/-!
# From grid populations to the round-box constant and the profile bounds

For a family on nested (foot, direction) grids (o038/x0305's `lineCell (ρ_k / 20)` with
`ρ_k = 2 δ L^k`):

* `roundBox_of_levels`: if every level-`k` cell of a fibre `F` holds at most `P k` tubes,
  `P k δ² ≤ D ρ_k²` at every level up to the fibre's own level, and `|F| δ² ≤ D ρ_top²`, then
  every box `e '' {|z 0| ≤ a, |z 1| ≤ b, |z 2| ≤ 2}` with `δ ≤ a ≤ b ≤ Λ a` holds at most
  `K a b / δ²` tubes of `F`, `K = 400 · 122³ · 16³ · L² Λ D`.  This is the round-box hypothesis
  of x0318's `fibre_dichotomy` (o070/x0318 `FibreDichotomy.lean`).
* `card_fibre_le_of_nest`, `card_fibre_le_subcells`, `card_subcells_le`,
  `card_fibre_le_of_frostman`: populations grow with the cell size, a coarse population is at most
  `(4 s/s' + 2)⁶` fine populations, and global Frostman bounds a population by the volume of a
  convex set holding the cell.  These give the step and lower bounds of the cell-count profile
  `G` of x0318's `profile_scale_choice` / x0305's `profile_dichotomy`.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set Metric MeasureTheory

/-- Points of one grid cell of size `s` are within `2 s` (o038/x0305's
`norm_sub_lt_of_cellIdx_eq`). -/
lemma norm_sub_lt_of_gridCell_eq {s : ℝ} (hs : 0 < s) {y y' : Space}
    (h : gridCell s y = gridCell s y') : ‖y - y'‖ < 2 * s := by
  have hc : ∀ c, |y c - y' c| < s := by
    intro c
    have h' := congrFun h c
    simp only [gridCell] at h'
    have := Int.abs_sub_lt_one_of_floor_eq_floor h'
    rw [← sub_div, abs_div, abs_of_pos hs, div_lt_one hs] at this
    exact this
  have hsq : ‖y - y'‖ ^ 2 < (2 * s) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ c, ‖(y - y') c‖ ^ 2 < ∑ _c : Fin 3, s ^ 2 := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro c _
          rw [PiLp.sub_apply, Real.norm_eq_abs]
          have := hc c
          nlinarith [abs_nonneg (y c - y' c)]
      _ = 3 * s ^ 2 := by simp
      _ ≤ (2 * s) ^ 2 := by nlinarith
  nlinarith [norm_nonneg (y - y')]

/-- **Subcell count.**  The lines of one cell of size `s` meet at most `(4 s / s' + 2)⁶` cells of
size `s'`. -/
theorem card_subcells_le {ι : Type*} (S : Finset ι) (x v : ι → Space) {s s' : ℝ}
    (hs : 0 < s) (hs' : 0 < s')
    (hcell : ∀ i ∈ S, ∀ j ∈ S, lineGridCell s (x i) (v i) = lineGridCell s (x j) (v j)) :
    ((S.image (fun i => lineGridCell s' (x i) (v i))).card : ℝ) ≤ (4 * s / s' + 2) ^ 6 := by
  have h := card_lineCells_le S (fun i => lineFoot (x i) (v i)) v hs' (by positivity : (0 : ℝ) ≤ 2 * s)
    (by positivity : (0 : ℝ) ≤ 2 * s)
    (fun i hi j hj => (norm_sub_lt_of_gridCell_eq hs
      (congrArg Prod.fst (hcell i hi j hj))).le)
    (fun i hi j hj => (norm_sub_lt_of_gridCell_eq hs
      (congrArg Prod.snd (hcell i hi j hj))).le)
  have e : (2 * (2 * s) / s' + 2) ^ 3 * (2 * (2 * s) / s' + 2) ^ 3 = (4 * s / s' + 2) ^ 6 := by
    ring
  rw [← e]
  exact h

/-- Populations grow with the cell: a fine cell lies in its coarse cell. -/
lemma card_fibre_le_of_nest {ι α β : Type*} [DecidableEq α] [DecidableEq β] (S : Finset ι)
    (κf : ι → α) (κc : ι → β) (hnest : ∀ i j, κf i = κf j → κc i = κc j) (i : ι) :
    (S.filter (fun j => κf j = κf i)).card ≤ (S.filter (fun j => κc j = κc i)).card :=
  Finset.card_le_card (fun j hj => by
    obtain ⟨hjS, hji⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hjS, hnest j i hji⟩)

/-- A coarse population is at most the number of its fine cells times a bound `P` on the fine
populations. -/
lemma card_fibre_le_subcells {ι α β : Type*} [DecidableEq α] [DecidableEq β] (S : Finset ι)
    (κf : ι → α) (κc : ι → β) (P : ℝ)
    (hP : ∀ j ∈ S, ((S.filter (fun j' => κf j' = κf j)).card : ℝ) ≤ P) (i : ι) :
    ((S.filter (fun j => κc j = κc i)).card : ℝ) ≤
      (((S.filter (fun j => κc j = κc i)).image κf).card : ℝ) * P := by
  classical
  set C := S.filter (fun j => κc j = κc i) with hC
  rw [Finset.card_eq_sum_card_image κf C]
  push_cast
  calc ∑ g ∈ C.image κf, ((C.filter (fun j => κf j = g)).card : ℝ)
      ≤ ∑ _g ∈ C.image κf, P := by
        apply Finset.sum_le_sum
        intro g hg
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hg
        have hjS : j ∈ S := (Finset.mem_filter.mp hj).1
        refine le_trans ?_ (hP j hjS)
        exact_mod_cast Finset.card_le_card (fun j' hj' => by
          obtain ⟨hj'C, hj'j⟩ := Finset.mem_filter.mp hj'
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj'C).1, hj'j⟩)
    _ = ((C.image κf).card : ℝ) * P := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The step bound of the population profile on nested line grids: a cell of size `s` holds at
most `(4 s / s' + 2)⁶ P` tubes when the cells of size `s'` hold at most `P`. -/
theorem card_lineCell_le_subcells {ι : Type*} (S : Finset ι) (x v : ι → Space) {s s' P : ℝ}
    (hs : 0 < s) (hs' : 0 < s') (hP0 : 0 ≤ P)
    (hP : ∀ j ∈ S, ((S.filter (fun j' => lineGridCell s' (x j') (v j') =
      lineGridCell s' (x j) (v j))).card : ℝ) ≤ P) (i : ι) :
    ((S.filter (fun j => lineGridCell s (x j) (v j) = lineGridCell s (x i) (v i))).card : ℝ) ≤
      (4 * s / s' + 2) ^ 6 * P := by
  classical
  have h1 := card_fibre_le_subcells S (fun j => lineGridCell s' (x j) (v j))
    (fun j => lineGridCell s (x j) (v j)) P hP i
  have h2 := card_subcells_le (S.filter (fun j => lineGridCell s (x j) (v j) =
    lineGridCell s (x i) (v i))) x v hs hs' (fun j hj j' hj' => by
      rw [(Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hj').2])
  calc _ ≤ _ := h1
    _ ≤ (4 * s / s' + 2) ^ 6 * P := mul_le_mul_of_nonneg_right h2 hP0

open Classical in
/-- Global Frostman bounds a population by the volume of a convex set holding the cell. -/
theorem card_fibre_le_of_frostman {n : ℕ} (x v : Fin n → Space) (S : Finset (Fin n))
    {α : Type*} [DecidableEq α] (κ : Fin n → α) (i : Fin n) {δ K V : ℝ} (W : Set Space)
    (hK : 0 ≤ K) (hV : 0 ≤ V) (hW : Convex ℝ W) (hVW : volume W ≤ ENNReal.ofReal V)
    (hsub : ∀ j ∈ S, κ j = κ i → Tube δ (x j) (v j) ⊆ W)
    (hF : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((S.filter (fun j => Tube δ (x j) (v j) ⊆ U)).card : ℝ) ≤
        ENNReal.ofReal (K * S.card) * volume U) :
    ((S.filter (fun j => κ j = κ i)).card : ℝ) ≤ K * S.card * V := by
  have hle : (S.filter (fun j => κ j = κ i)).card ≤
      (S.filter (fun j => Tube δ (x j) (v j) ⊆ W)).card :=
    Finset.card_le_card (fun j hj => by
      obtain ⟨hjS, hji⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hjS, hsub j hjS hji⟩)
  have h := hF W hW
  have h2 : ENNReal.ofReal ((S.filter (fun j => Tube δ (x j) (v j) ⊆ W)).card : ℝ) ≤
      ENNReal.ofReal (K * S.card * V) := by
    calc _ ≤ ENNReal.ofReal (K * S.card) * volume W := h
      _ ≤ ENNReal.ofReal (K * S.card) * ENNReal.ofReal V := by gcongr
      _ = ENNReal.ofReal (K * S.card * V) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
  exact (Nat.cast_le.mpr hle).trans this

open Classical in
/-- **Round-box constant from the populations.**  Let `F` be a set of unit `δ`-tubes in the unit
ball with no antipodal pair, and radii `ρ 0 ≤ … ≤ ρ top` with `ρ 0 ≤ 20 L δ`, ratio at most `L`
and `ρ top ≤ 2`.  If every level-`k` cell (`lineGridCell (ρ k / 20)`) of `F` holds at most `P k`
tubes, `P k δ² ≤ D (ρ k)²` for `k ≤ top`, and `|F| δ² ≤ D (ρ top)²`, then every box
`e '' {|z 0| ≤ a, |z 1| ≤ b, |z 2| ≤ 2}` with `δ ≤ a ≤ b ≤ Λ a` holds at most
`400 · 122³ · 16³ · L² Λ D · a b / δ²` tubes of `F`. -/
theorem roundBox_of_levels {n : ℕ} (x v : Fin n → Space) (F : Finset (Fin n))
    {δ L D Λ : ℝ} (ρ P : ℕ → ℝ) (top : ℕ)
    (hδ : 0 < δ) (hL : 1 ≤ L) (hD : 0 ≤ D) (hΛ : 1 ≤ Λ)
    (hρpos : ∀ k, 0 < ρ k) (hρ0 : ρ 0 ≤ 20 * L * δ) (hρstep : ∀ k, ρ (k + 1) ≤ L * ρ k)
    (hρtop : ρ top ≤ 2)
    (hv : ∀ i ∈ F, ‖v i‖ = 1) (hball : ∀ i ∈ F, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hanti : ∀ i ∈ F, ∀ j ∈ F, 1 ≤ ‖v i + v j‖)
    (hP0 : ∀ k ≤ top, 0 ≤ P k)
    (hpop : ∀ k ≤ top, ∀ i ∈ F, ((F.filter (fun j => lineGridCell (ρ k / 20) (x j) (v j) =
      lineGridCell (ρ k / 20) (x i) (v i))).card : ℝ) ≤ P k)
    (hPD : ∀ k ≤ top, P k * δ ^ 2 ≤ D * ρ k ^ 2)
    (hF : (F.card : ℝ) * δ ^ 2 ≤ D * ρ top ^ 2) :
    ∀ (a b : ℝ) (e : Space ≃ᵃⁱ[ℝ] Space), δ ≤ a → a ≤ b → b ≤ Λ * a → b ≤ 2 →
      ((F.filter (fun i => Tube δ (x i) (v i) ⊆
        e '' {z : Space | |z 0| ≤ a ∧ |z 1| ≤ b ∧ |z 2| ≤ 2})).card : ℝ) * δ ^ 2 ≤
        (400 * 122 ^ 3 * 16 ^ 3 * L ^ 2 * Λ * D) * a * b := by
  intro a b e hδa hab hbΛ hb2
  have ha0 : 0 < a := hδ.trans_le hδa
  have hb0 : 0 < b := ha0.trans_le hab
  have hbb : b ^ 2 ≤ Λ * (a * b) := by nlinarith
  set C₀ : ℝ := 122 ^ 3 * 16 ^ 3 with hC₀
  have hC₀1 : 1 ≤ C₀ := by norm_num [hC₀]
  set cnt := ((F.filter (fun i => Tube δ (x i) (v i) ⊆
    e '' {z : Space | |z 0| ≤ a ∧ |z 1| ≤ b ∧ |z 2| ≤ 2})).card : ℝ) with hcnt
  have hcntF : cnt ≤ F.card := by
    rw [hcnt]; exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  by_cases hbig : ρ top / 20 < b
  · -- the box is wider than the fibre's cells: count the whole fibre
    have hρb : ρ top ^ 2 ≤ 400 * b ^ 2 := by
      have h1 : ρ top < 20 * b := by linarith
      nlinarith [hρpos top]
    calc cnt * δ ^ 2 ≤ F.card * δ ^ 2 := by gcongr
      _ ≤ D * ρ top ^ 2 := hF
      _ ≤ D * (400 * b ^ 2) := by gcongr
      _ ≤ D * (400 * (Λ * (a * b))) := by gcongr
      _ ≤ (400 * C₀ * L ^ 2 * Λ * D) * a * b := by
          have h1 : D * (400 * (Λ * (a * b))) = (400 * Λ * D) * (a * b) := by ring
          have h2 : (400 * C₀ * L ^ 2 * Λ * D) * a * b = (400 * Λ * D) * (C₀ * L ^ 2) * (a * b) := by
            ring
          rw [h1, h2]
          have hpos : 0 ≤ 400 * Λ * D * (a * b) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hC₀1 hL2) hpos]
      _ = (400 * 122 ^ 3 * 16 ^ 3 * L ^ 2 * Λ * D) * a * b := by rw [hC₀]; ring
  · push Not at hbig
    have hb10 : b ≤ 1 / 10 := by linarith
    -- the first level whose cells are at least `b`
    have hex : ∃ k, b ≤ ρ k / 20 := ⟨top, hbig⟩
    set k := Nat.find hex with hkdef
    have hk : b ≤ ρ k / 20 := Nat.find_spec hex
    have hktop : k ≤ top := Nat.find_min' hex hbig
    have hρk : ρ k ≤ 20 * L * b := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0]; nlinarith
      · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hlt : ¬ b ≤ ρ k' / 20 := Nat.find_min hex (by omega)
        push Not at hlt
        calc ρ k = ρ (k' + 1) := by rw [hk']
          _ ≤ L * ρ k' := hρstep k'
          _ ≤ L * (20 * b) := by gcongr; linarith
          _ = 20 * L * b := by ring
    have hs : 0 < ρ k / 20 := by have := hρpos k; positivity
    have hbox := card_tubes_in_box_le x v F hδ ha0.le hab hb10 hs (hP0 k hktop) e hv hball hanti
      (hpop k hktop)
    have hfac : (120 * b / (ρ k / 20) + 2) ^ 3 * (14 * b / (ρ k / 20) + 2) ^ 3 ≤ C₀ := by
      have h1 : b / (ρ k / 20) ≤ 1 := (div_le_one hs).mpr hk
      have h2 : 0 ≤ b / (ρ k / 20) := by positivity
      have e1 : 120 * b / (ρ k / 20) = 120 * (b / (ρ k / 20)) := by ring
      have e2 : 14 * b / (ρ k / 20) = 14 * (b / (ρ k / 20)) := by ring
      rw [e1, e2, hC₀]
      gcongr <;> linarith
    have hcntP : cnt ≤ C₀ * P k := by
      calc cnt ≤ _ := hbox
        _ ≤ C₀ * P k := mul_le_mul_of_nonneg_right hfac (hP0 k hktop)
    calc cnt * δ ^ 2 ≤ C₀ * P k * δ ^ 2 := by gcongr
      _ = C₀ * (P k * δ ^ 2) := by ring
      _ ≤ C₀ * (D * ρ k ^ 2) := mul_le_mul_of_nonneg_left (hPD k hktop) (by positivity)
      _ ≤ C₀ * (D * (20 * L * b) ^ 2) := by
          gcongr
          exact (hρpos k).le
      _ = (400 * C₀ * L ^ 2 * D) * b ^ 2 := by ring
      _ ≤ (400 * C₀ * L ^ 2 * D) * (Λ * (a * b)) := by gcongr
      _ = (400 * C₀ * L ^ 2 * Λ * D) * a * b := by ring
      _ = (400 * 122 ^ 3 * 16 ^ 3 * L ^ 2 * Λ * D) * a * b := by rw [hC₀]; ring

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
