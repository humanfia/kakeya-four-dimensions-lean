-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/CountedPruning.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.CellCount
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.LightCells
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.ChildCount

/-!
# Counted pruning: no light observation cells (S4)

Let `b` be a packet of the frozen path, `H` the selected terminal incidences of its world
(covered by terminal packets, as in `ds`) and `inc₀ ≤ (ν ⊗ dt)|(H ∩ F_b)` any counted measure.
Fix the observation grid `cellIdx p Bv a` (base cubes of side `p`, the hidden bins of the
frozen observation `obs Bv a`) and a cell floor `mcell`.  Delete the light cells:
`inc = inc₀|heavySet`.  Then

* every observation cell has `inc`-mass `0` or at least `mcell` (`restrict_heavySet_fibre`);
* the deleted mass is at most `mcell` times the number of observation cells met by the
  descendants of `b` at a finer level `i'`.  These are at most
  `#children · (h'/p + 2)(2N^Mp + 2κ²h'/p + 2)² (24κ²δ(r_{i'})/a + 4)` with `h' = 2^{-T_{i'}}`
  (`exists_cell_finset_of_chart`), and the number of children times the ORIGINAL child mass
  floor of the path is at most the full product mass of `b`, hence at most the full old prior
  times the block length, `ν(A_b) 2^{-T_i}` (`card_finer_packets_mul_floor_le_mass`).

The incidences of `H ∩ F_b` lie in the children of `b` at level `i'` up to the null set of block
endpoints of `b`'s level (`mem_descendant_or_endpoint`): an incidence of a terminal packet lies
in all its ancestors, and two packets of one level and world meet only at block endpoints.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set MvPolynomial
open scoped ENNReal NNReal

noncomputable section

section Path

variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Ln} {E : Fin W → Set Ev}
    {B : Fin W → ℝ} {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {κ : ℝ} {C : ℕ} {lev : Fin C → ℕ}
    {par : Fin C → Fin C} {γ : Fin C → Fin W} {j : Fin C → ℕ} {c u : Fin C → P2}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ} {R : Fin C → Po} {A : Fin C → Set Ln}
    {F : Fin C → Set Ev} {lst : ℕ → Fin W → Ob → Finset (Fin C)}

/-- Ancestors along the parent map keep the world and contain the incidences. -/
lemma iterate_par_spec
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (k : ℕ) : ∀ b₀ : Fin C, k ≤ lev b₀ →
      lev (par^[k] b₀) = lev b₀ - k ∧ γ (par^[k] b₀) = γ b₀ ∧ F b₀ ⊆ F (par^[k] b₀) := by
  induction k with
  | zero => intro b₀ _; simp
  | succ k ih =>
    intro b₀ hk
    have hlev : 0 < lev b₀ := by omega
    obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b₀
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpar⟩ := hch
    obtain ⟨hl, hg, -, hF, -⟩ := hpar hlev
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2, h3⟩ := ih (par b₀) (by omega)
    exact ⟨by omega, h2.trans hg, hF.trans h3⟩

/-- **Descendants cover.**  An incidence of `b` lying in a terminal packet of the same world
lies in a descendant of `b` at any finer level, unless its time is a block endpoint of `b`'s
level. -/
lemma mem_descendant_or_endpoint
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (b : Fin C) (i' : ℕ) (hbi : lev b ≤ i') (hi' : i' ≤ m - 1)
    {q : Ev} (hqb : q ∈ F b) {bt : Fin C} (hbt : lev bt = m - 1) (hγt : γ bt = γ b)
    (hqt : q ∈ F bt) :
    (∃ b', lev b' = i' ∧ γ b' = γ b ∧ F b' ⊆ F b ∧ q ∈ F b') ∨
      ∃ n : ℕ, q.2 = (n : ℝ) / (2:ℝ) ^ T (lev b) := by
  obtain ⟨h1, h2, h3⟩ := iterate_par_spec hp (m - 1 - i') bt (by omega)
  set a' := par^[m - 1 - i'] bt with ha'
  have ha'lev : lev a' = i' := by omega
  obtain ⟨h4, h5, h6⟩ := iterate_par_spec hp (i' - lev b) a' (by omega)
  set a := par^[i' - lev b] a' with ha
  have halev : lev a = lev b := by omega
  have hqa' : q ∈ F a' := h3 hqt
  have hqa : q ∈ F a := h6 hqa'
  by_cases hab : a = b
  · left
    exact ⟨a', ha'lev, h2.trans hγt, hab ▸ h6, hqa'⟩
  · right
    obtain ⟨-, -, hcha⟩ := hp.2.2.2.2.2.2.2 a
    obtain ⟨-, -, hchb⟩ := hp.2.2.2.2.2.2.2 b
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hFa, -⟩ := hcha
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hFb, -⟩ := hchb
    have hqa'' := hFa q hqa
    have hqb'' := hFb q hqb
    have hγab : γ a = γ b := h5.trans (h2.trans hγt)
    by_cases hj : j a = j b
    · exact absurd (hp.2.2.2.2.2.2.1 a b hab halev hγab hj)
        (Set.not_disjoint_iff.mpr ⟨q.1, hqa''.2.1, hqb''.2.1⟩)
    · have hta := hqa''.2.2.1
      have htb := hqb''.2.2.1
      rw [halev] at hta
      have h2T : (0:ℝ) < (2:ℝ) ^ T (lev b) := by positivity
      rcases lt_or_gt_of_ne hj with hlt | hlt
      · refine ⟨j b, le_antisymm ?_ htb.1⟩
        have : ((j a : ℝ) + 1) ≤ (j b : ℝ) := by exact_mod_cast hlt
        exact hta.2.trans (div_le_div_of_nonneg_right this h2T.le)
      · refine ⟨j a, le_antisymm ?_ hta.1⟩
        have : ((j b : ℝ) + 1) ≤ (j a : ℝ) := by exact_mod_cast hlt
        exact htb.2.trans (div_le_div_of_nonneg_right this h2T.le)

/-- The incidences at block endpoints are null for every product law. -/
lemma prod_endpoints_null (μ : Measure Ln) (Tn : ℕ) :
    (μ.prod volume) {q : Ev | ∃ n : ℕ, q.2 = (n : ℝ) / (2:ℝ) ^ Tn} = 0 := by
  have : {q : Ev | ∃ n : ℕ, q.2 = (n : ℝ) / (2:ℝ) ^ Tn} =
      (Set.univ : Set Ln) ×ˢ Set.range (fun n : ℕ => (n : ℝ) / (2:ℝ) ^ Tn) := by
    ext q
    simp [eq_comm]
  rw [this, Measure.prod_prod, (Set.countable_range _).measure_zero volume, mul_zero]

/-- **Counted measures live on the children.**  A counted measure of `b` gives no mass to a set
avoiding the incidences of all descendants of `b` at level `i'`. -/
theorem counted_null_off_children
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (b : Fin C) (i' : ℕ) (hbi : lev b ≤ i') (hi' : i' ≤ m - 1)
    (H : Set Ev) (hHm : MeasurableSet H)
    (hH : ∀ q ∈ H, ∃ bt, lev bt = m - 1 ∧ γ bt = γ b ∧ q ∈ F bt)
    (inc₀ : Measure Ev) (hinc₀ : inc₀ ≤ ((ν (γ b)).prod volume).restrict {q | q ∈ H ∧ q ∈ F b})
    (Y : Set Ev) (hY : ∀ b', lev b' = i' → γ b' = γ b → F b' ⊆ F b → ∀ q ∈ F b', q ∉ Y) :
    inc₀ Y = 0 := by
  have hFm : MeasurableSet (F b) := by
    obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b
    exact hch.2.2.2.2.2.2.2.1
  have hHF : MeasurableSet {q | q ∈ H ∧ q ∈ F b} := hHm.inter hFm
  refine le_antisymm ?_ zero_le
  calc inc₀ Y ≤ (((ν (γ b)).prod volume).restrict {q | q ∈ H ∧ q ∈ F b}) Y := hinc₀ Y
    _ = ((ν (γ b)).prod volume) (Y ∩ {q | q ∈ H ∧ q ∈ F b}) := Measure.restrict_apply' hHF
    _ ≤ ((ν (γ b)).prod volume) {q : Ev | ∃ n : ℕ, q.2 = (n : ℝ) / (2:ℝ) ^ T (lev b)} := by
        apply measure_mono
        intro q hq
        obtain ⟨hqY, hqH, hqF⟩ := hq
        obtain ⟨bt, hbt, hγt, hqt⟩ := hH q hqH
        rcases mem_descendant_or_endpoint hp b i' hbi hi' hqF hbt hγt hqt with
          ⟨b', h1, h2, h3, h4⟩ | hend
        · exact absurd hqY (hY b' h1 h2 h3 q h4)
        · exact hend
    _ = 0 := prod_endpoints_null _ _

open Classical in
/-- **Counted pruning (S4).**  Deleting the light observation cells of a counted measure of `b`
leaves every observation cell empty or of mass at least `mcell`; the deleted mass, times the
original child floor of the path at level `i'`, is at most the full old prior times the block
length times the per-child cell count times `mcell`. -/
theorem counted_pruning
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hN : 1 ≤ Nk) (b : Fin C) (i' : ℕ) (hbi : lev b ≤ i') (hi' : i' ≤ m - 1)
    (hB : 0 < B (γ b))
    (H : Set Ev) (hHm : MeasurableSet H)
    (hH : ∀ q ∈ H, ∃ bt, lev bt = m - 1 ∧ γ bt = γ b ∧ q ∈ F bt)
    (inc₀ : Measure Ev) (hinc₀ : inc₀ ≤ ((ν (γ b)).prod volume).restrict {q | q ∈ H ∧ q ∈ F b})
    {p a : ℝ} (hp0 : 0 < p) (ha : 0 < a) (mcell : ℝ≥0∞)
    (hpR : ∀ b', lev b' = i' → 3 * lipBox (R b') (2 * Nk ^ Mp) * p ≤ κ * δ Nk (r i'))
    (hpD : ∀ b', lev b' = i' →
      3 * lipBox (pderiv 3 (R b')) (2 * Nk ^ Mp) * p ≤ B (γ b) / κ) :
    (∀ k, (inc₀.restrict (heavySet inc₀ (cellIdx p (B (γ b)) a) mcell))
        (cellIdx p (B (γ b)) a ⁻¹' {k}) = 0 ∨
      mcell ≤ (inc₀.restrict (heavySet inc₀ (cellIdx p (B (γ b)) a) mcell))
        (cellIdx p (B (γ b)) a ⁻¹' {k})) ∧
    inc₀ (heavySet inc₀ (cellIdx p (B (γ b)) a) mcell)ᶜ *
        ENNReal.ofReal (Nk ^ (-f (r i')) * (Nk ^ (-(nw i' + δ₀ * L)) / (4:ℝ) ^ T i') /
          ((2:ℝ) ^ T i' * κ)) ≤
      ν (γ b) (A b) * ENNReal.ofReal (((2:ℝ) ^ T (lev b))⁻¹) *
        ENNReal.ofReal (((((2:ℝ) ^ T i')⁻¹ / p + 2) *
          (2 * Nk ^ Mp + 2 * κ ^ 2 * ((2:ℝ) ^ T i')⁻¹ / p + 2) ^ 2) *
            (24 * κ ^ 2 * δ Nk (r i') / a + 4)) * mcell := by
  have hκ1 : 1 ≤ κ := hp.1
  have hκ : 0 < κ := by linarith
  have hNM : 1 ≤ Nk ^ Mp := one_le_pow₀ hN
  have hpack := hp.2.2.2.2.2.2.2
  set idx := cellIdx p (B (γ b)) a with hidx
  refine ⟨fun k => restrict_heavySet_fibre inc₀ (measurable_cellIdx _ _ _) mcell k, ?_⟩
  -- the children and their cells
  set S := Finset.univ.filter (fun b' => lev b' = i' ∧ γ b' = γ b ∧ F b' ⊆ F b) with hS
  set h' : ℝ := ((2:ℝ) ^ T i')⁻¹ with hh'
  set Kc : ℝ := (h' / p + 2) * (2 * Nk ^ Mp + 2 * κ ^ 2 * h' / p + 2) ^ 2 with hKc
  set Kb : ℝ := 24 * κ ^ 2 * δ Nk (r i') / a + 4 with hKb
  have hδ := δ_pos Nk (r i')
  have hKc0 : 0 ≤ Kc := by positivity
  have hKb0 : 0 ≤ Kb := by positivity
  have hcells : ∀ b' ∈ S, ∃ Sb : Finset ((Fin 3 → ℤ) × ℤ),
      (∀ q ∈ F b', idx q ∈ Sb) ∧ (Sb.card : ℝ) ≤ Kc * Kb := by
    intro b' hb'
    obtain ⟨hlev, hγ, -⟩ := (Finset.mem_filter.mp hb').2
    obtain ⟨-, hjlt, hch⟩ := hpack b'
    have hu : ‖u b'‖ ≤ Nk ^ Mp := by
      have := hch.2.1
      linarith [norm_nonneg (c b')]
    rw [hγ] at hch
    rw [hlev] at hch hjlt
    obtain ⟨Sb, hSb, hSbc⟩ := exists_cell_finset_of_chart hch hjlt hN hκ hB hp0 ha
      (hpR b' hlev) (hpD b' hlev)
    refine ⟨Sb, hSb, hSbc.trans ?_⟩
    rw [hKc, hh']
    gcongr
  choose! Sb hSb hSbc using hcells
  set Sall := S.biUnion Sb with hSall
  have hSall_card : (Sall.card : ℝ) ≤ S.card * (Kc * Kb) := by
    calc (Sall.card : ℝ) ≤ ∑ b' ∈ S, ((Sb b').card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _b' ∈ S, Kc * Kb := Finset.sum_le_sum hSbc
      _ = S.card * (Kc * Kb) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the counted measure lives on the cells of `Sall`
  have hnull : inc₀ {q | idx q ∉ Sall} = 0 := by
    refine counted_null_off_children hp b i' hbi hi' H hHm hH inc₀ hinc₀ _ ?_
    intro b' h1 h2 h3 q hq hqY
    have hb'S : b' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3⟩
    exact hqY (Finset.mem_biUnion.mpr ⟨b', hb'S, hSb b' hb'S q hq⟩)
  have hloss := measure_compl_heavySet_le inc₀ idx mcell Sall hnull
  -- children times the child floor
  have hchild := card_finer_packets_mul_floor_le_mass hp (by linarith) b i'
  rw [← hS] at hchild
  have hmassb : ((ν (γ b)).prod volume) (F b) ≤
      ν (γ b) (A b) * ENNReal.ofReal (((2:ℝ) ^ T (lev b))⁻¹) := by
    obtain ⟨-, -, hch⟩ := hpack b
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, -⟩ := hch
    exact prod_le_prior_mul_block (fun q hq => ⟨(hF q hq).2.1, (hF q hq).2.2.1⟩)
  set floor' := ENNReal.ofReal (Nk ^ (-f (r i')) * (Nk ^ (-(nw i' + δ₀ * L)) / (4:ℝ) ^ T i') /
      ((2:ℝ) ^ T i' * κ)) with hfloor'
  have hcardE : (Sall.card : ℝ≥0∞) ≤ (S.card : ℝ≥0∞) * ENNReal.ofReal (Kc * Kb) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (S.card),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hSall_card
  calc inc₀ (heavySet inc₀ idx mcell)ᶜ * floor'
      ≤ (Sall.card : ℝ≥0∞) * mcell * floor' := by gcongr
    _ ≤ (S.card : ℝ≥0∞) * ENNReal.ofReal (Kc * Kb) * mcell * floor' := by gcongr
    _ = ((S.card : ℝ≥0∞) * floor') * ENNReal.ofReal (Kc * Kb) * mcell := by ring
    _ ≤ ((ν (γ b)).prod volume) (F b) * ENNReal.ofReal (Kc * Kb) * mcell := by gcongr
    _ ≤ ν (γ b) (A b) * ENNReal.ofReal (((2:ℝ) ^ T (lev b))⁻¹) *
          ENNReal.ofReal (Kc * Kb) * mcell := by gcongr

end Path

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
