-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.StagesAssembly, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.ChildStage
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SimultaneousChildStates
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.WholeGraphStateSelection
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.WholeChildFailurePruning

/-!
# Assembly tools of the per-sample stages (session x1082)

* `rowClauses_of_readout`: `RowClauses` for states whose rows read the ancestor rows scaled by
  `aA/q` off the ancestor's clock code: bound, graph clause from the pointwise fit in clock
  units, lists from base-only lists of the scaled rows.
* `assemble_same_level_whole_cuts`: per-packet cuts at one level whose kept part carries a fixed
  fraction of each packet's slice assemble into one family with exact slices and the same
  fraction of the total weighted mass (the whole-state cuts of the regularity stage).
* `child_states_of_records`: the states of ALL children at one level, before every whole-state
  cut, from the ancestors' record sources (x1095's `relative_states_with_graph_code` and
  `assemble_simultaneous_child_states`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily)
open scoped ENNReal BigOperators

noncomputable section

/-- **Rows on states from the ancestor rows.** -/
theorem rowClauses_of_readout {K θ aA q : ℝ} {RA : Po} {zb : Ev → O204.Split.P3}
    {Se Er : Set Ev} {st : Ev → ℕ} {value : ℕ → Fin 3 → ℝ} {Code : Type*}
    (code : Ev → Code) (row : Code → Fin 3 → ℝ) (haA : 0 < aA) (hq : 0 < q)
    (hvalue : ∀ k i, |value k i| ≤ K * (aA / q))
    (hread : ∀ z, value (st z) = (aA / q) • row (code z))
    (hfit : ∀ x ∈ Se, |q / aA * Submission.Lib.K4GlobalParentSignal.rate RA x.1 x.2 -
      ∑ j : Fin 3, row (code x) j * (![1, x.1.2 3, x.1.2 4] : Fin 3 → ℝ) j| ≤ θ)
    (hlist : ∀ c' : Fin 3 → ℝ, ∃ Fc : Finset (Fin 3 → ℤ), (Fc.card : ℝ) ≤ K ∧
      ∀ x ∈ Er, (∀ j : Fin 3, |zb x j - c' j| ≤ θ) →
        (fun j : Fin 3 => ⌊(aA / q) * row (code x) j / ((aA / q) * θ)⌋) ∈ Fc) :
    RowClauses K θ aA q RA zb Se Er st value := by
  have hscale0 : 0 ≤ aA / q := (div_pos haA hq).le
  refine ⟨hvalue, ?_, ?_⟩
  · intro z hz
    have hf := hfit z hz
    rw [hread z]
    have hsum : ∑ j : Fin 3, (![1, z.1.2 3, z.1.2 4] : Fin 3 → ℝ) j * ((aA / q) • row (code z)) j =
        (aA / q) * ∑ j : Fin 3, row (code z) j * (![1, z.1.2 3, z.1.2 4] : Fin 3 → ℝ) j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hrate : Submission.Lib.K4GlobalParentSignal.rate RA z.1 z.2 =
        (aA / q) * (q / aA * Submission.Lib.K4GlobalParentSignal.rate RA z.1 z.2) := by
      field_simp
    rw [hsum, hrate, ← mul_sub, abs_mul, abs_of_nonneg hscale0]
    exact mul_le_mul_of_nonneg_left hf hscale0
  · intro c'
    obtain ⟨Fc, hFc, hmem⟩ := hlist c'
    refine ⟨Fc, hFc, fun x hx hbox => ?_⟩
    have h := hmem x hx hbox
    rw [hread x]
    simpa only [Pi.smul_apply, smul_eq_mul] using h

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

open Classical in
/-- **Charges against full references at one level add up to the charge.** -/
theorem weighted_selected_charge_le (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (selected : Set (Fin p.C)) (level : ℕ) (hlevel : ∀ b ∈ selected, p.lev b = level)
    (g : Fin p.C → ENNReal) (charge : ENNReal)
    (hg : ∀ b ∈ selected, g b ≤ charge * (d.ν k (p.γ b) (p.A b) *
      ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))) :
    (∑ w, ENNReal.ofReal (d.ω k w) *
      ∑ b ∈ Finset.univ.filter (fun b => b ∈ selected ∧ p.γ b = w), g b) ≤ charge := by
  classical
  have hregroup : (∑ w, ENNReal.ofReal (d.ω k w) *
      ∑ b ∈ Finset.univ.filter (fun b => b ∈ selected ∧ p.γ b = w), g b) =
      ∑ b, if b ∈ selected then ENNReal.ofReal (d.ω k (p.γ b)) * g b else 0 := by
    simp_rw [Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : b ∈ selected
    · simp only [hb, true_and, ↓reduceIte, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      simp
    · simp [hb]
  rw [hregroup]
  calc (∑ b, if b ∈ selected then ENNReal.ofReal (d.ω k (p.γ b)) * g b else 0)
      ≤ ∑ b, charge * ((if p.lev b = level then ENNReal.ofReal (d.ω k (p.γ b)) else 0) *
          (ENNReal.ofReal (((2 : ℝ) ^ p.T level)⁻¹) * d.ν k (p.γ b) (p.A b))) := by
        apply Finset.sum_le_sum
        intro b _
        by_cases hb : b ∈ selected
        · have hl := hlevel b hb
          simp only [hb, hl, ↓reduceIte]
          calc ENNReal.ofReal (d.ω k (p.γ b)) * g b
              ≤ ENNReal.ofReal (d.ω k (p.γ b)) * (charge * (d.ν k (p.γ b) (p.A b) *
                  ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))) :=
                mul_le_mul' le_rfl (hg b hb)
            _ = _ := by rw [hl]; ring
        · simp only [hb, ↓reduceIte]
          exact zero_le
    _ = charge * ∑ b, (if p.lev b = level then ENNReal.ofReal (d.ω k (p.γ b)) else 0) *
          (ENNReal.ofReal (((2 : ℝ) ^ p.T level)⁻¹) * d.ν k (p.γ b) (p.A b)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ charge * 1 := mul_le_mul' le_rfl
        (hp.full_reference_mass_le_one (hd.weights k).2.2 (hd.weights k).1 (hd.weights k).2.1
          level)
    _ = charge := mul_one _

/-- **Whole cuts at one level, multiplicatively.** If every event of `E` lies in a selected packet
of one level and each selected packet keeps a `c⁻¹` fraction of its slice, the assembled family
has exact slices and keeps a `c⁻¹` fraction of the total weighted mass. -/
theorem assemble_same_level_whole_cuts (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (selected : Set (Fin p.C)) (level : ℕ) (hlevel : ∀ b ∈ selected, p.lev b = level)
    (E : Fin (d.W k) → Set Ev) (hE : ∀ w, MeasurableSet (E w))
    (hbase : ∀ w, E w ⊆ Q.base w)
    (hcover : ∀ w, ∀ z ∈ E w, ∃ b ∈ selected, p.γ b = w ∧ z ∈ p.F b)
    (G : Fin p.C → Set Ev) (hG : ∀ b, b ∈ selected → MeasurableSet (G b)) (c : ENNReal)
    (hfrac : ∀ b, b ∈ selected → ((d.ν k (p.γ b)).prod volume) (E (p.γ b) ∩ p.F b) ≤
      c * ((d.ν k (p.γ b)).prod volume) ((E (p.γ b) ∩ p.F b) ∩ G b)) :
    ∃ keep : Fin (d.W k) → Set Ev,
      (∀ w, MeasurableSet (keep w) ∧ keep w ⊆ E w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E w)) ≤
        c * ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (keep w) ∧
      ∀ b, b ∈ selected → keep (p.γ b) ∩ p.F b = (E (p.γ b) ∩ p.F b) ∩ G b := by
  classical
  obtain ⟨keep, hkeep, -, hslice⟩ := Q.assemble_same_level_packet_cuts hd hp selected level hlevel E
    hE hbase G hG ⊤ (fun b hb => by
      by_cases h0 : d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹) = 0
      · have hsub : (E (p.γ b) ∩ p.F b) \ G b ⊆ p.fullCylinder b :=
          fun z hz => hp.counted_subset_fullCylinder b hz.1.2
        have hfull := p.fullCylinder_mass (d.ν k (p.γ b)) b
        refine (measure_mono hsub).trans ?_
        rw [hfull, h0]
        exact zero_le
      · rw [ENNReal.top_mul h0]
        exact le_top)
  refine ⟨keep, hkeep, ?_, hslice⟩
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  let idx : Fin (d.W k) → Finset (Fin p.C) := fun w =>
    Finset.univ.filter (fun b => b ∈ selected ∧ p.γ b = w)
  have hidx (w : Fin (d.W k)) (b : Fin p.C) : b ∈ idx w ↔ b ∈ selected ∧ p.γ b = w := by
    simp only [idx, Finset.mem_filter, Finset.mem_univ, true_and]
  -- slices of one world are disjoint on the base
  have hdisj (w : Fin (d.W k)) (S : Set Ev) (hS : S ⊆ Q.base w) :
      (↑(idx w) : Set (Fin p.C)).PairwiseDisjoint (fun b => S ∩ p.F b) := by
    intro b hb b' hb' hne
    obtain ⟨hs, hw⟩ := (hidx w b).mp hb
    obtain ⟨hs', hw'⟩ := (hidx w b').mp hb'
    apply Set.disjoint_left.mpr
    rintro z ⟨hzS, hzb⟩ ⟨_, hzb'⟩
    exact hne (Q.base_packet_unique w z (hS hzS) b b'
      ((hlevel b hs).trans (hlevel b' hs').symm) hw hw' hzb hzb')
  -- the mass of `E w` is the sum of its slices
  have hEw (w : Fin (d.W k)) : ((d.ν k w).prod volume) (E w) ≤
      ∑ b ∈ idx w, ((d.ν k w).prod volume) (E w ∩ p.F b) := by
    have hsub : E w ⊆ ⋃ b ∈ idx w, E w ∩ p.F b := by
      intro z hz
      obtain ⟨b, hb, hw, hzb⟩ := hcover w z hz
      exact mem_biUnion ((hidx w b).mpr ⟨hb, hw⟩) ⟨hz, hzb⟩
    exact (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
  -- the kept slices are disjoint parts of `keep w`
  have hkw (w : Fin (d.W k)) : ∑ b ∈ idx w, ((d.ν k w).prod volume) (keep w ∩ p.F b) ≤
      ((d.ν k w).prod volume) (keep w) := by
    rw [← measure_biUnion_finset (hdisj w (keep w) (fun z hz => hbase w ((hkeep w).2 hz)))
      (fun b _ => ((hkeep w).1.inter (hF b)))]
    exact measure_mono (iUnion₂_subset fun b _ => inter_subset_left)
  have hlocal (w : Fin (d.W k)) : ((d.ν k w).prod volume) (E w) ≤
      c * ((d.ν k w).prod volume) (keep w) := by
    refine (hEw w).trans ?_
    calc ∑ b ∈ idx w, ((d.ν k w).prod volume) (E w ∩ p.F b)
        ≤ ∑ b ∈ idx w, c * ((d.ν k w).prod volume) (keep w ∩ p.F b) := by
          apply Finset.sum_le_sum
          intro b hb
          obtain ⟨hs, hw⟩ := (hidx w b).mp hb
          subst hw
          rw [hslice b hs]
          exact hfrac b hs
      _ = c * ∑ b ∈ idx w, ((d.ν k w).prod volume) (keep w ∩ p.F b) := by
          rw [Finset.mul_sum]
      _ ≤ c * ((d.ν k w).prod volume) (keep w) := mul_le_mul' le_rfl (hkw w)
  calc (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E w))
      ≤ ∑ w, ENNReal.ofReal (d.ω k w) * (c * ((d.ν k w).prod volume) (keep w)) :=
        Finset.sum_le_sum fun w _ => mul_le_mul' le_rfl (hlocal w)
    _ = c * ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (keep w) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring

open Classical in
/-- **Whole cuts at one level with a fraction and a full-reference charge.** -/
theorem assemble_same_level_whole_cuts_charge (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (selected : Set (Fin p.C)) (level : ℕ) (hlevel : ∀ b ∈ selected, p.lev b = level)
    (E : Fin (d.W k) → Set Ev) (hE : ∀ w, MeasurableSet (E w))
    (hbase : ∀ w, E w ⊆ Q.base w)
    (hcover : ∀ w, ∀ z ∈ E w, ∃ b ∈ selected, p.γ b = w ∧ z ∈ p.F b)
    (G : Fin p.C → Set Ev) (hG : ∀ b, b ∈ selected → MeasurableSet (G b)) (c charge : ENNReal)
    (hfrac : ∀ b, b ∈ selected → ((d.ν k (p.γ b)).prod volume) (E (p.γ b) ∩ p.F b) ≤
      c * ((d.ν k (p.γ b)).prod volume) ((E (p.γ b) ∩ p.F b) ∩ G b) +
        charge * (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))) :
    ∃ keep : Fin (d.W k) → Set Ev,
      (∀ w, MeasurableSet (keep w) ∧ keep w ⊆ E w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E w)) ≤
        c * (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (keep w)) + charge ∧
      ∀ b, b ∈ selected → keep (p.γ b) ∩ p.F b = (E (p.γ b) ∩ p.F b) ∩ G b := by
  obtain ⟨keep, hkeep, -, hslice⟩ := Q.assemble_same_level_packet_cuts hd hp selected level hlevel E
    hE hbase G hG ⊤ (fun b hb => by
      by_cases h0 : d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹) = 0
      · have hsub : (E (p.γ b) ∩ p.F b) \ G b ⊆ p.fullCylinder b :=
          fun z hz => hp.counted_subset_fullCylinder b hz.1.2
        have hfull := p.fullCylinder_mass (d.ν k (p.γ b)) b
        refine (measure_mono hsub).trans ?_
        rw [hfull, h0]
        exact zero_le
      · rw [ENNReal.top_mul h0]
        exact le_top)
  refine ⟨keep, hkeep, ?_, hslice⟩
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  let idx : Fin (d.W k) → Finset (Fin p.C) := fun w =>
    Finset.univ.filter (fun b => b ∈ selected ∧ p.γ b = w)
  have hidx (w : Fin (d.W k)) (b : Fin p.C) : b ∈ idx w ↔ b ∈ selected ∧ p.γ b = w := by
    simp only [idx, Finset.mem_filter, Finset.mem_univ, true_and]
  have hdisj (w : Fin (d.W k)) (S : Set Ev) (hS : S ⊆ Q.base w) :
      (↑(idx w) : Set (Fin p.C)).PairwiseDisjoint (fun b => S ∩ p.F b) := by
    intro b hb b' hb' hne
    obtain ⟨hs, hw⟩ := (hidx w b).mp hb
    obtain ⟨hs', hw'⟩ := (hidx w b').mp hb'
    apply Set.disjoint_left.mpr
    rintro z ⟨hzS, hzb⟩ ⟨_, hzb'⟩
    exact hne (Q.base_packet_unique w z (hS hzS) b b'
      ((hlevel b hs).trans (hlevel b' hs').symm) hw hw' hzb hzb')
  have hEw (w : Fin (d.W k)) : ((d.ν k w).prod volume) (E w) ≤
      ∑ b ∈ idx w, ((d.ν k w).prod volume) (E w ∩ p.F b) := by
    have hsub : E w ⊆ ⋃ b ∈ idx w, E w ∩ p.F b := by
      intro z hz
      obtain ⟨b, hb, hw, hzb⟩ := hcover w z hz
      exact mem_biUnion ((hidx w b).mpr ⟨hb, hw⟩) ⟨hz, hzb⟩
    exact (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
  have hkw (w : Fin (d.W k)) : ∑ b ∈ idx w, ((d.ν k w).prod volume) (keep w ∩ p.F b) ≤
      ((d.ν k w).prod volume) (keep w) := by
    rw [← measure_biUnion_finset (hdisj w (keep w) (fun z hz => hbase w ((hkeep w).2 hz)))
      (fun b _ => ((hkeep w).1.inter (hF b)))]
    exact measure_mono (iUnion₂_subset fun b _ => inter_subset_left)
  let g : Fin p.C → ENNReal := fun b =>
    charge * (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))
  have hlocal (w : Fin (d.W k)) : ((d.ν k w).prod volume) (E w) ≤
      c * ((d.ν k w).prod volume) (keep w) + ∑ b ∈ idx w, g b := by
    refine (hEw w).trans ?_
    calc ∑ b ∈ idx w, ((d.ν k w).prod volume) (E w ∩ p.F b)
        ≤ ∑ b ∈ idx w, (c * ((d.ν k w).prod volume) (keep w ∩ p.F b) + g b) := by
          apply Finset.sum_le_sum
          intro b hb
          obtain ⟨hs, hw⟩ := (hidx w b).mp hb
          subst hw
          rw [hslice b hs]
          exact hfrac b hs
      _ = c * ∑ b ∈ idx w, ((d.ν k w).prod volume) (keep w ∩ p.F b) + ∑ b ∈ idx w, g b := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ c * ((d.ν k w).prod volume) (keep w) + ∑ b ∈ idx w, g b :=
          add_le_add (mul_le_mul' le_rfl (hkw w)) le_rfl
  have hcharge := weighted_selected_charge_le hd hp selected level hlevel g charge
    (fun b _ => le_rfl)
  calc (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E w))
      ≤ ∑ w, ENNReal.ofReal (d.ω k w) *
          (c * ((d.ν k w).prod volume) (keep w) + ∑ b ∈ idx w, g b) :=
        Finset.sum_le_sum fun w _ => mul_le_mul' le_rfl (hlocal w)
    _ = c * (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (keep w)) +
          ∑ w, ENNReal.ofReal (d.ω k w) * ∑ b ∈ idx w, g b := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun w _ => by ring
    _ ≤ _ := add_le_add le_rfl hcharge

/-- **The states of all children at one level**, built before every whole-state cut: each
selected child `b` below the active ancestor `anc b` gets x1095's states on its slice of `E`
(rows `(aA/q)•row (anc b)` on the ancestor clock code), and the slices are assembled into one
family with exact child slices and one total loss `6561 β`. -/
theorem child_states_of_records {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal}
    {F : PaletteFamily Q i stop meshF envF θF} (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (selected : Set (Fin p.C)) (level : ℕ) (hlevel : ∀ b ∈ selected, p.lev b = level)
    (anc : Fin p.C → Fin p.C)
    (hanc : ∀ b ∈ selected, F.active (anc b) ∧ p.γ b = p.γ (anc b) ∧ p.lev b ≤ stop)
    {Edata : Fin p.C → Set Ev}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension
      Kcap : ℝ}
    (data : (a : Fin p.C) → F.active a → OriginalAncestorRecordSource F a (Edata a) Krecord
      baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension Kcap)
    (hEdata : ∀ a, F.active a → Edata a ⊆ Q.base (p.γ a))
    (E : Fin (d.W k) → Set Ev) (hE : ∀ w, MeasurableSet (E w)) (hEbase : ∀ w, E w ⊆ Q.base w)
    (hkept : ∀ b (hb : b ∈ selected), E (p.γ b) ∩ p.F b ⊆ (data (anc b) (hanc b hb).1).kept)
    {K ε pv aA q graphMesh : ℝ} (hK : 0 < K) (heps : 0 < ε) (haA : 0 < aA) (hq : 0 < q)
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef) (hcut : 0 < cut) (hfr : 0 ≤ fraction)
    (hgraph : 0 < graphMesh) (hfinePv : 0 < finePv) (hpv : finePv ≤ pv)
    (hgraphBase : 3 * baseRef ≤ graphMesh) (hgraphHidden : 3 * hiddenRef ≤ graphMesh)
    (hphysicalBase : ∀ b ∈ selected,
      3 * ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev (anc b))) * baseRef ≤ ε)
    (hphysicalHidden : ∀ b ∈ selected,
      3 * (δ (d.N k) (p.r (p.lev (anc b))) / δ (d.N k) (p.r (p.lev b))) * hiddenRef ≤
        (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev b))) * ε)
    (beta : ENNReal) (hbeta : beta ≠ 0) (hbetaTop : beta ≠ ⊤)
    (hstripWidth : ∀ b ∈ selected,
      (K / 4) ^ (-100 : ℝ) * (∑ j : Fin 2, ∑ l : Fin 2, |p.Q (anc b) j l|) ≤
        frontRadius * ((2 : ℝ) ^ p.T (p.lev (anc b)) * |(p.Q (anc b)).det|))
    (hstripRatio : ENNReal.ofReal ((8 * fraction) / cut) / beta ≤ (1 / 2000000000000 : ENNReal))
    (hpaletteRatio : ENNReal.ofReal ((8 * paletteRatio) / cut) / beta ≤ ENNReal.ofReal (K / 4))
    (row : Fin p.C → (Fin 4 → ℤ) → Fin 3 → ℝ) {Brow : ℝ} (hBrow : 0 ≤ Brow)
    (hrow : ∀ a c j, |row a c j| ≤ Brow) :
    ∃ (keep : Fin (d.W k) → Set Ev)
      (localKeep : (b : Fin p.C) → b ∈ selected → Set Ev)
      (state : (b : Fin p.C) → b ∈ selected → Ev → ℕ)
      (value : (b : Fin p.C) → b ∈ selected → ℕ → Fin 3 → ℝ)
      (palette : (b : Fin p.C) → b ∈ selected → Measure (Fin 2 → ℤ)),
      (∀ w, MeasurableSet (keep w) ∧ keep w ⊆ E w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (E w \ keep w)) ≤
        (6561 : ENNReal) * beta ∧
      ∀ b (hb : b ∈ selected),
        keep (p.γ b) ∩ p.F b = localKeep b hb ∧
        StateClauses K ε pv (d.ν k (p.γ b)) (unshearedPacketBase p b)
          (fun z => MvPolynomial.eval (xp z.1 z.2) (p.R (anc b)) / δ (d.N k) (p.r (p.lev b)))
          (keep (p.γ b) ∩ p.F b) (state b hb) (palette b hb) ∧
        (∀ z, value b hb (state b hb z) = (aA / q) • row (anc b) (clockParentCode p (anc b)
          (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b)) graphMesh z)) ∧
        (∀ j c, |value b hb j c| ≤ (aA / q) * Brow) ∧
        ∀ x y, state b hb x = state b hb y →
          clockParentCode p (anc b) (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b))
            graphMesh x =
          clockParentCode p (anc b) (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b))
            graphMesh y := by
  classical
  have hscale0 : 0 ≤ aA / q := (div_pos haA hq).le
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hlocal : ∀ b, b ∈ selected →
      ∃ (keepb : Set Ev) (state : Ev → ℕ) (value : ℕ → Fin 3 → ℝ)
        (palette : Measure (Fin 2 → ℤ)),
        keepb ⊆ E (p.γ b) ∩ p.F b ∧
        ((d.ν k (p.γ b)).prod volume) (E (p.γ b) ∩ p.F b) ≤
          ((d.ν k (p.γ b)).prod volume) keepb +
            ((6561 : ENNReal) * beta) * (d.ν k (p.γ b) (p.A b) *
              ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) ∧
        StateClauses K ε pv (d.ν k (p.γ b)) (unshearedPacketBase p b)
          (fun z => MvPolynomial.eval (xp z.1 z.2) (p.R (anc b)) / δ (d.N k) (p.r (p.lev b)))
          keepb state palette ∧
        (∀ z, value (state z) = (fun b c => (aA / q) • row (anc b) c) b
          ((fun b => clockParentCode p (anc b)
            (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b)) graphMesh) b z)) ∧
        (∀ j c, |value j c| ≤ (fun _ => (aA / q) * Brow) b) ∧
        ∀ x y, state x = state y →
          (fun b => clockParentCode p (anc b)
            (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b)) graphMesh) b x =
          (fun b => clockParentCode p (anc b)
            (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b)) graphMesh) b y := by
    intro b hb
    obtain ⟨hact, hworld, hstop⟩ := hanc b hb
    have hδb : 0 < δ (d.N k) (p.r (p.lev b)) := by unfold δ; positivity
    have hrow' : ∀ c j, |((aA / q) • row (anc b) c) j| ≤ (aA / q) * Brow := by
      intro c j
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hscale0]
      exact mul_le_mul_of_nonneg_left (hrow _ c j) hscale0
    obtain ⟨keepb, state, value, palette, hsub, hloss, hstates, hvalue, hbound, hfaith⟩ :=
      OriginalAncestorRecordSource.relative_states_with_graph_code (data (anc b) hact) hd hp hHE hH
        hact (hEdata _ hact) b hworld hstop hbaseRef hhiddenRef hcut hfr hgraph heps hδb hfinePv
        hpv hK hgraphBase hgraphHidden (hphysicalBase b hb) (hphysicalHidden b hb)
        (E (p.γ b) ∩ p.F b) ((hE _).inter (hF b)) (fun z hz => ⟨hkept b hb hz, hz.2⟩)
        beta hbeta hbetaTop (fun c => (aA / q) • row (anc b) c) (mul_nonneg hscale0 hBrow)
        hrow' (hstripWidth b hb) hstripRatio hpaletteRatio
    refine ⟨keepb, state, value, palette, hsub, ?_, ?_, hvalue, hbound, hfaith⟩
    · have h := hloss
      rw [← hworld] at h
      simpa only [mul_assoc] using h
    · rw [hworld]
      exact hstates
  obtain ⟨keep, localKeep, state, value, palette, hkeep, hloss, hslices⟩ :=
    assemble_simultaneous_child_states Q hd hp selected level hlevel E hE hEbase K (fun _ => ε)
      (fun _ => pv) (fun b => unshearedPacketBase p b)
      (fun b z => MvPolynomial.eval (xp z.1 z.2) (p.R (anc b)) / δ (d.N k) (p.r (p.lev b)))
      (fun b => clockParentCode p (anc b) (Parent.SignalGraph.ancestorSignal (d.N k) p (anc b))
        graphMesh)
      (fun b c => (aA / q) • row (anc b) c) (fun _ => (aA / q) * Brow) ((6561 : ENNReal) * beta)
      hlocal
  exact ⟨keep, localKeep, state, value, palette, hkeep, hloss, hslices⟩

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
