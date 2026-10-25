-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.ColorRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs
import Submission.WZ.Obl.wz_measurable_angular_selection
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize
import Submission.WZ.Obl.wz_terminal_grains_restoration.Basic

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- One class of a finite coloring admits measurable subshadings that keep
mass and a fixed fraction of the original multiplicity at every retained
point. The two losses are at most the square of the number of colors and
the number of colors, respectively. -/
theorem color_refinement {n K : ℕ} (hK : 0 < K)
    (color : Fin n → Fin K) (Y : Fin n → Set V) (hY : ∀ i, MeasurableSet (Y i)) :
    ∃ (a : Fin K) (Z : Fin n → Set V),
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (color i ≠ a → Z i = ∅)) ∧
      (∑ i, μ (Y i)) ≤ (K : ENNReal) ^ 2 * ∑ i, μ (Z i) ∧
      ∀ p, (∃ i, p ∈ Z i) → q n {i | p ∈ Y i} ≤ K * q n {i | p ∈ Z i} := by
  classical
  choose pick hpick using fun T : Finset (Fin n) =>
    WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color hK T color (fun _ => 1)
  let keep (T : Finset (Fin n)) := T.filter (fun i => color i = pick T)
  have hkeep (T : Finset (Fin n)) : T.card ≤ K * (keep T).card := by
    have he : (T.card : ENNReal) ≤ (K : ENNReal) * (keep T).card := by
      simpa only [keep, Finset.sum_const, nsmul_eq_mul, mul_one] using hpick T
    exact_mod_cast he
  let pat (p : V) := Finset.univ.filter (fun i => p ∈ Y i)
  have hpat : ∀ p i, i ∈ pat p ↔ p ∈ Y i := by intro p i; simp [pat]
  let W (i : Fin n) : Set V := {p | i ∈ keep (pat p)}
  have hWm : ∀ i, MeasurableSet (W i) := fun i =>
    WangZahlLot.Obl.wz_measurable_angular_selection.measurableSet_pattern hY pat hpat
      (fun T => i ∈ keep T)
  have hWsub : ∀ i, W i ⊆ Y i := by
    intro i p hp
    exact (hpat p i).mp (Finset.mem_of_mem_filter _ hp)
  have hmultY (p : V) :
      WangZahlLot.Obl.wz_terminal_grains_restoration.mult Finset.univ Y p = (pat p).card := rfl
  have hmultW (p : V) :
      WangZahlLot.Obl.wz_terminal_grains_restoration.mult Finset.univ W p = (keep (pat p)).card := by
    unfold WangZahlLot.Obl.wz_terminal_grains_restoration.mult
    congr 1
    ext i
    simp [W]
  have hmassW : (∑ i, μ (Y i)) ≤ (K : ENNReal) * ∑ i, μ (W i) := by
    rw [WangZahlLot.Obl.wz_terminal_grains_restoration.sum_measure_eq_lintegral_mult
      volume Finset.univ Y (fun i _ => hY i),
      WangZahlLot.Obl.wz_terminal_grains_restoration.sum_measure_eq_lintegral_mult
        volume Finset.univ W (fun i _ => hWm i)]
    calc
      _ ≤ ∫⁻ p, (K : ENNReal) *
          (WangZahlLot.Obl.wz_terminal_grains_restoration.mult Finset.univ W p : ENNReal) := by
        apply lintegral_mono
        intro p
        dsimp only
        rw [hmultY, hmultW]
        exact_mod_cast hkeep (pat p)
      _ = _ := lintegral_const_mul' _ _ (by simp)
  obtain ⟨a, ha⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color
    hK Finset.univ color (fun i => μ (W i))
  let Z (i : Fin n) : Set V := if color i = a then W i else ∅
  have hZsum : (∑ i, μ (Z i)) = ∑ i ∈ Finset.univ.filter (fun i => color i = a), μ (W i) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : color i = a <;> simp [Z, hi, μ]
  refine ⟨a, Z, ?_, ?_, ?_⟩
  · intro i
    constructor
    · dsimp [Z]
      split_ifs <;> simp_all only [MeasurableSet.empty]
    · constructor
      · intro p hp
        by_cases hi : color i = a
        · exact hWsub i (by simpa only [Z, ite_eq_left hi] using hp)
        · simp only [Z, ite_eq_right hi, Set.mem_empty_iff_false] at hp
      · intro hi
        simp only [Z, ite_eq_right hi]
  · rw [hZsum, pow_two, mul_assoc]
    exact hmassW.trans (mul_le_mul_right ha (K : ENNReal))
  · intro p hp
    obtain ⟨i₀, hi₀⟩ := hp
    have hc : color i₀ = a := by
      by_contra hn
      simp only [Z, ite_eq_right hn, Set.mem_empty_iff_false] at hi₀
    have hi₀' : i₀ ∈ keep (pat p) := by simpa only [Z, ite_eq_left hc, W, Set.mem_ofPred_eq] using hi₀
    have hpick : pick (pat p) = a := (Finset.mem_filter.mp hi₀').2.symm.trans hc
    have hZp : {i | p ∈ Z i} = (↑(keep (pat p)) : Set (Fin n)) := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.mem_coe]
      constructor
      · intro hi
        by_cases hc : color i = a
        · simpa only [Z, ite_eq_left hc, W, Set.mem_ofPred_eq, Finset.mem_coe] using hi
        · simp only [Z, ite_eq_right hc, Set.mem_empty_iff_false] at hi
      · intro hi
        have hc : color i = a := (Finset.mem_filter.mp hi).2.trans hpick
        simpa only [Z, ite_eq_left hc, W, Set.mem_ofPred_eq] using hi
    have hYp : {i | p ∈ Y i} = (↑(pat p) : Set (Fin n)) := by ext i; simp [pat]
    change (({i | p ∈ Y i} : Set (Fin n)).ncard : ℝ) ≤
      K * (({i | p ∈ Z i} : Set (Fin n)).ncard : ℝ)
    rw [hYp, hZp, Set.ncard_coe_finset, Set.ncard_coe_finset]
    exact_mod_cast hkeep (pat p)

/-- Retaining a pointwise fraction of the tubes preserves broadness, with
the reciprocal fraction as the only loss. -/
theorem broad_of_pointwise_fraction {δ ρ l β K : ℝ} {n : ℕ}
    {v : Fin n → V} {Y Z : Fin n → Set V}
    (hδ : 0 ≤ δ) (hρ : 0 < ρ) (hl : 0 ≤ l)
    (hZY : ∀ i, Z i ⊆ Y i)
    (hfrac : ∀ p, (∃ i, p ∈ Z i) → q n {i | p ∈ Y i} ≤ K * q n {i | p ∈ Z i})
    (hbr : ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        l * (r / ρ) ^ β * q n {i | p ∈ Y i}) :
    ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        (K * l) * (r / ρ) ^ β * q n {i | p ∈ Z i} := by
  intro p u r hu hdr hrρ
  by_cases hp : ∃ i, p ∈ Z i
  · have hcap : q n {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        q n {i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} := by
      apply Nat.cast_le.mpr
      exact Set.ncard_le_ncard (fun i hi => ⟨hZY i hi.1, hi.2⟩) (Set.toFinite _)
    calc
      _ ≤ l * (r / ρ) ^ β * q n {i | p ∈ Y i} := hcap.trans (hbr p u r hu hdr hrρ)
      _ ≤ l * (r / ρ) ^ β * (K * q n {i | p ∈ Z i}) :=
        mul_le_mul_of_nonneg_left (hfrac p hp)
          (mul_nonneg hl (Real.rpow_nonneg (div_nonneg (hδ.trans hdr) hρ.le) _))
      _ = _ := by ring
  · have hZ : {i | p ∈ Z i} = (∅ : Set (Fin n)) := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hi => hp ⟨i, hi⟩
    have hcap : {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} = (∅ : Set (Fin n)) := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hi => hp ⟨i, hi.1⟩
    simp only [q, hZ, hcap, Set.ncard_empty, Nat.cast_zero, mul_zero, le_refl]

end WangZahlLot.Obl.wz_coarse_grains_assembly
