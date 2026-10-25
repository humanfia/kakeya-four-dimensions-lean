-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.ExactMultiplicity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs
import Submission.WZ.Obl.wz_measurable_angular_selection
import Submission.WZ.Obl.wz_terminal_grains_restoration.Basic

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- If at least `M` shadings pass through each point of their union, one can
measurably retain exactly `M`, preserving the whole union. -/
theorem exact_multiplicity_refinement {n M : ℕ} (hM : 0 < M)
    (Y : Fin n → Set V) (hY : ∀ i, MeasurableSet (Y i))
    (hlow : ∀ p, (∃ i, p ∈ Y i) → (M : ℝ) ≤ q n {i | p ∈ Y i}) :
    ∃ Z : Fin n → Set V,
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      {p | ∃ i, p ∈ Z i} = {p | ∃ i, p ∈ Y i} ∧
      ∀ p, (∃ i, p ∈ Z i) → q n {i | p ∈ Z i} = M := by
  classical
  choose keep hkeep hcard using fun s : Finset (Fin n) =>
    Finset.exists_subset_card_eq (min_le_right M s.card)
  let pat (p : V) : Finset (Fin n) := Finset.univ.filter (fun i => p ∈ Y i)
  have hpat (p : V) (i : Fin n) : i ∈ pat p ↔ p ∈ Y i := by simp [pat]
  have hpat_count (p : V) : q n {i | p ∈ Y i} = ((pat p).card : ℝ) := by
    have he : {i | p ∈ Y i} = (↑(pat p) : Set (Fin n)) := by ext i; simp [pat]
    simp only [q, he, Set.ncard_coe_finset]
  let Z (i : Fin n) : Set V := {p | i ∈ keep (pat p)}
  have hZmeas (i : Fin n) : MeasurableSet (Z i) :=
    WangZahlLot.Obl.wz_measurable_angular_selection.measurableSet_pattern hY pat hpat
      (fun s => i ∈ keep s)
  have hZY (i : Fin n) : Z i ⊆ Y i := by
    intro p hp
    exact (hpat p i).mp (hkeep (pat p) hp)
  have hkeep_count (p : V) (hp : ∃ i, p ∈ Y i) : (keep (pat p)).card = M := by
    rw [hcard]
    apply min_eq_left
    have hh := hlow p hp
    rw [hpat_count] at hh
    exact_mod_cast hh
  have hZcount (p : V) : q n {i | p ∈ Z i} = ((keep (pat p)).card : ℝ) := by
    have he : {i | p ∈ Z i} = (↑(keep (pat p)) : Set (Fin n)) := by
      ext i
      rfl
    simp only [q, he, Set.ncard_coe_finset]
  refine ⟨Z, fun i => ⟨hZmeas i, hZY i⟩, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, hZY i hi⟩
    · intro hp
      have hh : (keep (pat p)).Nonempty := Finset.card_pos.mp (by rw [hkeep_count p hp]; exact hM)
      obtain ⟨i, hi⟩ := hh
      exact ⟨i, hi⟩
  · intro p hp
    obtain ⟨i, hi⟩ := hp
    rw [hZcount, hkeep_count p ⟨i, hZY i hi⟩]

/-- A pointwise comparison of real cardinalities gives the same comparison
of summed shading volumes. -/
theorem mass_of_multiplicity_fraction {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    {Y Z : Fin n → Set V} (hY : ∀ i, MeasurableSet (Y i))
    (hZ : ∀ i, MeasurableSet (Z i))
    (hfrac : ∀ p, q n {i | p ∈ Y i} ≤ C * q n {i | p ∈ Z i}) :
    (∑ i, μ (Y i)) ≤ O C * ∑ i, μ (Z i) := by
  classical
  have hcount (W : Fin n → Set V) (p : V) :
      q n {i | p ∈ W i} =
        (WangZahlLot.Obl.wz_terminal_grains_restoration.mult Finset.univ W p : ℝ) := by
    have he : {i | p ∈ W i} = (↑(Finset.univ.filter (fun i => p ∈ W i)) : Set (Fin n)) := by
      ext i
      simp
    simp only [q, he, Set.ncard_coe_finset, WangZahlLot.Obl.wz_terminal_grains_restoration.mult]
  rw [WangZahlLot.Obl.wz_terminal_grains_restoration.sum_measure_eq_lintegral_mult
    volume Finset.univ Y (fun i _ => hY i),
    WangZahlLot.Obl.wz_terminal_grains_restoration.sum_measure_eq_lintegral_mult
      volume Finset.univ Z (fun i _ => hZ i)]
  calc
    _ ≤ ∫⁻ p, O C *
        (WangZahlLot.Obl.wz_terminal_grains_restoration.mult Finset.univ Z p : ENNReal) := by
      apply lintegral_mono
      intro p
      have hh := hfrac p
      rw [hcount Y, hcount Z] at hh
      have he := ENNReal.ofReal_le_ofReal hh
      simpa only [O, ENNReal.ofReal_mul hC, ENNReal.ofReal_natCast] using he
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Equalizing multiplicities in a bounded interval preserves its entire
union and loses at most the ratio of the interval in mass and broadness. -/
theorem exact_multiplicity_with_mass {n M : ℕ} {C : ℝ} (hM : 0 < M) (hC : 0 ≤ C)
    (Y : Fin n → Set V) (hY : ∀ i, MeasurableSet (Y i))
    (hinterval : ∀ p, (∃ i, p ∈ Y i) →
      (M : ℝ) ≤ q n {i | p ∈ Y i} ∧ q n {i | p ∈ Y i} ≤ C * M) :
    ∃ Z : Fin n → Set V,
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      {p | ∃ i, p ∈ Z i} = {p | ∃ i, p ∈ Y i} ∧
      (∀ p, (∃ i, p ∈ Z i) → q n {i | p ∈ Z i} = M) ∧
      (∀ p, q n {i | p ∈ Y i} ≤ C * q n {i | p ∈ Z i}) ∧
      (∑ i, μ (Y i)) ≤ O C * ∑ i, μ (Z i) := by
  obtain ⟨Z, hZ, hunion, hexact⟩ := exact_multiplicity_refinement hM Y hY
    (fun p hp => (hinterval p hp).1)
  have hfrac : ∀ p, q n {i | p ∈ Y i} ≤ C * q n {i | p ∈ Z i} := by
    intro p
    by_cases hp : ∃ i, p ∈ Y i
    · have hpZ : ∃ i, p ∈ Z i := by
        change p ∈ {p | ∃ i, p ∈ Z i}
        rw [hunion]
        exact hp
      rw [hexact p hpZ]
      exact (hinterval p hp).2
    · have he : {i | p ∈ Y i} = (∅ : Set (Fin n)) := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hi => hp ⟨i, hi⟩
      simp only [q, he, Set.ncard_empty, Nat.cast_zero]
      positivity
  exact ⟨Z, hZ, hunion, hexact, hfrac,
    mass_of_multiplicity_fraction hC hY (fun i => (hZ i).1) hfrac⟩

end WangZahlLot.Obl.wz_coarse_grains_assembly
