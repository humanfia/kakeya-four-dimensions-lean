-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/SatMarkov.lean
import Mathlib

/-!
# Crossing counts under a density cap

For a measure `μ` whose image under an observation map `o` has density `g`
against `lam`, the observations with density at most `cap` that lie in more than
`H` of the sets `S b` have mass at most `cap * ∑ lam(S b) / H` (Markov's
inequality, as in the proof of paper Lemma 2.8).  We also record the
multiplicity-two bound used to sum restrictions over charts whose closed time
blocks may share an endpoint.
-/

namespace Submission.Obl.k4_terminal_label_saturation

open MeasureTheory Set
open scoped ENNReal

/-- The number of sets of a finite family containing a point, as an extended real. -/
noncomputable def crossCount {O ι : Type*} [Fintype ι] (S : ι → Set O) (q : O) : ℝ≥0∞ :=
  ∑ b, (S b).indicator 1 q

theorem crossCount_eq_card {O ι : Type*} [Fintype ι] (S : ι → Set O) (q : O) :
    crossCount S q = (({b | q ∈ S b}.ncard : ℕ) : ℝ≥0∞) := by
  classical
  unfold crossCount
  simp only [indicator_apply, Pi.one_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext b
  simp

theorem crossing_capped_sum_le {Ω O ι : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    [Fintype ι] (μ : Measure Ω) {o : Ω → O} (ho : Measurable o) (lam : Measure O)
    {g : O → ℝ≥0∞} (hg : Measurable g) (hmap : μ.map o = lam.withDensity g)
    (S : ι → Set O) (hS : ∀ b, MeasurableSet (S b)) (cap : ℝ≥0∞) :
    ∑ b, μ (o ⁻¹' ({q | g q ≤ cap} ∩ S b)) ≤ cap * ∑ b, lam (S b) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  have hA : MeasurableSet ({q | g q ≤ cap} ∩ S b) :=
    (measurableSet_le hg measurable_const).inter (hS b)
  rw [← Measure.map_apply ho hA, hmap, withDensity_apply _ hA]
  calc ∫⁻ q in {q | g q ≤ cap} ∩ S b, g q ∂lam ≤ ∫⁻ _ in {q | g q ≤ cap} ∩ S b, cap ∂lam :=
        setLIntegral_mono' hA (fun q hq => hq.1)
    _ = cap * lam ({q | g q ≤ cap} ∩ S b) := setLIntegral_const _ _
    _ ≤ cap * lam (S b) := mul_le_mul' le_rfl (measure_mono inter_subset_right)

/-- Markov's inequality for crossing counts under a density cap. -/
theorem crossing_markov {Ω O ι : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    [Fintype ι] (μ : Measure Ω) {o : Ω → O} (ho : Measurable o) (lam : Measure O)
    {g : O → ℝ≥0∞} (hg : Measurable g) (hmap : μ.map o = lam.withDensity g)
    (S : ι → Set O) (hS : ∀ b, MeasurableSet (S b)) (cap H : ℝ≥0∞) :
    H * μ {p | g (o p) ≤ cap ∧ H < crossCount S (o p)} ≤ cap * ∑ b, lam (S b) := by
  set A : ι → Set Ω := fun b => o ⁻¹' ({q | g q ≤ cap} ∩ S b) with hAdef
  have hA : ∀ b, MeasurableSet (A b) := fun b =>
    ho ((measurableSet_le hg measurable_const).inter (hS b))
  set f : Ω → ℝ≥0∞ := fun p => ∑ b, (A b).indicator 1 p with hf
  have hfm : Measurable f :=
    Finset.measurable_sum _ (fun b _ => measurable_one.indicator (hA b))
  have hint : ∫⁻ p, f p ∂μ = ∑ b, μ (A b) := by
    rw [hf, lintegral_finsetSum _ (fun b _ => measurable_one.indicator (hA b))]
    apply Finset.sum_congr rfl
    intro b _
    exact lintegral_indicator_one (hA b)
  have hsub : {p | g (o p) ≤ cap ∧ H < crossCount S (o p)} ⊆ {p | H ≤ f p} := by
    rintro p ⟨hcap, hH⟩
    have heq : f p = crossCount S (o p) := by
      simp only [hf, crossCount]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : o p ∈ S b
      · have hpA : p ∈ A b := ⟨hcap, hb⟩
        rw [indicator_of_mem hpA, indicator_of_mem hb]
        rfl
      · have hpA : p ∉ A b := fun h => hb h.2
        rw [indicator_of_notMem hpA, indicator_of_notMem hb]
    show H ≤ f p
    rw [heq]
    exact hH.le
  calc H * μ {p | g (o p) ≤ cap ∧ H < crossCount S (o p)} ≤ H * μ {p | H ≤ f p} :=
        mul_le_mul' le_rfl (measure_mono hsub)
    _ ≤ ∫⁻ p, f p ∂μ := mul_meas_ge_le_lintegral hfm H
    _ = ∑ b, μ (A b) := hint
    _ ≤ cap * ∑ b, lam (S b) := crossing_capped_sum_le μ ho lam hg hmap S hS cap

/-- Sets covering every point at most twice: restricting them to `Y` and summing
costs at most twice the mass of `Y`. -/
theorem sum_measure_inter_le_two {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (F : ι → Set X) (hF : ∀ b, MeasurableSet (F b))
    (hmult : ∀ p, ∑ b, (F b).indicator (1 : X → ℝ≥0∞) p ≤ 2)
    (Y : Set X) (hY : MeasurableSet Y) :
    ∑ b, μ (F b ∩ Y) ≤ 2 * μ Y := by
  have hFY : ∀ b, MeasurableSet (F b ∩ Y) := fun b => (hF b).inter hY
  calc ∑ b, μ (F b ∩ Y) = ∑ b, ∫⁻ p, (F b ∩ Y).indicator 1 p ∂μ := by
        apply Finset.sum_congr rfl
        intro b _
        exact (lintegral_indicator_one (hFY b)).symm
    _ = ∫⁻ p, ∑ b, (F b ∩ Y).indicator 1 p ∂μ :=
        (lintegral_finsetSum _ (fun b _ => measurable_one.indicator (hFY b))).symm
    _ ≤ ∫⁻ p, Y.indicator (fun _ => (2 : ℝ≥0∞)) p ∂μ := by
        apply lintegral_mono
        intro p
        by_cases hp : p ∈ Y
        · rw [indicator_of_mem hp]
          calc ∑ b, (F b ∩ Y).indicator (1 : X → ℝ≥0∞) p
              = ∑ b, (F b).indicator (1 : X → ℝ≥0∞) p := by
                apply Finset.sum_congr rfl
                intro b _
                by_cases hb : p ∈ F b
                · rw [indicator_of_mem (show p ∈ F b ∩ Y from ⟨hb, hp⟩), indicator_of_mem hb]
                · rw [indicator_of_notMem (fun h => hb h.1), indicator_of_notMem hb]
            _ ≤ 2 := hmult p
        · rw [indicator_of_notMem hp]
          apply le_of_eq
          apply Finset.sum_eq_zero
          intro b _
          exact indicator_of_notMem (fun h => hp h.2) _
    _ = 2 * μ Y := lintegral_indicator_const hY 2

/-- A time lies in at most two closed dyadic blocks of one generation. -/
theorem card_dyadic_blocks_le_two (T : ℕ) (t : ℝ) :
    ({j : Fin (2 ^ T) | t ∈ Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T)}.ncard)
      ≤ 2 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  set m : ℤ := ⌊t * (2 : ℝ) ^ T⌋ with hm
  have hsub : {j : Fin (2 ^ T) | t ∈ Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T)}
      ⊆ {j : Fin (2 ^ T) | (j : ℤ) = m ∨ (j : ℤ) = m - 1} := by
    intro j hj
    obtain ⟨h1, h2⟩ := hj
    have h1' : (j : ℝ) ≤ t * (2 : ℝ) ^ T := by
      rw [div_le_iff₀ hpos] at h1; linarith
    have h2' : t * (2 : ℝ) ^ T ≤ (j : ℝ) + 1 := by
      rw [le_div_iff₀ hpos] at h2; linarith
    have hj1 : (j : ℤ) ≤ m := Int.le_floor.mpr (by exact_mod_cast h1')
    have hj2 : m ≤ (j : ℤ) + 1 := by
      have := Int.floor_le (t * (2 : ℝ) ^ T)
      have : (m : ℝ) ≤ (j : ℝ) + 1 := by rw [hm]; linarith
      exact_mod_cast this
    simp only [mem_ofPred_eq]
    omega
  have hfin : ({j : Fin (2 ^ T) | (j : ℤ) = m ∨ (j : ℤ) = m - 1}).ncard ≤ 2 := by
    classical
    have hsub2 : {j : Fin (2 ^ T) | (j : ℤ) = m ∨ (j : ℤ) = m - 1} ⊆
        (({j : Fin (2 ^ T) | (j : ℤ) = m}.toFinset ∪
          {j : Fin (2 ^ T) | (j : ℤ) = m - 1}.toFinset : Finset (Fin (2 ^ T))) : Set _) := by
      intro j hj
      simp only [mem_ofPred_eq] at hj
      simp only [Finset.coe_union, Set.coe_toFinset, mem_union, mem_ofPred_eq]
      exact hj
    have hone (a : ℤ) : ({j : Fin (2 ^ T) | (j : ℤ) = a}.toFinset).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      simp only [Set.mem_toFinset, mem_ofPred_eq] at hx hy
      exact Fin.ext (by omega)
    calc ({j : Fin (2 ^ T) | (j : ℤ) = m ∨ (j : ℤ) = m - 1}).ncard
        ≤ ((({j : Fin (2 ^ T) | (j : ℤ) = m}.toFinset ∪
          {j : Fin (2 ^ T) | (j : ℤ) = m - 1}.toFinset : Finset (Fin (2 ^ T))) : Set _)).ncard :=
          Set.ncard_le_ncard hsub2 (Finset.finite_toSet _)
      _ = ({j : Fin (2 ^ T) | (j : ℤ) = m}.toFinset ∪
          {j : Fin (2 ^ T) | (j : ℤ) = m - 1}.toFinset).card := Set.ncard_coe_finset _
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 1 + 1 := add_le_add (hone m) (hone (m - 1))
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans hfin

end Submission.Obl.k4_terminal_label_saturation
