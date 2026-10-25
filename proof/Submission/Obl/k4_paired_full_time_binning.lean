import Mathlib
import ChallengeDeps
import Submission.Obl.k4_paired_full_time_binning.Bins
import Submission.Obl.k4_paired_full_time_binning.TimeSelection
set_option linter.unusedVariables false

/-!
# `Submission.k4_paired_full_time_binning`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_paired_full_time_binning`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_paired_full_time_binning/`
belong to this obligation.
-/

open MeasureTheory
open scoped RealInnerProductSpace
namespace Submission.Obl.k4_paired_full_time_binning

theorem _root_.Submission.k4_paired_full_time_binning : ((fun (B₀:Prop) => B₀) (∃ C:ℕ,2 ≤ C∧∀ (α:Type) [MeasurableSpace α] (ν:MeasureTheory.Measure α) (E:Set (α × ℝ)) (b v:α→ EuclideanSpace ℝ (Fin 2)) (n:ℕ) (normal:Fin n→ EuclideanSpace ℝ (Fin 2)) (intercept speed:Fin n→ ℝ) (tag:α × ℝ→ Fin n) (O:α × ℝ→ EuclideanSpace ℝ (Fin 3) × ℤ) (lst:(EuclideanSpace ℝ (Fin 3) × ℤ)→ Finset (Fin n)) (K H g:ℝ),MeasureTheory.IsProbabilityMeasure ν→ MeasurableSet E→ E ⊆ Set.univ ×ˢ Set.Icc (0:ℝ) 1→ Measurable b→ Measurable v→ Measurable tag→ Measurable O→ (∀ i,‖normal i‖ = 1∧ |intercept i| + |speed i| ≤ K)→ (∀ o,((lst o).card:ℝ) ≤ K)→ (∀ i,MeasurableSet {o | i ∈ lst o})→ (∀ p ∈ E,tag p ∈ lst (O p)∧‖b p.1‖ + ‖v p.1‖ ≤ K∧ |inner ℝ (normal (tag p)) (b p.1) - intercept (tag p)| ≤ K * g∧ |inner ℝ (normal (tag p)) (v p.1) - speed (tag p)| ≤ K * g)→ 2 ≤ K→ (C:ℝ) * K ^ 2 ≤ H→ 0 < g→ g * H ^ 2 ≤ 1→ (fun (μ:MeasureTheory.Measure (α × ℝ)) (pair:MeasureTheory.Measure (α × (ℝ × ℝ))) (bin:Fin n→ Fin 4→ ℤ) => 0 < μ Set.univ→ pair {p | (p.1,p.2.1) ∈ E∧(p.1,p.2.2) ∈ E∧g * H < min ‖normal (tag (p.1,p.2.1)) - normal (tag (p.1,p.2.2))‖ ‖normal (tag (p.1,p.2.1)) + normal (tag (p.1,p.2.2))‖} ≤ ENNReal.ofReal ((μ.real Set.univ) ^ 2 / 4)→ ∃ (t₀:ℝ) (m:ℕ) (rep:Fin m→ Fin n) (A:Fin m→ Set α) (L:(EuclideanSpace ℝ (Fin 3) × ℤ)→ Finset (Fin m)),t₀ ∈ Set.Icc (0:ℝ) 1∧(m:ℝ) ≤ ((C:ℝ) * K / (g * H ^ 2)) ^ C∧Function.Injective (fun i => bin (rep i))∧(∀ i,A i = {l | (l,t₀) ∈ E∧bin (tag (l,t₀)) = bin (rep i)})∧(∀ i,MeasurableSet (A i))∧(∀ i j,i ≠ j→ Disjoint (A i) (A j))∧(∀ i l,l ∈ A i→ ∀ t ∈ Set.Icc (0:ℝ) 1,|inner ℝ (normal (rep i)) (b l + t • v l) - intercept (rep i) - t * speed (rep i)| ≤ (C:ℝ) * K * (g * H ^ 2))∧(∀ o,((L o).card:ℝ) ≤ (C:ℝ) * K)∧(∀ i,MeasurableSet {o | i ∈ L o})∧ENNReal.ofReal ((μ.real Set.univ) ^ 2 / 4) ≤ μ {p | ∃ i,p.1 ∈ A i∧i ∈ L (O p)}) ((ν.prod MeasureTheory.volume).restrict E) (ν.prod (MeasureTheory.volume.prod MeasureTheory.volume)) (fun i => ![⌊normal i 0 / (g * H ^ 2)⌋,⌊normal i 1 / (g * H ^ 2)⌋,⌊intercept i / (g * H ^ 2)⌋,⌊speed i / (g * H ^ 2)⌋]))) := by
  classical
  refine ⟨8192, by norm_num, ?_⟩
  intro α _ ν E b v n normal intercept speed tag O lst K H g
    hν hE hEI hb hv htag hO hn hlst hmlst hfit hK hH hg hG
  dsimp only
  intro hp hbad
  norm_num only [Nat.cast_ofNat] at hH ⊢
  have : IsProbabilityMeasure ν := hν
  let G := g * H ^ 2
  let data : Fin n → Record := fun i => record (normal i) (intercept i) (speed i)
  let bin : Fin n → Code := fun i =>
    ![⌊normal i 0 / G⌋, ⌊normal i 1 / G⌋, ⌊intercept i / G⌋, ⌊speed i / G⌋]
  let μ := (ν.prod volume).restrict E
  have hH2 : 2 ≤ H := by nlinarith [sq_nonneg K]
  have hHK : 2 * K ≤ H := by nlinarith [sq_nonneg (K - 1)]
  have hGpos : 0 < G := by dsimp [G]; positivity
  have hgG : g ≤ G := by
    have hh : 1 ≤ H ^ 2 := by nlinarith
    exact (le_mul_of_one_le_right hg.le hh)
  have hdata : ∀ i k, |data i k| ≤ K := fun i =>
    record_bound (hn i).1 (hn i).2 (by linarith)
  have hbin (i : Fin n) : code G (record (normal i) (intercept i) (speed i)) = bin i :=
    code_record _ _ _ _
  have hmeasnormal : Measurable normal := measurable_of_finite _
  let R : Set (α × (ℝ × ℝ)) := {p |
    min ‖normal (tag (p.1, p.2.1)) - normal (tag (p.1, p.2.2))‖
      ‖normal (tag (p.1, p.2.1)) + normal (tag (p.1, p.2.2))‖ ≤ g * H}
  have hR : MeasurableSet R := measurableSet_le (by fun_prop) measurable_const
  have hbadR : (ν.prod (volume.prod volume))
      {p : α × (ℝ × ℝ) | (p.1, p.2.1) ∈ E ∧ (p.1, p.2.2) ∈ E ∧ p ∉ R} ≤
      ENNReal.ofReal ((μ.real Set.univ) ^ 2 / 4) := by
    simpa only [R, Set.mem_ofPred_eq, not_le] using hbad
  obtain ⟨t₀, ht₀, hmass⟩ := select_time ν hE hEI hR hp hbadR
  obtain ⟨m, rep, hm, hrep, hcover⟩ := representatives bin
  let A : Fin m → Set α := fun i => {l |
    (l, t₀) ∈ E ∧ bin (tag (l, t₀)) = bin (rep i)}
  let L := fun o => observationList (fun i => bin (rep i)) bin (lst o)
  have hmeasbin : Measurable bin := measurable_of_finite _
  have hA : ∀ i, MeasurableSet (A i) := by
    intro i
    exact (hE.preimage (by fun_prop)).inter (measurableSet_eq_fun (by fun_prop) measurable_const)
  have hcount : (m : ℝ) ≤ (7 * K / G) ^ 4 := by
    rw [hm]
    simpa only [data, hbin] using card_codes data hGpos hG (by linarith) hdata
  have hbase : 1 ≤ 8192 * K / G := (le_div_iff₀ hGpos).mpr (by
    have : G ≤ 1 := hG
    linarith)
  refine ⟨t₀, m, rep, A, L, ht₀, ?_, hrep, (fun _ => rfl), hA, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (m : ℝ) ≤ (7 * K / G) ^ 4 := hcount
      _ ≤ (8192 * K / G) ^ 4 := by gcongr; linarith
      _ ≤ (8192 * K / G) ^ 8192 := pow_le_pow_right₀ hbase (by norm_num)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro l hli hlj
    apply hij
    exact hrep (hli.2.symm.trans hlj.2)
  · intro i l hli t ht
    have h := hfit (l, t₀) hli.1
    exact (same_code_fit hGpos hgG hK
      (by simpa only [hbin] using hli.2) h.2.1 h.2.2.1 h.2.2.2 ht).trans
      (by
        change 6 * K * G ≤ 8192 * K * G
        have hnonneg : 0 ≤ K * G := by positivity
        nlinarith)
  · intro o
    have hh : ((L o).card : ℝ) ≤ 4802 * ((lst o).card : ℝ) := by
      exact_mod_cast card_observationList (fun i => bin (rep i)) bin hrep (lst o)
    exact hh.trans ((mul_le_mul_of_nonneg_left (hlst o) (by norm_num)).trans
      (by nlinarith))
  · exact measurable_observationList (fun i => bin (rep i)) bin lst hmlst
  · apply hmass.trans
    apply measure_mono_ae
    filter_upwards [ae_restrict_mem hE] with p hpE
    intro hpS
    obtain ⟨i, hi⟩ := hcover (tag (p.1, t₀))
    refine ⟨i, ⟨hpS.1, hi.symm⟩, ?_⟩
    apply (mem_observationList _ _ _ _).mpr
    refine ⟨tag p, (hfit p hpE).1, ?_⟩
    rw [hi]
    have h0 := hfit (p.1, t₀) hpS.1
    have h1 := hfit p hpE
    have hnear := good_records hg hH2 hHK h0.2.1 h0.2.2.1 h0.2.2.2
      h1.2.2.1 h1.2.2.2 hpS.2
    simpa only [hbin] using code_mem_nearby hGpos hnear


end Submission.Obl.k4_paired_full_time_binning
