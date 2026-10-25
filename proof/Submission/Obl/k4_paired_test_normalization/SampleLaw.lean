-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/SampleLaw.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.TestedSample
import Submission.Obl.k4_paired_test_normalization.TaggedPairs
import Submission.Obl.k4_paired_test_normalization.PairDeletion
import Submission.Obl.k4_paired_test_normalization.FrozenDensity

namespace Submission.Obl.k4_paired_test_normalization.NormalizationStep

open MeasureTheory Set

namespace TestedSample

variable {cv : Prop} {lam Nk : ℝ} {Wk : ℕ}
  {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
  {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
  {L dc a h : ℝ} {M D : ℕ} {ε : ℝ}
  (d : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε)

def world (s : Fin d.m) : Fin Wk := d.γ (d.frame s)

noncomputable def basePoint (s : Fin d.m) (p : PairPoint) : EuclideanSpace ℝ (Fin 3) :=
  base d.T ((d.j (d.frame s) : ℕ) : ℝ) d.κ (d.c (d.frame s))
    (d.u (d.frame s)) (d.Q (d.frame s)) p.1 p.2.1

noncomputable def hiddenPoint (s : Fin d.m) (p : PairPoint) : ℝ :=
  Bk (d.world s) * (x p.1 p.2.1) 3

lemma measurable_basePoint (s : Fin d.m) : Measurable (d.basePoint s) := by
  unfold basePoint base y x
  fun_prop

lemma common_world (s s' : Fin d.m) (p : PairPoint) (hp : p ∈ d.H s s') :
    d.world s = d.world s' := by
  have hfr := ((d.hH s s').2 p hp).2.2.2.2.1
  exact congrArg d.γ hfr.symm

lemma disjoint_columns : ∀ j, Pairwise fun i k => Disjoint (d.H i j) (d.H k j) := by
  intro j i k hik
  apply Set.disjoint_left.mpr
  intro p hi hk
  have hpi := (d.hH i j).2 p hi
  have hpk := (d.hH k j).2 p hk
  have hfr : d.frame i = d.frame k := hpi.2.2.2.2.1.symm.trans hpk.2.2.2.2.1
  exact Set.disjoint_left.mp
    (d.hdisj i k hik (congrArg d.γ hfr) (congrArg d.j hfr)) hpi.1 hpk.1

lemma raw_point_tests (s : Fin d.m) (p : PairPoint)
    (hp : p ∈ (⋃ j, d.H s j) ∪ (⋃ j, d.H j s)) :
    ‖d.basePoint s p‖ ≤ 1 / 8 ∧
    |MvPolynomial.eval (Fin.snoc (fun k => d.basePoint s p k) (d.hiddenPoint s p)) (d.P s)| ≤
      δ Nk L * Nk ^ a ∧
    Nk ^ (-a) ≤ |MvPolynomial.eval
      (Fin.snoc (fun k => d.basePoint s p k) (d.hiddenPoint s p))
      (MvPolynomial.pderiv (3 : Fin 4) (d.P s))| ∧
    |MvPolynomial.eval (Fin.snoc (fun k => d.basePoint s p k) (d.hiddenPoint s p))
      (MvPolynomial.pderiv (3 : Fin 4) (d.P s))| ≤ Nk ^ a := by
  have hpair (i j : Fin d.m) (hp' : p ∈ d.H i j) :
      ‖d.basePoint i p‖ ≤ 1 / 8 ∧ ∀ R : MvPolynomial (Fin 4) ℝ,
        R = d.P i ∨ R = d.P j →
        |MvPolynomial.eval (Fin.snoc (fun k => d.basePoint i p k) (d.hiddenPoint i p)) R| ≤
          δ Nk L * Nk ^ a ∧
        Nk ^ (-a) ≤ |MvPolynomial.eval
          (Fin.snoc (fun k => d.basePoint i p k) (d.hiddenPoint i p))
          (MvPolynomial.pderiv (3 : Fin 4) R)| ∧
        |MvPolynomial.eval (Fin.snoc (fun k => d.basePoint i p k) (d.hiddenPoint i p))
          (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ Nk ^ a := by
    have hh := (d.hH i j).2 p hp'
    have hs := (d.hS i).2.2 (p.1, p.2.1) hh.1
    have hbase := (hs.2.2.2.2 p.2.1 hs.2.2.2.1).2.2.1
    refine ⟨hbase, ?_⟩
    intro R hR
    have ht := hh.2.2.2.2.2.1 R hR
    exact ⟨ht.1, ht.2.1, ht.2.2.1⟩
  rcases hp with hp | hp
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    have hs := hpair s j hj
    exact ⟨hs.1, hs.2 (d.P s) (Or.inl rfl)⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    have hs := hpair i s hi
    have hfr := ((d.hH i s).2 p hi).2.2.2.2.1
    have hh := hs.2 (d.P s) (Or.inr rfl)
    simpa only [basePoint, hiddenPoint, world, hfr] using And.intro hs.1 hh

noncomputable def worldMeasure (γ : Fin Wk) : Measure PairPoint :=
  ENNReal.ofReal ((2 : ℝ) ^ d.T) ^ 2 • (νk γ).prod (volume.prod volume)

noncomputable def worldWeight (γ : Fin Wk) : ℝ := ωk γ / (2 : ℝ) ^ d.T

noncomputable def law : Measure (Fin Wk × PairPoint) :=
  taggedPairMeasure d.worldMeasure d.worldWeight

lemma worldWeight_nonneg (hω : ∀ γ, 0 ≤ ωk γ) (γ : Fin Wk) :
    0 ≤ d.worldWeight γ := div_nonneg (hω γ) (by positivity)

lemma base_density_source (s : Fin d.m) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : MeasurableSet U) :
    d.worldMeasure (d.world s) ((⋃ j, d.H s j) ∩ d.basePoint s ⁻¹' U) ≤
      ENNReal.ofReal (d.β s) * volume U := by
  dsimp [worldMeasure]
  have heq : ((⋃ j, d.H s j) ∩ d.basePoint s ⁻¹' U) =
      {p | (∃ j, p ∈ d.H s j) ∧ d.basePoint s p ∈ U} := by
    ext p
    simp
  rw [heq]
  exact ((d.hβ s).2.2 U hU).1

lemma base_density_witness (s : Fin d.m) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : MeasurableSet U) :
    d.worldMeasure (d.world s) ((⋃ j, d.H j s) ∩ d.basePoint s ⁻¹' U) ≤
      ENNReal.ofReal (d.β s) * volume U := by
  dsimp [worldMeasure]
  have heq : ((⋃ j, d.H j s) ∩ d.basePoint s ⁻¹' U) =
      {p | (∃ j, p ∈ d.H j s) ∧ d.basePoint s p ∈ U} := by
    ext p
    simp
  rw [heq]
  exact ((d.hβ s).2.2 U hU).2

lemma tagged_density_source (hω : ∀ γ, 0 ≤ ωk γ) (s : Fin d.m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    d.law ((⋃ j, tagPair d.world d.H s j) ∩
      (fun p : Fin Wk × PairPoint => d.basePoint s p.2) ⁻¹' U) ≤
      ENNReal.ofReal (d.worldWeight (d.world s) * d.β s) * volume U := by
  rw [tagPair_row]
  exact taggedPairMeasure_base_density d.worldMeasure d.worldWeight
    (d.worldWeight_nonneg hω) volume (d.world s) _
    (MeasurableSet.iUnion (fun j => (d.hH s j).1))
    (d.basePoint s) (d.measurable_basePoint s) (d.β s) (d.base_density_source s) hU

lemma tagged_density_witness (hω : ∀ γ, 0 ≤ ωk γ) (s : Fin d.m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    d.law ((⋃ j, tagPair d.world d.H j s) ∩
      (fun p : Fin Wk × PairPoint => d.basePoint s p.2) ⁻¹' U) ≤
      ENNReal.ofReal (d.worldWeight (d.world s) * d.β s) * volume U := by
  rw [tagPair_column d.world d.H d.common_world]
  exact taggedPairMeasure_base_density d.worldMeasure d.worldWeight
    (d.worldWeight_nonneg hω) volume (d.world s) _
    (MeasurableSet.iUnion (fun j => (d.hH j s).1))
    (d.basePoint s) (d.measurable_basePoint s) (d.β s) (d.base_density_witness s) hU

lemma weighted_beta_budget (hN : 1 ≤ Nk) (hω : ∀ γ, 0 ≤ ωk γ)
    (hωsum : ∑ γ, ωk γ = 1) :
    ∑ s, d.worldWeight (d.world s) * d.β s ≤ (Nk ^ a) ^ 2 := by
  classical
  have hq : 0 < (2 : ℝ) ^ d.T := by positivity
  have hs := weighted_fiber_budget
    (fun s : Fin d.m => (d.world s, d.j (d.frame s)))
    (fun q : Fin Wk × Fin (2 ^ d.T) => d.worldWeight q.1) d.β
    (Real.rpow_nonneg (by linarith : 0 ≤ Nk) _) d.σ_pos
    (fun q => d.worldWeight_nonneg hω q.1)
    (fun s => (d.hβ s).2.1) (fun q => by
      rcases q with ⟨γ₀, j₀⟩
      simpa only [world, Prod.mk.injEq] using d.hcount γ₀ j₀)
  have hsum : (∑ q : Fin Wk × Fin (2 ^ d.T), d.worldWeight q.1) = 1 := by
    rw [Fintype.sum_prod_type]
    have hin (γ : Fin Wk) : (∑ _j : Fin (2 ^ d.T), d.worldWeight γ) = ωk γ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        worldWeight, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
    simpa only [hin] using hωsum
  simpa only [hsum, mul_one] using hs

lemma worldWeight_measure_factor (hω : ∀ γ, 0 ≤ ωk γ) (γ : Fin Wk) :
    ENNReal.ofReal (d.worldWeight γ) * ENNReal.ofReal ((2 : ℝ) ^ d.T) ^ 2 =
      ENNReal.ofReal (ωk γ * (2 : ℝ) ^ d.T) := by
  have hw := d.worldWeight_nonneg hω γ
  have hq : 0 ≤ (2 : ℝ) ^ d.T := by positivity
  rw [pow_two, ← mul_assoc, ← ENNReal.ofReal_mul hw,
    ← ENNReal.ofReal_mul (mul_nonneg hw hq)]
  congr 1
  dsimp [worldWeight]
  field_simp

/-- The tagged normalized law has exactly the frozen original-world pair weights. -/
lemma weighted_rows_mass (hω : ∀ γ, 0 ≤ ωk γ) (H₀ : Fin d.m → Fin d.m → Set PairPoint)
    (hH₀ : ∀ i j, MeasurableSet (H₀ i j)) :
    (∑ s, d.law (⋃ j, tagPair d.world H₀ s j)) =
      ∑ s, ENNReal.ofReal (ωk (d.world s) * (2 : ℝ) ^ d.T) *
        ((νk (d.world s)).prod (volume.prod volume)) (⋃ j, H₀ s j) := by
  apply Finset.sum_congr rfl
  intro s _
  change taggedPairMeasure d.worldMeasure d.worldWeight (⋃ j, tagPair d.world H₀ s j) = _
  rw [tagPair_row_mass d.worldMeasure d.worldWeight d.world H₀ hH₀]
  change ENNReal.ofReal (d.worldWeight (d.world s)) *
    (ENNReal.ofReal ((2 : ℝ) ^ d.T) ^ 2 *
      ((νk (d.world s)).prod (volume.prod volume)) (⋃ j, H₀ s j)) = _
  rw [← mul_assoc, d.worldWeight_measure_factor hω]

lemma weighted_pullback_mass (hω : ∀ γ, 0 ≤ ωk γ)
    (K : Fin d.m → Fin d.m → Set (Fin Wk × PairPoint))
    (hKm : ∀ i j, MeasurableSet (K i j))
    (hK : ∀ i j, K i j ⊆ tagPair d.world d.H i j) :
    (∑ s, d.law (⋃ j, K s j)) =
      ∑ s, ENNReal.ofReal (ωk (d.world s) * (2 : ℝ) ^ d.T) *
        ((νk (d.world s)).prod (volume.prod volume))
          (⋃ j, (fun p => (d.world s, p)) ⁻¹' K s j) := by
  let H₀ (i j : Fin d.m) := (fun p => (d.world i, p)) ⁻¹' K i j
  have hH₀ (i j : Fin d.m) : MeasurableSet (H₀ i j) :=
    (hKm i j).preimage (measurable_const.prodMk measurable_id)
  have hm := d.weighted_rows_mass hω H₀ hH₀
  simpa only [H₀, tagPair_pullback d.world d.H K hK] using hm

end TestedSample

end Submission.Obl.k4_paired_test_normalization.NormalizationStep
