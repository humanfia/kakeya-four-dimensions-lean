-- Adapted from this LOT tree, o206 (`k4_coarse_pair_frame_preparation`), session x0709,
-- commit ccf298c0, files Submission/Obl/k4_coarse_pair_frame_preparation/PairSwap.lean,
-- JensenCoverage.lean (`selected_source_mass_le_one`), PairExceptions.lean,
-- OppositeDerivative.lean, NativeDerivativeBudget.lean, NativeDerivativeSource.lean and
-- PairRelabel.lean. OppositeDerivative.lean says it was adapted there from o156, session x0524,
-- commit 00e5abee, Submission/Obl/k4_terminal_local_sheet_pairing/OppositeDerivative.lean.
-- The block-level Jensen bound `block_pair_lower` is new here (same method as x0709's
-- `source_indexed_pair_lower`, with the witness time in the source's own block union).
import Submission.Obl.k4_homogeneous_native_pair_preparation.Interface
import Submission.Obl.k4_scalar_angular_pair_agreement.AllPairs
import Submission.Obl.k4_scalar_angular_pair_agreement.PairTail
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal
import Submission.Obl.k4_quadratic_finite_greedy_cover.DerivativeLoss
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection
import Submission.Obl.k4_scalar_normalized_exact_refinement.Mass
import Submission.Lib.K4GoodTimes

/-!
# Original-law measure estimates for two-time pairs

Two-time pairs `(l, t₁, t₂)` carry the unconditioned law `ν ⊗ vol ⊗ vol` of their world.
This file collects the estimates used to build the pair masks of a native sample:

* `block_pair_lower`: Jensen over worlds and coarse time blocks;
* `source_indexed_pair_exception_le`: a one-time exceptional set costs twice its
  original weighted mass, with no label-count factor;
* `native_opposite_derivative_budget`, `native_source_derivative_budget`: opposite-time
  failures of an affine hidden derivative cost `4 * ε * K` of the selected mass;
* `weighted_assignment_cover_le`: relabel disjoint events by a covering family.
-/

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Set MvPolynomial
open scoped ENNReal BigOperators
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_angular_pair_agreement (pairSet measurableSet_pairSet)

/-! ### Measurability of trajectory evaluations -/

theorem measurable_x_fun : Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => x p.1 p.2) := by
  rw [measurable_pi_iff]
  intro i
  fin_cases i <;> simp [x] <;> fun_prop

theorem measurable_eval_x (R : MvPolynomial (Fin 4) ℝ) :
    Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => eval (x p.1 p.2) R) :=
  (continuous_eval R).measurable.comp measurable_x_fun

/-- Evaluation at the first time of a pair. -/
theorem measurable_eval_x_fst (R : MvPolynomial (Fin 4) ℝ) :
    Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) => eval (x p.1 p.2.1) R) := by
  have h : Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) => x p.1 p.2.1) := by
    rw [measurable_pi_iff]
    intro i
    fin_cases i <;> simp [x] <;> fun_prop
  exact (continuous_eval R).measurable.comp h

/-- Evaluation at the second time of a pair. -/
theorem measurable_eval_x_snd (R : MvPolynomial (Fin 4) ℝ) :
    Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) => eval (x p.1 p.2.2) R) := by
  have h : Measurable (fun p : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ) => x p.1 p.2.2) := by
    rw [measurable_pi_iff]
    intro i
    fin_cases i <;> simp [x] <;> fun_prop
  exact (continuous_eval R).measurable.comp h

/-! ### Swapping the two times -/

def swapTimes {X : Type*} (p : X × (ℝ × ℝ)) : X × (ℝ × ℝ) :=
  (p.1, p.2.2, p.2.1)

theorem measurable_swapTimes {X : Type*} [MeasurableSpace X] :
    Measurable (swapTimes (X := X)) :=
  measurable_fst.prodMk (measurable_snd.snd.prodMk measurable_snd.fst)

theorem measurePreserving_swapTimes {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] :
    MeasurePreserving swapTimes (ν.prod (volume.prod volume))
      (ν.prod (volume.prod volume)) :=
  (MeasurePreserving.id ν).prod Measure.measurePreserving_swap

theorem measure_swapTimes_preimage {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {F : Set (X × (ℝ × ℝ))} (hF : MeasurableSet F) :
    (ν.prod (volume.prod volume)) (swapTimes ⁻¹' F) =
      (ν.prod (volume.prod volume)) F :=
  (measurePreserving_swapTimes ν).measure_preimage hF.nullMeasurableSet

/-! ### Jensen over worlds and coarse blocks -/

/-- The union of the sources of world `w` in coarse block `b`. -/
def blockUnion {X ι : Type*} {W K : ℕ} (γ : ι → Fin W) (J : ι → Fin K)
    (S : ι → Set (X × ℝ)) (w : Fin W) (b : Fin K) : Set (X × ℝ) :=
  {p | ∃ s, (γ s, J s) = (w, b) ∧ p ∈ S s}

theorem measurableSet_blockUnion {X ι : Type*} [MeasurableSpace X] [Finite ι]
    {W K : ℕ} (γ : ι → Fin W) (J : ι → Fin K) (S : ι → Set (X × ℝ))
    (hS : ∀ s, MeasurableSet (S s)) (w : Fin W) (b : Fin K) :
    MeasurableSet (blockUnion γ J S w b) := by
  classical
  have : blockUnion γ J S w b = ⋃ s, ({_p | (γ s, J s) = (w, b)} ∩ S s) := by
    ext p
    simp [blockUnion]
  rw [this]
  exact MeasurableSet.iUnion fun s => (MeasurableSet.const _).inter (hS s)

/-- The source-indexed two-time masses with the witness time in the source's own block
union are at least the square of the selected one-time mass. The block normalization and
all original world weights are retained. -/
theorem block_pair_lower {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (W T : ℕ) (ν : Fin W → Measure X) [∀ w, IsProbabilityMeasure (ν w)]
    (ω : Fin W → ℝ≥0∞) (hω : ∑ w, ω w = 1)
    (γ : ι → Fin W) (J : ι → Fin (2 ^ T))
    (S : ι → Set (X × ℝ)) (hS : ∀ s, MeasurableSet (S s))
    (hdisj : ∀ s s', s ≠ s' → γ s = γ s' → J s = J s' → Disjoint (S s) (S s'))
    {m₀ : ℝ≥0∞} (hm₀ : m₀ ≠ ⊤)
    (hmass : m₀ ≤ ∑ s, ω (γ s) * ((ν (γ s)).prod volume) (S s)) :
    m₀ ^ 2 ≤ ∑ s, ω (γ s) * (2 ^ T : ℕ) *
      ((ν (γ s)).prod (volume.prod volume))
        (pairSet (S s) (blockUnion γ J S (γ s) (J s))) := by
  classical
  let D : Fin W → Fin (2 ^ T) → Set (X × ℝ) := blockUnion γ J S
  have hD (w : Fin W) (b : Fin (2 ^ T)) : MeasurableSet (D w b) :=
    measurableSet_blockUnion γ J S hS w b
  have hsplit : (∑ w, ∑ b, ω w * ((ν w).prod volume) (D w b)) =
      ∑ s, ω (γ s) * ((ν (γ s)).prod volume) (S s) := by
    have h := Submission.Obl.k4_quadratic_finite_greedy_cover.weighted_assignment_union
      (fun a : Fin W × Fin (2 ^ T) => (ν a.1).prod volume)
      (fun a => ω a.1) (fun _ : ι => True) (fun s => (γ s, J s)) S
      (fun s _ => hS s) (fun s s' _ _ hne heq => hdisj s s' hne
        (congrArg Prod.fst heq) (congrArg Prod.snd heq))
    simpa only [Fintype.sum_prod_type, true_and, ite_true, D, blockUnion] using h
  have hpair := Submission.Obl.k4_scalar_angular_pair_agreement.all_pairs_lower
    (Nat.two_pow_pos T) ω hω ν D hD hm₀ (by simpa only [hsplit] using hmass)
  let H (s : ι) := pairSet (S s) (D (γ s) (J s))
  have hH (s : ι) : MeasurableSet (H s) := measurableSet_pairSet (hS s) (hD _ _)
  let U (w : Fin W) (b : Fin (2 ^ T)) : Set (X × (ℝ × ℝ)) :=
    {p | ∃ s, (γ s, J s) = (w, b) ∧ p ∈ H s}
  have hsplitH : (∑ w, ∑ b, ω w * (2 ^ T : ℕ) *
      ((ν w).prod (volume.prod volume)) (U w b)) =
      ∑ s, ω (γ s) * (2 ^ T : ℕ) * ((ν (γ s)).prod (volume.prod volume)) (H s) := by
    have h := Submission.Obl.k4_quadratic_finite_greedy_cover.weighted_assignment_union
      (fun a : Fin W × Fin (2 ^ T) => (ν a.1).prod (volume.prod volume))
      (fun a => ω a.1 * (2 ^ T : ℕ)) (fun _ : ι => True) (fun s => (γ s, J s)) H
      (fun s _ => hH s) (by
        intro s s' _ _ hne heq
        apply disjoint_left.mpr
        intro p hp hp'
        exact disjoint_left.mp (hdisj s s' hne (congrArg Prod.fst heq)
          (congrArg Prod.snd heq)) hp.1 hp'.1)
    simpa only [Fintype.sum_prod_type, true_and, ite_true, U] using h
  apply hpair.trans
  rw [← hsplitH]
  apply Finset.sum_le_sum
  intro w _
  apply Finset.sum_le_sum
  intro b _
  gcongr
  rintro p ⟨⟨s, hs, hp⟩, hp'⟩
  refine ⟨s, hs, hp, ?_⟩
  have hγ : γ s = w := congrArg Prod.fst hs
  have hJ : J s = b := congrArg Prod.snd hs
  show (p.1, p.2.2) ∈ D (γ s) (J s)
  rw [hγ, hJ]
  exact hp'

/-- A family disjoint in each world, in unit time, has total original weighted mass at
most one. -/
theorem selected_source_mass_le_one {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (V : ℕ) (ν : Fin V → Measure X) [∀ w, IsProbabilityMeasure (ν w)]
    (ω : Fin V → ℝ) (hω : ∀ w, 0 ≤ ω w) (hωsum : ∑ w, ω w = 1)
    (γ : ι → Fin V) (S : ι → Set (X × ℝ)) (hS : ∀ i, MeasurableSet (S i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → Disjoint (S i) (S i'))
    (hunit : ∀ i, S i ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    (∑ i, ENNReal.ofReal (ω (γ i)) * ((ν (γ i)).prod volume) (S i)) ≤ 1 := by
  classical
  have heq := Submission.Obl.k4_quadratic_finite_greedy_cover.weighted_assignment_union
    (fun w => (ν w).prod (volume : Measure ℝ)) (fun w => ENNReal.ofReal (ω w))
    (fun _ : ι => True) γ S (fun i _ => hS i) (fun i i' _ _ => hdisj i i')
  simp only [true_and, ite_true] at heq
  rw [← heq]
  have hworld (w : Fin V) : ((ν w).prod volume) {p | ∃ i, γ i = w ∧ p ∈ S i} ≤ 1 := by
    calc
      _ ≤ ((ν w).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := by
        apply measure_mono
        rintro p ⟨i, _, hp⟩
        exact hunit i hp
      _ = _ := by simp [Measure.prod_prod]
  calc
    _ ≤ ∑ w, ENNReal.ofReal (ω w) * 1 :=
      Finset.sum_le_sum fun w _ => mul_le_mul' le_rfl (hworld w)
    _ = 1 := by
      simp only [mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hω w), hωsum]
      norm_num

/-! ### One-time exceptions -/

/-- Two-time exceptions, summed over disjoint source entries, are bounded by twice the
original weighted one-time exceptional mass. -/
theorem source_indexed_pair_exception_le {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (W T : ℕ) (ν : Fin W → Measure X) (hν : ∀ w, SFinite (ν w))
    (ω : Fin W → ℝ) (γ : ι → Fin W) (j : ι → Fin (2 ^ T))
    (S : ι → Set (X × ℝ))
    (hdisj : ∀ s s', s ≠ s' → γ s = γ s' → j s = j s' → Disjoint (S s) (S s'))
    (H : ι → Set (X × (ℝ × ℝ))) (hH : ∀ s, MeasurableSet (H s))
    (hsource : ∀ s p, p ∈ H s → (p.1, p.2.1) ∈ S s)
    (hblock : ∀ s p, p ∈ H s → p.2.1 ∈ I T (j s) ∧ p.2.2 ∈ I T (j s))
    (Q : Fin W → Set (X × ℝ)) (hQ : ∀ w, MeasurableSet (Q w)) :
    (∑ s, ENNReal.ofReal (ω (γ s) * (2 : ℝ) ^ T) *
      ((ν (γ s)).prod (volume.prod volume))
        (H s ∩ {p | (p.1, p.2.1) ∈ Q (γ s) ∨ (p.1, p.2.2) ∈ Q (γ s)})) ≤
      2 * ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (Q w) := by
  classical
  let bad (w : Fin W) : Set (X × (ℝ × ℝ)) :=
    {p | (p.1, p.2.1) ∈ Q w ∨ (p.1, p.2.2) ∈ Q w}
  have hbad (w : Fin W) : MeasurableSet (bad w) :=
    ((hQ w).preimage (measurable_fst.prodMk measurable_snd.fst)).union
      ((hQ w).preimage (measurable_fst.prodMk measurable_snd.snd))
  let blockPairs (w : Fin W) (b : Fin (2 ^ T)) : Set (X × (ℝ × ℝ)) :=
    {p | p.2.1 ∈ I T b ∧ p.2.2 ∈ I T b}
  have hsum : (∑ s, ENNReal.ofReal (ω (γ s) * (2 : ℝ) ^ T) *
      ((ν (γ s)).prod (volume.prod volume)) (H s ∩ bad (γ s))) ≤
      ∑ w : Fin W, ∑ b : Fin (2 ^ T),
        ENNReal.ofReal (ω w) * ENNReal.ofReal ((2 : ℝ) ^ T) *
          ((ν w).prod (volume.prod volume)) (blockPairs w b ∩ bad w) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun s => (γ s, j s))]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro w _
    apply Finset.sum_le_sum
    intro b _
    let F := Finset.univ.filter (fun s => (γ s, j s) = (w, b))
    have heq : ∑ s ∈ F, ENNReal.ofReal (ω (γ s) * (2 : ℝ) ^ T) *
        ((ν (γ s)).prod (volume.prod volume)) (H s ∩ bad (γ s)) =
        ENNReal.ofReal (ω w * (2 : ℝ) ^ T) *
          ∑ s ∈ F, ((ν w).prod (volume.prod volume)) (H s ∩ bad w) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hsγ : γ s = w := congrArg Prod.fst (Finset.mem_filter.mp hs).2
      rw [hsγ]
    rw [heq]
    have hsets : (↑F : Set ι).PairwiseDisjoint (fun s => H s ∩ bad w) := by
      intro s hs s' hs' hne
      have hs0 := (Finset.mem_filter.mp hs).2
      have hs1 := (Finset.mem_filter.mp hs').2
      apply disjoint_left.mpr
      rintro p ⟨hp, _⟩ ⟨hp', _⟩
      exact disjoint_left.mp (hdisj s s' hne
        ((congrArg Prod.fst hs0).trans (congrArg Prod.fst hs1).symm)
        ((congrArg Prod.snd hs0).trans (congrArg Prod.snd hs1).symm))
        (hsource s p hp) (hsource s' p hp')
    have hmass : (∑ s ∈ F, ((ν w).prod (volume.prod volume)) (H s ∩ bad w)) ≤
        ((ν w).prod (volume.prod volume)) (blockPairs w b ∩ bad w) := by
      rw [← measure_biUnion_finset hsets (fun s _ => (hH s).inter (hbad w))]
      apply measure_mono
      rintro p hp
      simp only [mem_iUnion, mem_inter_iff] at hp
      obtain ⟨s, hs, hpH, hpbad⟩ := hp
      have hsJ : j s = b := congrArg Prod.snd (Finset.mem_filter.mp hs).2
      refine ⟨?_, hpbad⟩
      simpa only [blockPairs, mem_ofPred_eq, hsJ] using hblock s p hpH
    rw [ENNReal.ofReal_mul' (by positivity)]
    exact mul_le_mul' le_rfl hmass
  exact hsum.trans (Submission.Obl.k4_scalar_angular_pair_agreement.normalized_pair_tail_le
    W T ν hν ω Q hQ blockPairs (fun _ _ _ h => h))

/-! ### Opposite-time derivative deletions -/

variable {X : Type*} [MeasurableSpace X]

/-- If every selected witness is a regular point of an affine derivative, its
opposite-time exceptional mass is small relative to the selected witness mass. -/
theorem opposite_affine_derivative_omission_le
    (ν : Measure X) (W : Set (X × ℝ)) (F : Set (X × (ℝ × ℝ)))
    (hW : MeasurableSet W) (hF : MeasurableSet F)
    (a b : X → ℝ) (s q M ε : ℝ)
    (hq : 0 < q) (hM : 0 < M) (hε : 0 ≤ ε) (hεM : ε ≤ M / 2)
    (hlarge : ∀ p ∈ W, p.2 ∈ Icc s (s + q) ∧ M ≤ |a p.1 * p.2 + b p.1|)
    (hsub : ∀ p ∈ F, p.2.1 ∈ Icc s (s + q) ∧
      (p.1, p.2.2) ∈ W ∧ |a p.1 * p.2.1 + b p.1| < ε) :
    (ν.prod (volume.prod volume)) F ≤
      ENNReal.ofReal (4 * ε * q / M) * (ν.prod volume) W := by
  have hfiber (y : X) :
      (volume.prod volume) (Prod.mk y ⁻¹' F) ≤
        ENNReal.ofReal (4 * ε * q / M) * volume (Prod.mk y ⁻¹' W) := by
    by_cases hy : (Prod.mk y ⁻¹' W).Nonempty
    · obtain ⟨t, ht⟩ := hy
      obtain ⟨htI, htM⟩ := hlarge (y, t) ht
      have hbad := Submission.Lib.K4GoodTimes.volume_affine_sublevel_on_interval
        (a y) (b y) s q M ε hq hM hε hεM ⟨t, htI, htM⟩
      calc
        (volume.prod volume) (Prod.mk y ⁻¹' F) ≤
            (volume.prod volume)
              ({t : ℝ | t ∈ Icc s (s + q) ∧ |a y * t + b y| < ε} ×ˢ
                (Prod.mk y ⁻¹' W)) := by
          apply measure_mono
          intro p hp
          obtain ⟨hpI, hpW, hpε⟩ := hsub (y, p) hp
          exact ⟨⟨hpI, hpε⟩, hpW⟩
        _ = volume {t : ℝ | t ∈ Icc s (s + q) ∧ |a y * t + b y| < ε} *
            volume (Prod.mk y ⁻¹' W) := Measure.prod_prod _ _
        _ ≤ _ := by gcongr
    · have he : Prod.mk y ⁻¹' F = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        exact hy ⟨p.2, (hsub (y, p) hp).2.1⟩
      rw [he, measure_empty]
      exact zero_le
  rw [Measure.prod_apply hF, Measure.prod_apply hW]
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (4 * ε * q / M) * volume (Prod.mk y ⁻¹' W) ∂ν :=
      lintegral_mono hfiber
    _ = _ := lintegral_const_mul _ (measurable_measure_prodMk_left hW)

/-- Summing the opposite-time losses costs only the original selected witness mass,
with no factor for the number of labels or time blocks. Derivatives are normalized so
that the common witness floor is `1 / K`. -/
theorem normalized_opposite_derivative_budget {ι : Type*} [Fintype ι]
    (V T : ℕ) (ν : Fin V → Measure X) (ω : Fin V → ℝ) (γ : ι → Fin V)
    (Sel : ι → Set (X × ℝ)) (F : ι → Set (X × (ℝ × ℝ)))
    (hSel : ∀ i, MeasurableSet (Sel i)) (hF : ∀ i, MeasurableSet (F i))
    (a b : ι → X → ℝ) (s : ι → ℝ) {K ε : ℝ}
    (hK : 0 < K) (hε : 0 ≤ ε) (hεK : ε ≤ (1 / K) / 2)
    (hlarge : ∀ i p, p ∈ Sel i →
      p.2 ∈ Icc (s i) (s i + 1 / (2 : ℝ) ^ T) ∧ 1 / K ≤ |a i p.1 * p.2 + b i p.1|)
    (hsub : ∀ i p, p ∈ F i →
      p.2.1 ∈ Icc (s i) (s i + 1 / (2 : ℝ) ^ T) ∧
      (p.1, p.2.2) ∈ Sel i ∧ |a i p.1 * p.2.1 + b i p.1| < ε)
    (hmass : (∑ i, ENNReal.ofReal (ω (γ i)) * ((ν (γ i)).prod volume) (Sel i)) ≤ 1) :
    (∑ i, ENNReal.ofReal (ω (γ i) * (2 : ℝ) ^ T) *
      ((ν (γ i)).prod (volume.prod volume)) (F i)) ≤ ENNReal.ofReal (4 * ε * K) := by
  have hfreq : (0 : ℝ) < 2 ^ T := by positivity
  have hscale : (2 : ℝ) ^ T * (4 * ε * (1 / (2 : ℝ) ^ T) / (1 / K)) =
      4 * ε * K := by field_simp
  have hentry (i : ι) : ENNReal.ofReal (ω (γ i) * (2 : ℝ) ^ T) *
      ((ν (γ i)).prod (volume.prod volume)) (F i) ≤
      ENNReal.ofReal (4 * ε * K) *
        (ENNReal.ofReal (ω (γ i)) * ((ν (γ i)).prod volume) (Sel i)) := by
    have h := opposite_affine_derivative_omission_le (ν (γ i)) (Sel i) (F i)
      (hSel i) (hF i) (a i) (b i) (s i) (1 / (2 : ℝ) ^ T) (1 / K) ε
      (by positivity) (by positivity) hε hεK (hlarge i) (hsub i)
    calc
      _ ≤ ENNReal.ofReal (ω (γ i) * (2 : ℝ) ^ T) *
          (ENNReal.ofReal (4 * ε * (1 / (2 : ℝ) ^ T) / (1 / K)) *
            ((ν (γ i)).prod volume) (Sel i)) := mul_le_mul' le_rfl h
      _ = (ENNReal.ofReal (ω (γ i)) *
          (ENNReal.ofReal ((2 : ℝ) ^ T) *
            ENNReal.ofReal (4 * ε * (1 / (2 : ℝ) ^ T) / (1 / K)))) *
              ((ν (γ i)).prod volume) (Sel i) := by
        rw [ENNReal.ofReal_mul' hfreq.le]
        ring
      _ = _ := by rw [← ENNReal.ofReal_mul hfreq.le, hscale]; ring
  calc
    _ ≤ ∑ i, ENNReal.ofReal (4 * ε * K) *
        (ENNReal.ofReal (ω (γ i)) * ((ν (γ i)).prod volume) (Sel i)) :=
      Finset.sum_le_sum fun i _ => hentry i
    _ = ENNReal.ofReal (4 * ε * K) *
        ∑ i, ENNReal.ofReal (ω (γ i)) * ((ν (γ i)).prod volume) (Sel i) := by
      rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (4 * ε * K) * 1 := mul_le_mul' le_rfl hmass
    _ = _ := mul_one _

/-- The normalized affine budget applied to native hidden derivatives with world scale `B`:
the witness polynomial failing at the source time. -/
theorem native_opposite_derivative_budget {ι : Type*} [Fintype ι]
    (V T : ℕ) (ν : Fin V → Measure (ℕ × (Fin 6 → ℝ)))
    (ω : Fin V → ℝ) (γ : ι → Fin V)
    (Sel : ι → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (F : ι → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)))
    (hSel : ∀ i, MeasurableSet (Sel i)) (hF : ∀ i, MeasurableSet (F i))
    (R : ι → MvPolynomial (Fin 4) ℝ) (hR : ∀ i, (R i).totalDegree ≤ 2)
    (B : Fin V → ℝ) (hB : ∀ w, 0 < B w) (s : ι → ℝ) {K ε : ℝ}
    (hK : 0 < K) (hε : 0 ≤ ε) (hεK : ε ≤ (1 / K) / 2)
    (hlarge : ∀ i p, p ∈ Sel i →
      p.2 ∈ Icc (s i) (s i + 1 / (2 : ℝ) ^ T) ∧
        B (γ i) / K ≤ |eval (x p.1 p.2) (pderiv (3 : Fin 4) (R i))|)
    (hsub : ∀ i p, p ∈ F i →
      p.2.1 ∈ Icc (s i) (s i + 1 / (2 : ℝ) ^ T) ∧
        (p.1, p.2.2) ∈ Sel i ∧
          |eval (x p.1 p.2.1) (pderiv (3 : Fin 4) (R i))| < ε * B (γ i))
    (hmass : (∑ i, ENNReal.ofReal (ω (γ i)) * ((ν (γ i)).prod volume) (Sel i)) ≤ 1) :
    (∑ i, ENNReal.ofReal (ω (γ i) * (2 : ℝ) ^ T) *
      ((ν (γ i)).prod (volume.prod volume)) (F i)) ≤ ENNReal.ofReal (4 * ε * K) := by
  classical
  have haff : ∀ i (l : ℕ × (Fin 6 → ℝ)), ∃ a b : ℝ, ∀ t : ℝ,
      eval (x l t) (pderiv (3 : Fin 4) (R i)) = a * t + b := by
    intro i l
    exact Submission.Obl.k4_quadratic_finite_greedy_cover.trajectory_native_derivative_affine
      (R i) (hR i) l
  choose a b hab using haff
  have heval (i : ι) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
      (a i l / B (γ i)) * t + b i l / B (γ i) =
        eval (x l t) (pderiv (3 : Fin 4) (R i)) / B (γ i) := by
    rw [hab]
    ring
  apply normalized_opposite_derivative_budget V T ν ω γ Sel F hSel hF
    (fun i l => a i l / B (γ i)) (fun i l => b i l / B (γ i)) s hK hε hεK
    ?_ ?_ hmass
  · intro i p hp
    refine ⟨(hlarge i p hp).1, ?_⟩
    rw [heval, abs_div, abs_of_pos (hB (γ i))]
    apply (le_div_iff₀ (hB (γ i))).mpr
    convert (hlarge i p hp).2 using 1
    ring
  · intro i p hp
    refine ⟨(hsub i p hp).1, (hsub i p hp).2.1, ?_⟩
    rw [heval, abs_div, abs_of_pos (hB (γ i)), div_lt_iff₀ (hB (γ i))]
    exact (hsub i p hp).2.2

/-- The same budget in the source orientation: the source polynomial failing at the
witness time. -/
theorem native_source_derivative_budget {ι : Type*} [Fintype ι]
    (V T : ℕ) (ν : Fin V → Measure (ℕ × (Fin 6 → ℝ))) [∀ w, SFinite (ν w)]
    (ω : Fin V → ℝ) (γ : ι → Fin V)
    (Sel : ι → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (F : ι → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)))
    (hSel : ∀ i, MeasurableSet (Sel i)) (hF : ∀ i, MeasurableSet (F i))
    (R : ι → MvPolynomial (Fin 4) ℝ) (hR : ∀ i, (R i).totalDegree ≤ 2)
    (B : Fin V → ℝ) (hB : ∀ w, 0 < B w) (s : ι → ℝ) {K ε : ℝ}
    (hK : 0 < K) (hε : 0 ≤ ε) (hεK : ε ≤ (1 / K) / 2)
    (hlarge : ∀ i p, p ∈ Sel i →
      p.2 ∈ Icc (s i) (s i + 1 / (2 : ℝ) ^ T) ∧
        B (γ i) / K ≤ |eval (x p.1 p.2) (pderiv (3 : Fin 4) (R i))|)
    (hsub : ∀ i p, p ∈ F i →
      (p.1, p.2.1) ∈ Sel i ∧ p.2.2 ∈ Icc (s i) (s i + 1 / (2 : ℝ) ^ T) ∧
        |eval (x p.1 p.2.2) (pderiv (3 : Fin 4) (R i))| < ε * B (γ i))
    (hmass : (∑ i, ENNReal.ofReal (ω (γ i)) * ((ν (γ i)).prod volume) (Sel i)) ≤ 1) :
    (∑ i, ENNReal.ofReal (ω (γ i) * (2 : ℝ) ^ T) *
      ((ν (γ i)).prod (volume.prod volume)) (F i)) ≤ ENNReal.ofReal (4 * ε * K) := by
  classical
  have hswap : ∀ i, ((ν (γ i)).prod (volume.prod volume)) (swapTimes ⁻¹' F i) =
      ((ν (γ i)).prod (volume.prod volume)) (F i) := fun i =>
    measure_swapTimes_preimage (ν (γ i)) (hF i)
  have h := native_opposite_derivative_budget V T ν ω γ Sel
    (fun i => swapTimes ⁻¹' F i) hSel (fun i => (hF i).preimage measurable_swapTimes)
    R hR B hB s hK hε hεK hlarge (by
      intro i p hp
      have hp' := hsub i (swapTimes p) hp
      exact ⟨hp'.2.1, hp'.1, hp'.2.2⟩) hmass
  simpa only [hswap] using h

/-! ### Relabelling -/

/-- Relabel a disjoint source family by a covering witness family, without changing the
original measure or the weight of its world and block. -/
theorem weighted_assignment_cover_le {ι κ Γ : Type*}
    [Fintype ι] [Fintype κ] [Fintype Γ]
    (μ : Γ → Measure X) (w : Γ → ℝ≥0∞) (src : ι → Γ) (wit : κ → Γ)
    (S : ι → Set X) (T : κ → Set X) (hS : ∀ i, MeasurableSet (S i))
    (hdisj : ∀ i i', i ≠ i' → src i = src i' → Disjoint (S i) (S i'))
    (hcover : ∀ i y, y ∈ S i → ∃ j, wit j = src i ∧ y ∈ T j) :
    (∑ i, w (src i) * μ (src i) (S i)) ≤ ∑ j, w (wit j) * μ (wit j) (T j) := by
  classical
  have heq := Submission.Obl.k4_quadratic_finite_greedy_cover.weighted_assignment_union
    μ w (fun _ : ι => True) src S (fun i _ => hS i) (fun i i' _ _ => hdisj i i')
  simp only [true_and, ite_true] at heq
  rw [← heq]
  apply le_trans ?_
    (Submission.Obl.k4_scalar_normalized_exact_refinement.weighted_union_le_sum μ w wit T)
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul' le_rfl
  apply measure_mono
  rintro y ⟨i, hi, hy⟩
  obtain ⟨j, hj, hyj⟩ := hcover i y hy
  exact ⟨j, hj.trans hi, hyj⟩

end Submission.Obl.k4_homogeneous_native_pair_preparation
