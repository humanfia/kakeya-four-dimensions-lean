import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Densities
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.SelectedFormat
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.WorldMeasure

/-!
# Problems with smaller events

`withEvents p K M D E` keeps every prior, weight and resolution of `p` and replaces
its events by `E`, with the canonical Radon-Nikodym observation densities. These
densities exist for every measurable sub-event (`hasDensities_withEvents`). We also
record that incidence laws live, almost surely, in a polynomial label box.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set Filter
open scoped ENNReal

/-- The canonical observation density of a finite incidence law. -/
def obsDensity (μ : Measure Incidence) (n r : ℝ) : Observation → ℝ≥0∞ :=
  (μ.map (observe n r)).rnDeriv reference

theorem obsDensity_spec (μ : Measure Incidence) [IsFiniteMeasure μ]
    (hac : μ.map baseOf ≪ (volume : Measure (Fin 2 → ℝ))) (n r : ℝ) :
    Measurable (obsDensity μ n r) ∧
      μ.map (observe n r) = reference.withDensity (obsDensity μ n r) := by
  refine ⟨Measure.measurable_rnDeriv _ _, ?_⟩
  have hfst : (μ.map (observe n r)).map Prod.fst ≪ (volume : Measure (Fin 2 → ℝ)) := by
    rw [Measure.map_map measurable_fst (measurable_observe n r)]
    exact hac
  have hfull :=
    Submission.Obl.k4_dyadic_crop_affine_laws.Framework.absolutelyContinuous_prod_count_of_fst
      (μ.map (observe n r)) volume hfst
  have : SigmaFinite reference := by unfold reference; infer_instance
  exact (Measure.withDensity_rnDeriv_eq _ _ hfull).symm

theorem isFiniteMeasure_incidence (ν : Measure Trajectory) [IsProbabilityMeasure ν]
    {S : Set Incidence} (hS : S ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    IsFiniteMeasure ((ν.prod volume).restrict S) := by
  constructor
  rw [Measure.restrict_apply_univ]
  calc (ν.prod volume) S ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hS
    _ = 1 := by simp [Measure.prod_prod]
    _ < ⊤ := ENNReal.one_lt_top

/-- The incidence law of a sub-event has mass at most one. -/
theorem incidence_le_one (ν : Measure Trajectory) [IsProbabilityMeasure ν]
    {S : Set Incidence} (hS : S ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    ((ν.prod volume).restrict S) univ ≤ 1 := by
  rw [Measure.restrict_apply_univ]
  calc (ν.prod volume) S ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hS
    _ = 1 := by simp [Measure.prod_prod]

/-- The problem with the same priors and weights and new events. -/
def withEvents (p : Problem) (K : ℕ → ℝ) (M D : ℕ)
    (E : (k : ℕ) → Fin (p.1 k) → Set Incidence) : Problem :=
  ⟨p.1, resolution p, K, M, D, length p, rate p, angularRate p, angularLength p,
    weight p, prior p, E,
    (fun k a r => obsDensity (((prior p k a).prod volume).restrict (E k a)) (resolution p k) r),
    (fun _ _ _ _ => 0), fun _ => 0⟩

theorem law_withEvents (p : Problem) (K : ℕ → ℝ) (M D : ℕ)
    (E : (k : ℕ) → Fin (p.1 k) → Set Incidence) (k : ℕ) (a : Fin (p.1 k)) :
    law (withEvents p K M D E) k a = ((prior p k a).prod volume).restrict (E k a) := rfl

/-- The base law of every sub-event of a raw problem is absolutely continuous. -/
theorem base_ac (p : Problem) (hp : RawScalar p) (k : ℕ) (a : Fin (p.1 k))
    (S : Set Incidence) :
    (((prior p k a).prod volume).restrict S).map baseOf ≪ (volume : Measure (Fin 2 → ℝ)) := by
  obtain ⟨n, -, h, i, B, -, hν⟩ := ((hp.2 k).2.2.2.1 a).2.1
  rw [hν]
  exact mixture_base_ac h i B S

/-- Every sub-event law has the canonical density at every depth. -/
theorem obsDensity_sub (p : Problem) (hp : RawScalar p) (k : ℕ) (a : Fin (p.1 k))
    {S : Set Incidence} (hS : S ⊆ event p k a) (n r : ℝ) :
    Measurable (obsDensity (((prior p k a).prod volume).restrict S) n r) ∧
      (((prior p k a).prod volume).restrict S).map (observe n r) =
        reference.withDensity (obsDensity (((prior p k a).prod volume).restrict S) n r) := by
  have := ((hp.2 k).2.2.2.1 a).1
  have := isFiniteMeasure_incidence (prior p k a) (hS.trans ((hp.2 k).2.2.2.1 a).2.2.2.2.1)
  exact obsDensity_spec _ (base_ac p hp k a S) n r

theorem hasDensities_withEvents (p : Problem) (hp : RawScalar p) (K : ℕ → ℝ) (M D : ℕ)
    (E : (k : ℕ) → Fin (p.1 k) → Set Incidence) (hE : ∀ k a, E k a ⊆ event p k a) :
    HasDensities (withEvents p K M D E) := by
  intro k a r _ _
  exact obsDensity_sub p hp k a (hE k a) (resolution p k) r

/-- Priors of a raw problem are supported in the polynomial coefficient cube. -/
theorem prior_support (p : Problem) (hp : RawScalar p) (k : ℕ) (a : Fin (p.1 k)) :
    ∀ᵐ l ∂(prior p k a), ∀ e, |l.2 e| ≤ resolution p k ^ (sizeBudget p : ℝ) := by
  obtain ⟨n, -, h, i, B, hB, hν⟩ := ((hp.2 k).2.2.2.1 a).2.1
  set R := resolution p k ^ (sizeBudget p : ℝ)
  have hgood : MeasurableSet {l : Trajectory | ∀ e, |l.2 e| ≤ R} := by
    have : {l : Trajectory | ∀ e, |l.2 e| ≤ R} = ⋂ e, {l : Trajectory | |l.2 e| ≤ R} := by
      ext l
      simp
    rw [this]
    exact MeasurableSet.iInter fun e =>
      measurableSet_le ((measurable_pi_apply e).comp measurable_snd).abs measurable_const
  have hbad : MeasurableSet {l : Trajectory | ¬ ∀ e, |l.2 e| ≤ R} := hgood.compl
  rw [hν, ae_iff, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [Measure.smul_apply, Measure.map_apply (by fun_prop) hbad,
    Measure.restrict_apply (hbad.preimage (by fun_prop))]
  have hempty : (fun b => (i j, b)) ⁻¹' {l : Trajectory | ¬ ∀ e, |l.2 e| ≤ R} ∩ B j = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro b ⟨hb', hb⟩
    exact hb' ((hB j).2.2.2.2 b hb)
  rw [hempty, measure_empty, smul_zero]

/-- The radius of the label box. -/
def labelRadius (n R₀ : ℝ) (H : ℕ) : ℕ := ⌈3 * n ^ H * R₀⌉₊ + 1

theorem abs_floor_le_of_abs_le {u B : ℝ} (hu : |u| ≤ B) : |(⌊u⌋ : ℝ)| ≤ B + 1 := by
  have h1 := Int.floor_le u
  have h2 := Int.lt_floor_add_one u
  obtain ⟨hl, hr⟩ := abs_le.mp hu
  rw [abs_le]
  constructor <;> linarith

theorem scalarLabel_bound {n R₀ : ℝ} (hn : 1 ≤ n) (hR₀ : 1 ≤ R₀) (H : ℕ) {z : Incidence}
    (ht : z.2 ∈ Icc (0 : ℝ) 1) (hl : ∀ e, |z.1.2 e| ≤ R₀) (c : Fin 3) :
    |scalarLabel n H z c| ≤ (labelRadius n R₀ H : ℤ) := by
  have hnH : 0 ≤ n ^ H := pow_nonneg (by linarith) H
  have hnH1 : 1 ≤ n ^ H := one_le_pow₀ hn
  obtain ⟨ht0, ht1⟩ := ht
  have hta : |z.2| ≤ 1 := abs_le.mpr ⟨by linarith, ht1⟩
  have ht2 : |z.2 ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) hta
  have hcoord : |n ^ H * (![z.2, y z.1 z.2, x z.1 z.2] c)| ≤ 3 * n ^ H * R₀ := by
    rw [abs_mul, abs_of_nonneg hnH]
    have hv : |(![z.2, y z.1 z.2, x z.1 z.2] : Fin 3 → ℝ) c| ≤ 3 * R₀ := by
      fin_cases c
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        linarith
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, y]
        calc |z.1.2 0 + z.2 * z.1.2 1| ≤ |z.1.2 0| + |z.2 * z.1.2 1| := abs_add_le _ _
          _ ≤ R₀ + 1 * R₀ := by
            rw [abs_mul]
            gcongr
            · exact hl 0
            · exact hl 1
          _ ≤ 3 * R₀ := by linarith
      · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, x]
        calc |z.1.2 2 + z.2 * z.1.2 3 + z.2 ^ 2 * z.1.2 4|
            ≤ |z.1.2 2| + |z.2 * z.1.2 3| + |z.2 ^ 2 * z.1.2 4| := abs_add_three _ _ _
          _ ≤ R₀ + 1 * R₀ + 1 * R₀ := by
            rw [abs_mul, abs_mul]
            gcongr
            · exact hl 2
            · exact hl 3
            · exact hl 4
          _ = 3 * R₀ := by ring
    calc n ^ H * |(![z.2, y z.1 z.2, x z.1 z.2] : Fin 3 → ℝ) c| ≤ n ^ H * (3 * R₀) :=
          mul_le_mul_of_nonneg_left hv hnH
      _ = 3 * n ^ H * R₀ := by ring
  have hfl : scalarLabel n H z c = ⌊n ^ H * (![z.2, y z.1 z.2, x z.1 z.2] c)⌋ := by
    fin_cases c <;> rfl
  have hreal : |((scalarLabel n H z c : ℤ) : ℝ)| ≤ ((labelRadius n R₀ H : ℕ) : ℝ) := by
    rw [hfl]
    refine (abs_floor_le_of_abs_le hcoord).trans ?_
    simp only [labelRadius, Nat.cast_add, Nat.cast_one]
    have := Nat.le_ceil (3 * n ^ H * R₀)
    linarith
  have : (|scalarLabel n H z c| : ℤ) ≤ ((labelRadius n R₀ H : ℕ) : ℤ) := by
    have h' : ((|scalarLabel n H z c| : ℤ) : ℝ) ≤ (((labelRadius n R₀ H : ℕ) : ℤ) : ℝ) := by
      push_cast
      exact hreal
    exact_mod_cast h'
  exact this

/-- Almost every incidence of a sub-event lies in the polynomial label box. -/
theorem ae_label_box (p : Problem) (hp : RawScalar p) (k : ℕ) (a : Fin (p.1 k)) (H : ℕ)
    {S : Set Incidence} (hS : S ⊆ event p k a) (hSm : MeasurableSet S) :
    ∀ᵐ z ∂(((prior p k a).prod volume).restrict S), ∀ c,
      |scalarLabel (resolution p k) H z c| ≤
        (labelRadius (resolution p k) (resolution p k ^ (sizeBudget p : ℝ)) H : ℤ) := by
  have hN : 1 ≤ resolution p k := by linarith [hp.1.1 k]
  have hR₀ : 1 ≤ resolution p k ^ (sizeBudget p : ℝ) :=
    Real.one_le_rpow hN (Nat.cast_nonneg _)
  have hsupp : ∀ᵐ z ∂((prior p k a).prod (volume : Measure ℝ)),
      ∀ e, |z.1.2 e| ≤ resolution p k ^ (sizeBudget p : ℝ) :=
    (Measure.quasiMeasurePreserving_fst (ν := (volume : Measure ℝ))).ae
      (prior_support p hp k a)
  have htime : ∀ᵐ z ∂(((prior p k a).prod volume).restrict S), z ∈ S :=
    ae_restrict_mem hSm
  filter_upwards [ae_restrict_of_ae hsupp, htime] with z hz hzS c
  have hzE := ((hp.2 k).2.2.2.1 a).2.2.2.2.1 (hS hzS)
  exact scalarLabel_bound hN hR₀ H (mem_prod.mp hzE).2 hz c

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
