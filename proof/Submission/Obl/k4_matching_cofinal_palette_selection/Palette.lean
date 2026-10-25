/- Adapted from this LOT tree, o040, session x0115, commit 9f7e9a910e7de423611a55b624313eab3641558f,
   Submission/Obl/k4_matching_refinement_exponent/Palette.lean. -/
import Submission.Obl.k4_matching_cofinal_palette_selection.Estimates
import Submission.Obl.k4_matching_cofinal_palette_selection.FiniteLaw

open MeasureTheory Set

namespace Submission.Obl.k4_matching_cofinal_palette_selection

/-- The palette hypothesis in the notation for conditional likelihoods. -/
theorem palette_sum_le (h : PaletteEstimate)
    (n L C M : ℕ) (p : Fin n → ℝ) (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ)
    (hC : 1 ≤ C) (hM : 1 ≤ M) (hp : ∀ x, 0 ≤ p x) (hpsum : ∑ x, p x = 1)
    (hnest : ∀ k x y, F (k + 1) x = F (k + 1) y → F k x = F k y)
    (hsupp : ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ M) :
    (∑ a ∈ Finset.range L, ∑ x, p x *
      max 0 (Real.log (likelihood p F Z (a + C) x / likelihood p F Z a x))) ≤
      (C : ℝ) * Real.log (M : ℝ) + (L : ℝ) := by
  exact h n L C M p F Z hC hM hp hpsum hnest hsupp

/-- The finite palette hypothesis applies to a continuous event law by using
a finite joint code for all of its records and its palette. -/
theorem palette_integral_le (h : PaletteEstimate)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n L C M : ℕ) (X : Ω → Fin n) (hX : Measurable X)
    (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hnest : ∀ k x y, F (k + 1) x = F (k + 1) y → F k x = F k y)
    (hsupp : ∀ x, ((Finset.univ.filter
      (fun y => 0 < atomMass μ X y ∧ F 0 y = F 0 x)).image Z).card ≤ M) :
    (∑ a ∈ Finset.range L, ∫ ω,
      max 0 (Real.log (eventLikelihood μ X F Z (a + C) ω /
        eventLikelihood μ X F Z a ω)) ∂μ) ≤
      (C : ℝ) * Real.log (M : ℝ) + (L : ℝ) := by
  have hsum := palette_sum_le h n L C M (atomMass μ X) F Z hC hM
    (atomMass_nonneg μ X) (sum_atomMass_eq_one μ X hX) hnest hsupp
  calc
    _ = ∑ a ∈ Finset.range L, ∑ x, atomMass μ X x *
        max 0 (Real.log (likelihood (atomMass μ X) F Z (a + C) x /
          likelihood (atomMass μ X) F Z a x)) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp_rw [eventLikelihood_eq μ X hX]
      exact integral_atomMass μ X hX (fun x => max 0
        (Real.log (likelihood (atomMass μ X) F Z (a + C) x /
          likelihood (atomMass μ X) F Z a x)))
    _ ≤ _ := hsum

/-- A weighted finite Markov inequality. -/
theorem weighted_markov {n : ℕ} (p g : Fin n → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hg : ∀ x, 0 ≤ g x) (T : ℝ) :
    T * (∑ x ∈ Finset.univ.filter (fun x => T < g x), p x) ≤ ∑ x, p x * g x := by
  classical
  rw [Finset.mul_sum]
  calc
    (∑ x ∈ Finset.univ.filter (fun x => T < g x), T * p x) ≤
        ∑ x ∈ Finset.univ.filter (fun x => T < g x), p x * g x := by
      apply Finset.sum_le_sum
      intro x hx
      have ht : T ≤ g x := (Finset.mem_filter.mp hx).2.le
      nlinarith [hp x]
    _ ≤ ∑ x, p x * g x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => mul_nonneg (hp x) (hg x))

/-- Two Markov estimates on any finite set of steps. -/
theorem two_markov_on {α : Type*} {n : ℕ} (A : Finset α)
    (p : Fin n → ℝ) (g : α → Fin n → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hg : ∀ a x, 0 ≤ g a x)
    (T ε : ℝ) (hT : 0 ≤ T) :
    (((A.filter (fun a =>
      ε < ∑ x ∈ Finset.univ.filter (fun x => T < g a x), p x)).card : ℕ) : ℝ) *
        (T * ε) ≤ ∑ a ∈ A, ∑ x, p x * g a x := by
  classical
  let B := A.filter (fun a =>
    ε < ∑ x ∈ Finset.univ.filter (fun x => T < g a x), p x)
  change (B.card : ℝ) * (T * ε) ≤ _
  calc
    (B.card : ℝ) * (T * ε) = ∑ _a ∈ B, T * ε := by simp
    _ ≤ ∑ a ∈ B, ∑ x, p x * g a x := by
      apply Finset.sum_le_sum
      intro a ha
      calc
        T * ε ≤ T * (∑ x ∈ Finset.univ.filter (fun x => T < g a x), p x) := by
          apply mul_le_mul_of_nonneg_left _ hT
          exact (Finset.mem_filter.mp ha).2.le
        _ ≤ _ := weighted_markov p (g a) hp (hg a) T
    _ ≤ ∑ a ∈ A, ∑ x, p x * g a x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ => Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (hg a x))

/-- Few rows can have a large probability of a large loss. -/
theorem two_markov {n L : ℕ} (p : Fin n → ℝ) (g : Fin L → Fin n → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hg : ∀ a x, 0 ≤ g a x)
    (T ε : ℝ) (hT : 0 ≤ T) :
    (((Finset.univ.filter (fun a : Fin L =>
      ε < ∑ x ∈ Finset.univ.filter (fun x => T < g a x), p x)).card : ℕ) : ℝ) *
        (T * ε) ≤ ∑ a, ∑ x, p x * g a x :=
  two_markov_on Finset.univ p g hp hg T ε hT

/-- Failure mass at a step, ignoring zero-mass atoms. -/
noncomputable def likelihoodFailureMass {n : ℕ} (p : Fin n → ℝ)
    (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ) (C a : ℕ) (R : ℝ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => 0 < p x ∧
    R * likelihood p F Z a x < likelihood p F Z (a + C) x), p x

/-- A power-size likelihood failure entails the corresponding logarithmic loss. -/
theorem log_gain_gt_of_failure {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ x, 0 ≤ p x) (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ)
    (a C : ℕ) (N τ : ℝ) (hN : 0 < N) (x : Fin n) (hx : 0 < p x)
    (hfail : N ^ τ * likelihood p F Z a x < likelihood p F Z (a + C) x) :
    τ * Real.log N < max 0
      (Real.log (likelihood p F Z (a + C) x / likelihood p F Z a x)) := by
  have hq : 0 < likelihood p F Z a x :=
    Submission.Obl.k4_matching_palette_likelihood.posterior_pos p (F a) Z hp x hx
  have hratio : N ^ τ < likelihood p F Z (a + C) x / likelihood p F Z a x :=
    (lt_div_iff₀ hq).mpr hfail
  have hlog := Real.log_lt_log (Real.rpow_pos_of_pos hN τ) hratio
  rw [Real.log_rpow hN] at hlog
  exact hlog.trans_le (le_max_right _ _)

theorem failure_mass_le_log_exceed {n : ℕ} {p : Fin n → ℝ}
    (hp : ∀ x, 0 ≤ p x) (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ)
    (a C : ℕ) (N τ : ℝ) (hN : 0 < N) :
    likelihoodFailureMass p F Z C a (N ^ τ) ≤
      ∑ x ∈ Finset.univ.filter (fun x => τ * Real.log N < max 0
        (Real.log (likelihood p F Z (a + C) x / likelihood p F Z a x))), p x := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact log_gain_gt_of_failure hp F Z a C N τ hN x hx.1 hx.2
  · exact fun x _ _ => hp x

/-- A direct good-step count from the frozen palette hypothesis. -/
theorem palette_bad_steps_bound (h : PaletteEstimate)
    (n L C M : ℕ) (p : Fin n → ℝ) (F : ℕ → Fin n → ℕ) (Z : Fin n → ℕ)
    (hC : 1 ≤ C) (hM : 1 ≤ M) (hp : ∀ x, 0 ≤ p x) (hpsum : ∑ x, p x = 1)
    (hnest : ∀ k x y, F (k + 1) x = F (k + 1) y → F k x = F k y)
    (hsupp : ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ M)
    (N τ ε : ℝ) (hN : 1 ≤ N) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    (((Finset.range L).filter (fun a =>
      ε < likelihoodFailureMass p F Z C a (N ^ τ))).card : ℝ) * (τ * Real.log N * ε) ≤
      (C : ℝ) * Real.log (M : ℝ) + (L : ℝ) := by
  classical
  let g : ℕ → Fin n → ℝ := fun a x => max 0
    (Real.log (likelihood p F Z (a + C) x / likelihood p F Z a x))
  have hT : 0 ≤ τ * Real.log N := mul_nonneg hτ (Real.log_nonneg hN)
  have hsub : (Finset.range L).filter (fun a =>
      ε < likelihoodFailureMass p F Z C a (N ^ τ)) ⊆
      (Finset.range L).filter (fun a =>
        ε < ∑ x ∈ Finset.univ.filter (fun x => τ * Real.log N < g a x), p x) := by
    intro a ha
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, ?_⟩
    exact (Finset.mem_filter.mp ha).2.trans_le
      (failure_mass_le_log_exceed hp F Z a C N τ (by positivity))
  have hcard : ((((Finset.range L).filter (fun a =>
      ε < likelihoodFailureMass p F Z C a (N ^ τ))).card : ℕ) : ℝ) ≤
      (((Finset.range L).filter (fun a =>
        ε < ∑ x ∈ Finset.univ.filter (fun x => τ * Real.log N < g a x), p x)).card : ℝ) :=
    by exact_mod_cast Finset.card_le_card hsub
  calc
    _ ≤ (((Finset.range L).filter (fun a =>
        ε < ∑ x ∈ Finset.univ.filter (fun x => τ * Real.log N < g a x), p x)).card : ℝ) *
        (τ * Real.log N * ε) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hT hε)
    _ ≤ ∑ a ∈ Finset.range L, ∑ x, p x * g a x :=
      two_markov_on (Finset.range L) p g hp (fun _ _ => le_max_left _ _)
        (τ * Real.log N) ε hT
    _ ≤ _ := palette_sum_le h n L C M p F Z hC hM hp hpsum hnest hsupp


end Submission.Obl.k4_matching_cofinal_palette_selection
