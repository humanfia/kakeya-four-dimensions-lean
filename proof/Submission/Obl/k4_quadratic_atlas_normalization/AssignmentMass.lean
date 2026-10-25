import Mathlib
import Submission.Lib.K4GoodTimes

/-!
# Mass budgets for assignments on the original probability laws

The disjointness hypothesis is only within a world and time block. Consequently
summing assignment budgets costs the number of time blocks, regardless of the
number of charts.
-/

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Set MeasureTheory

/-- A disjoint fiber of assignments costs at most the mass of the whole space. -/
theorem sum_measure_assignment_fiber_le {X ι C : Type*}
    [MeasurableSpace X] [Fintype ι] [DecidableEq C]
    (μ : Measure X) (g : ι → C) (A : ι → Set X) (c : C)
    (hA : ∀ b, MeasurableSet (A b))
    (hdisj : ∀ b b', b ≠ b' → g b = g b' → Disjoint (A b) (A b')) :
    ∑ b ∈ Finset.univ.filter (fun b => g b = c), μ (A b) ≤ μ univ := by
  classical
  let s := Finset.univ.filter (fun b => g b = c)
  have hd : (↑s : Set ι).PairwiseDisjoint A := by
    intro b hb b' hb' hne
    have hb : g b = c := (Finset.mem_filter.mp hb).2
    have hb' : g b' = c := (Finset.mem_filter.mp hb').2
    exact hdisj b b' hne (hb.trans hb'.symm)
  calc
    _ = μ (⋃ b ∈ s, A b) := (measure_biUnion_finset hd (fun b _ => hA b)).symm
    _ ≤ μ univ := measure_mono (subset_univ _)

/-- The original weighted assignment budget is at most the number of time blocks. -/
theorem weighted_assignment_budget {X ι Γ J : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype Γ] [Fintype J]
    (ν : Γ → Measure X) (w : Γ → ENNReal)
    (γ : ι → Γ) (j : ι → J) (A : ι → Set X)
    (hprob : ∀ g, ν g univ = 1) (hw : ∑ g, w g = 1)
    (hA : ∀ b, MeasurableSet (A b))
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b')) :
    ∑ b, w (γ b) * ν (γ b) (A b) ≤ (Fintype.card J : ENNReal) := by
  classical
  let g : ι → Γ × J := fun b => (γ b, j b)
  have hgroup (c : Γ × J) :
      ∑ b ∈ Finset.univ.filter (fun b => g b = c), w (γ b) * ν (γ b) (A b) ≤
        w c.1 := by
    calc
      _ = w c.1 * ∑ b ∈ Finset.univ.filter (fun b => g b = c), ν c.1 (A b) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        have hc := congrArg Prod.fst (Finset.mem_filter.mp hb).2
        change γ b = c.1 at hc
        rw [hc]
      _ ≤ w c.1 * ν c.1 univ := by
        gcongr
        exact sum_measure_assignment_fiber_le (ν c.1) g A c hA
          (fun b b' hne heq => hdisj b b' hne
            (congrArg Prod.fst heq) (congrArg Prod.snd heq))
      _ = w c.1 := by rw [hprob, mul_one]
  calc
    _ = ∑ c : Γ × J,
        ∑ b ∈ Finset.univ.filter (fun b => g b = c), w (γ b) * ν (γ b) (A b) :=
      (Finset.sum_fiberwise Finset.univ g (fun b => w (γ b) * ν (γ b) (A b))).symm
    _ ≤ ∑ c : Γ × J, w c.1 := Finset.sum_le_sum (fun c _ => hgroup c)
    _ = (Fintype.card J : ENNReal) := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum, hw, mul_one]

/-- The same assignment estimate for real, nonnegative probability weights. -/
theorem weighted_assignment_budget_ofReal {X ι Γ J : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype Γ] [Fintype J]
    (ν : Γ → Measure X) (w : Γ → ℝ)
    (γ : ι → Γ) (j : ι → J) (A : ι → Set X)
    (hprob : ∀ g, IsProbabilityMeasure (ν g))
    (hw0 : ∀ g, 0 ≤ w g) (hw : ∑ g, w g = 1)
    (hA : ∀ b, MeasurableSet (A b))
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b')) :
    ∑ b, ENNReal.ofReal (w (γ b)) * ν (γ b) (A b) ≤ (Fintype.card J : ENNReal) := by
  apply weighted_assignment_budget ν (fun g => ENNReal.ofReal (w g)) γ j A
  · intro g
    have := hprob g
    exact measure_univ
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => hw0 g), hw]
    simp
  · exact hA
  · exact hdisj

/-- A uniform bound on vertical sections is charged to the original assignment law. -/
theorem incidence_mass_le_section_bound {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (A : Set X) (F : Set (X × ℝ)) (c : ENNReal)
    (hF : MeasurableSet F) (hsub : ∀ p ∈ F, p.1 ∈ A)
    (hsec : ∀ l ∈ A, volume {t : ℝ | (l, t) ∈ F} ≤ c) :
    (ν.prod volume) F ≤ c * ν A := by
  classical
  rw [Measure.prod_apply hF]
  calc
    _ ≤ ∫⁻ l, A.indicator (fun _ => c) l ∂ν := by
      apply lintegral_mono
      intro l
      by_cases hl : l ∈ A
      · rw [Set.indicator_of_mem hl]
        exact hsec l hl
      · have he : (Prod.mk l ⁻¹' F) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro t ht
          exact hl (hsub (l, t) ht)
        simp [he, Set.indicator_of_notMem hl]
    _ ≤ c * ν A := lintegral_indicator_const_le A c

/-- Summing section bounds across the atlas uses only world/block disjointness. -/
theorem weighted_incidence_mass_le_section_bound {X ι Γ J : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype Γ] [Fintype J]
    (ν : Γ → Measure X) (w : Γ → ℝ)
    (γ : ι → Γ) (j : ι → J) (A : ι → Set X) (F : ι → Set (X × ℝ))
    (c : ENNReal) (hprob : ∀ g, IsProbabilityMeasure (ν g))
    (hw0 : ∀ g, 0 ≤ w g) (hw : ∑ g, w g = 1)
    (hA : ∀ b, MeasurableSet (A b)) (hF : ∀ b, MeasurableSet (F b))
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b'))
    (hsub : ∀ b p, p ∈ F b → p.1 ∈ A b)
    (hsec : ∀ b l, l ∈ A b → volume {t : ℝ | (l, t) ∈ F b} ≤ c) :
    ∑ b, ENNReal.ofReal (w (γ b)) * ((ν (γ b)).prod volume) (F b) ≤
      c * (Fintype.card J : ENNReal) := by
  calc
    _ ≤ ∑ b, ENNReal.ofReal (w (γ b)) * (c * ν (γ b) (A b)) := by
      apply Finset.sum_le_sum
      intro b _
      gcongr
      exact incidence_mass_le_section_bound
        (ν (γ b)) (A b) (F b) c (hF b) (hsub b) (hsec b)
    _ = c * ∑ b, ENNReal.ofReal (w (γ b)) * ν (γ b) (A b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ c * (Fintype.card J : ENNReal) := by
      gcongr
      exact weighted_assignment_budget_ofReal ν w γ j A hprob hw0 hw hA hdisj

/-- An affine derivative has few small-value times relative to its block maximum. -/
theorem affine_incidence_mass_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (A : Set X) (F : Set (X × ℝ))
    (m d : X → ℝ) (s q M ε : ℝ)
    (hq : 0 < q) (hM : 0 < M) (hε : 0 ≤ ε) (hεM : ε ≤ M / 2)
    (hF : MeasurableSet F)
    (hsub : ∀ p ∈ F, p.1 ∈ A ∧ p.2 ∈ Set.Icc s (s + q) ∧
      |m p.1 * p.2 + d p.1| < ε)
    (hlarge : ∀ l ∈ A, ∃ t ∈ Set.Icc s (s + q), M ≤ |m l * t + d l|) :
    (ν.prod volume) F ≤ ENNReal.ofReal (4 * ε * q / M) * ν A := by
  apply incidence_mass_le_section_bound ν A F _ hF (fun p hp => (hsub p hp).1)
  intro l hl
  apply (measure_mono (fun t ht => (hsub (l, t) ht).2)).trans
  exact Submission.Lib.K4GoodTimes.volume_affine_sublevel_on_interval
    (m l) (d l) s q M ε hq hM hε hεM (hlarge l hl)

/-- Deleting times below `B / τ` costs at most `4 / τ` on the unchanged priors.
The factor equal to the number of blocks cancels their common length. -/
theorem weighted_affine_deletion_bound {X ι Γ J : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype Γ] [Fintype J]
    (ν : Γ → Measure X) (w : Γ → ℝ)
    (γ : ι → Γ) (j : ι → J) (A : ι → Set X) (F : ι → Set (X × ℝ))
    (m d : ι → X → ℝ) (B : Γ → ℝ) (s : ι → ℝ) (q τ : ℝ)
    (hprob : ∀ g, IsProbabilityMeasure (ν g))
    (hw0 : ∀ g, 0 ≤ w g) (hw : ∑ g, w g = 1)
    (hB : ∀ g, 0 < B g) (hq : 0 < q) (hτ : 2 ≤ τ)
    (hqcard : q * (Fintype.card J : ℝ) = 1)
    (hA : ∀ b, MeasurableSet (A b)) (hF : ∀ b, MeasurableSet (F b))
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b'))
    (hsub : ∀ b p, p ∈ F b → p.1 ∈ A b ∧
      p.2 ∈ Set.Icc (s b) (s b + q) ∧ |m b p.1 * p.2 + d b p.1| < B (γ b) / τ)
    (hlarge : ∀ b l, l ∈ A b →
      ∃ t ∈ Set.Icc (s b) (s b + q), B (γ b) ≤ |m b l * t + d b l|) :
    ∑ b, ENNReal.ofReal (w (γ b)) * ((ν (γ b)).prod volume) (F b) ≤
      ENNReal.ofReal (4 / τ) := by
  have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  have hsec b l (hl : l ∈ A b) : volume {t : ℝ | (l, t) ∈ F b} ≤
      ENNReal.ofReal (4 * q / τ) := by
    calc
      _ ≤ volume {t : ℝ | t ∈ Set.Icc (s b) (s b + q) ∧
          |m b l * t + d b l| < B (γ b) / τ} := by
        apply measure_mono
        intro t ht
        exact (hsub b (l, t) ht).2
      _ ≤ ENNReal.ofReal (4 * (B (γ b) / τ) * q / B (γ b)) := by
        apply Submission.Lib.K4GoodTimes.volume_affine_sublevel_on_interval
          (m b l) (d b l) (s b) q (B (γ b)) (B (γ b) / τ)
          hq (hB _) (div_nonneg (hB _).le hτpos.le) _ (hlarge b l hl)
        apply (div_le_div_iff₀ hτpos (by norm_num : (0 : ℝ) < 2)).mpr
        nlinarith [hB (γ b)]
      _ = ENNReal.ofReal (4 * q / τ) := by
        congr 1
        field_simp [(hB (γ b)).ne']
  have hbound := weighted_incidence_mass_le_section_bound ν w γ j A F
    (ENNReal.ofReal (4 * q / τ)) hprob hw0 hw hA hF hdisj
    (fun b p hp => (hsub b p hp).1) hsec
  have hident : (4 * q / τ) * (Fintype.card J : ℝ) = 4 / τ := by
    calc
      _ = 4 * (q * (Fintype.card J : ℝ)) / τ := by ring
      _ = 4 / τ := by rw [hqcard, mul_one]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), hident] at hbound
  exact hbound

end Submission.Obl.k4_quadratic_atlas_normalization
