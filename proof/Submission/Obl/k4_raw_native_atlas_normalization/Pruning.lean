import Submission.Obl.k4_finite_width_output_exclusion.Models
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

namespace Submission.Obl.k4_raw_native_atlas_normalization

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Enumerate a retained set without changing the individual charts. -/
def retainedIndex {p : Data} {k : ℕ} (a : Atlas p k) (s : Finset (Fin a.C)) :
    Fin s.card ↪ Fin a.C :=
  (s.orderEmbOfFin rfl).toEmbedding

lemma retainedIndex_mem {p : Data} {k : ℕ} (a : Atlas p k) (s : Finset (Fin a.C))
    (b : Fin s.card) : retainedIndex a s b ∈ s :=
  ((s.orderIsoOfFin rfl) b).property

def restrictAtlas {p : Data} {k : ℕ} (a : Atlas p k) (s : Finset (Fin a.C)) : Atlas p k where
  T := a.T
  C := s.card
  γ b := a.γ (retainedIndex a s b)
  j b := a.j (retainedIndex a s b)
  c b := a.c (retainedIndex a s b)
  u b := a.u (retainedIndex a s b)
  Q b := a.Q (retainedIndex a s b)
  R b := a.R (retainedIndex a s b)
  A b := a.A (retainedIndex a s b)
  F b := a.F (retainedIndex a s b)
  lst γ o := Finset.univ.filter (fun b => retainedIndex a s b ∈ a.lst γ o)

lemma restrictAtlas_mem_list {p : Data} {k : ℕ} (a : Atlas p k)
    (s : Finset (Fin a.C)) (γ : Fin (p.W k)) (o : Observation) (b : Fin s.card) :
    b ∈ (restrictAtlas a s).lst γ o ↔ retainedIndex a s b ∈ a.lst γ o := by
  change b ∈ Finset.univ.filter (fun b' => retainedIndex a s b' ∈ a.lst γ o) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma restrictAtlas_list_card {p : Data} {k : ℕ} (a : Atlas p k)
    (s : Finset (Fin a.C)) (γ : Fin (p.W k)) (o : Observation) :
    ((restrictAtlas a s).lst γ o).card ≤ (a.lst γ o).card := by
  classical
  apply Finset.card_le_card_of_injOn (retainedIndex a s)
  · intro b hb
    exact (Finset.mem_filter.mp hb).2
  · exact (retainedIndex a s).injective.injOn

lemma sum_retainedIndex {p : Data} {k : ℕ} (a : Atlas p k)
    (s : Finset (Fin a.C)) {V : Type*} [AddCommMonoid V] (f : Fin a.C → V) :
    ∑ b, f (retainedIndex a s b) = ∑ b ∈ s, f b := by
  classical
  rw [Finset.sum_subtype s (fun _ => Iff.rfl)]
  exact Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv _ _ (fun _ => rfl)

lemma chart_mass_le_prior {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C)
    (hsub : ∀ z ∈ a.F b, z.1 ∈ a.A b ∧
      z.2 ∈ Set.Icc ((a.j b : ℝ) / (2 : ℝ) ^ a.T)
        (((a.j b : ℝ) + 1) / (2 : ℝ) ^ a.T)) :
    priorMass p k (a.γ b) (a.F b) ≤ p.ν k (a.γ b) (a.A b) := by
  have hT : (0 : ℝ) < (2 : ℝ) ^ a.T := by positivity
  have hT1 : (1 : ℝ) ≤ (2 : ℝ) ^ a.T := one_le_pow₀ (by norm_num)
  calc
    _ ≤ ((p.ν k (a.γ b)).prod volume)
        (a.A b ×ˢ Set.Icc ((a.j b : ℝ) / (2 : ℝ) ^ a.T)
          (((a.j b : ℝ) + 1) / (2 : ℝ) ^ a.T)) := measure_mono hsub
    _ = p.ν k (a.γ b) (a.A b) * ENNReal.ofReal (1 / (2 : ℝ) ^ a.T) := by
      rw [Measure.prod_prod, Real.volume_Icc]
      congr 2
      ring
    _ ≤ p.ν k (a.γ b) (a.A b) * 1 := by
      gcongr
      apply (ENNReal.ofReal_le_ofReal ?_).trans_eq ENNReal.ofReal_one
      exact (div_le_one hT).mpr hT1
    _ = _ := mul_one _

/-- Remove charts below a reciprocal polynomial full-prior mass. -/
theorem prune_small_priors {p : Data} {k M D : ℕ} {κ r : ℝ} (a : Atlas p k)
    (ha : a.KnownAt M D κ r) (hN : 2 ≤ p.N k) (hκ : 1 ≤ κ) (hκN : κ ≤ p.N k)
    (hω : ∀ γ, 0 ≤ p.ω k γ) (hωs : ∑ γ, p.ω k γ = 1)
    (hν : ∀ γ, IsProbabilityMeasure (p.ν k γ)) (hB : ∀ γ, 0 ≤ p.B k γ) :
    ∃ s : Finset (Fin a.C),
      (restrictAtlas a s).KnownAt M D (2 * κ) r ∧
      ∀ b : Fin s.card,
        0 < p.ν k ((restrictAtlas a s).γ b) ((restrictAtlas a s).A b) ∧
        (p.ν k ((restrictAtlas a s).γ b) ((restrictAtlas a s).A b)).toReal⁻¹ ≤
          p.N k ^ (M + 3) := by
  classical
  have hNpos : 0 < p.N k := by linarith
  have hκpos : 0 < κ := by linarith
  let τ : ℝ := (p.N k ^ (M + 3))⁻¹
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let s := Finset.univ.filter (fun b => τ ≤ (p.ν k (a.γ b) (a.A b)).toReal)
  let m : Fin a.C → ENNReal := fun b => ENNReal.ofReal (p.ω k (a.γ b)) *
    priorMass p k (a.γ b) (a.F b)
  have hω1 (γ : Fin (p.W k)) : p.ω k γ ≤ 1 := by
    rw [← hωs]
    exact Finset.single_le_sum (fun γ _ => hω γ) (Finset.mem_univ γ)
  have hsmall (b : Fin a.C) (hb : b ∉ s) : m b ≤ ENNReal.ofReal τ := by
    have hνb := hν (a.γ b)
    have hreal : (p.ν k (a.γ b) (a.A b)).toReal ≤ τ := by
      have : ¬ τ ≤ (p.ν k (a.γ b) (a.A b)).toReal := by simpa [s] using hb
      exact (lt_of_not_ge this).le
    have hbound := chart_mass_le_prior a b (fun z hz =>
      ⟨((ha.1.2.2.1 b).2.2.2.2.2.2.2.2.2.2.1 z hz).2.1,
        ((ha.1.2.2.1 b).2.2.2.2.2.2.2.2.2.2.1 z hz).2.2.1⟩)
    calc
      m b ≤ 1 * p.ν k (a.γ b) (a.A b) :=
        mul_le_mul' ((ENNReal.ofReal_le_ofReal (hω1 _)).trans_eq ENNReal.ofReal_one) hbound
      _ = ENNReal.ofReal (p.ν k (a.γ b) (a.A b)).toReal := by
        rw [one_mul, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  have hdelete : ∑ b ∈ Finset.univ.filter (fun b => b ∉ s), m b ≤
      ENNReal.ofReal ((κ⁻¹) / 2) := by
    calc
      _ ≤ ∑ _b : Fin a.C, ENNReal.ofReal τ := by
        apply (Finset.sum_le_sum (fun b hb => hsmall b (Finset.mem_filter.mp hb).2)).trans
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => bot_le)
      _ = ENNReal.ofReal ((a.C : ℝ) * τ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h2κ : 2 * κ ≤ p.N k ^ 3 := by
          have : 2 * p.N k ≤ p.N k ^ 3 := by nlinarith [sq_nonneg (p.N k - 2)]
          linarith
        have hmul : (a.C : ℝ) * (2 * κ) ≤ p.N k ^ (M + 3) := by
          rw [pow_add]
          exact mul_le_mul ha.1.1 h2κ (by positivity) (by positivity)
        have heq : κ⁻¹ / 2 = 1 / (2 * κ) := by field_simp
        rw [heq]
        change (a.C : ℝ) / p.N k ^ (M + 3) ≤ 1 / (2 * κ)
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        simpa using hmul
  have hcover : ∑ b, m b ≤ (∑ b ∈ s, m b) +
      ∑ b ∈ Finset.univ.filter (fun b => b ∉ s), m b := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b => b ∈ s) m]
    simp
  have hmass : ENNReal.ofReal ((2 * κ)⁻¹) ≤ ∑ b ∈ s, m b := by
    have h := Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
      (∑ b, m b) (∑ b ∈ s, m b)
      (∑ b ∈ Finset.univ.filter (fun b => b ∉ s), m b)
      κ⁻¹ (by positivity) ha.1.2.2.2 hcover hdelete
    convert h using 2 <;> field_simp <;> ring
  refine ⟨s, ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact (show (s.card : ℝ) ≤ a.C by
      exact_mod_cast (show s.card ≤ a.C by simpa using Finset.card_le_univ s)).trans ha.1.1
  · intro b b' hne hγ hj
    exact ha.1.2.1 _ _ (fun heq => hne ((retainedIndex a s).injective heq)) hγ hj
  · intro b
    apply Submission.Obl.k4_quadratic_atlas_normalization.chart_mono
      (by linarith : 1 ≤ p.N k) (M' := M) (D' := D) le_rfl le_rfl hκpos
      (show κ ≤ 2 * κ by linarith) (hB _)
      (ha.1.2.2.1 (retainedIndex a s b))
    intro hl z hz
    exact (restrictAtlas_mem_list a s _ _ b).mpr (hl z hz)
  · change ENNReal.ofReal ((2 * κ)⁻¹) ≤ ∑ b, m (retainedIndex a s b)
    rw [sum_retainedIndex]
    exact hmass
  · intro γ o
    exact (show (((restrictAtlas a s).lst γ o).card : ℝ) ≤ (a.lst γ o).card by
      exact_mod_cast restrictAtlas_list_card a s γ o).trans ((ha.2 γ o).trans (by linarith))
  · intro b
    have hb := retainedIndex_mem a s b
    have hνb := hν (a.γ (retainedIndex a s b))
    have hm : τ ≤ (p.ν k (a.γ (retainedIndex a s b)) (a.A (retainedIndex a s b))).toReal :=
      (Finset.mem_filter.mp hb).2
    have hpos : 0 < (p.ν k (a.γ (retainedIndex a s b)) (a.A (retainedIndex a s b))).toReal :=
      hτ.trans_le hm
    refine ⟨ENNReal.toReal_pos_iff.mp hpos |>.1, ?_⟩
    exact (inv_le_inv₀ hpos hτ).mpr hm |>.trans_eq (inv_inv _)

end
end Submission.Obl.k4_raw_native_atlas_normalization
