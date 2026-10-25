-- Adapted from this LOT tree, o114, session x0680, commit 8cc890dd,
-- Submission/Obl/k4_terminal_representative_atlas/Preparation/ProblemCaps.lean.
import Submission.Obl.k4_homogeneous_native_pair_preparation.Interface
import Submission.Obl.k4_homogeneous_native_pair_preparation.FiniteCaps

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Set Filter
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- The frozen pure-density typicality clause gives simultaneous pointwise caps
at any fixed finite set of depths. All exceptional masses use the original
selected laws and their original world weights. -/
theorem problem_finite_pure_caps (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ)
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ →
      ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (hp : prob N K L d S η W ω ν E P B f g G)
    (R : Finset ℝ) (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ L) {τ : ℝ} (hτ : 0 < τ) :
    ∃ Good : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ k γ, Good k γ ⊆ E k γ) ∧
      (∀ k γ, MeasurableSet (Good k γ)) ∧
      (∀ k γ p, p ∈ Good k γ → ∀ r ∈ R,
        g k γ r (obs (B k γ) (δ (N k) r) p) ≤ ENNReal.ofReal (N k ^ (-f r + τ))) ∧
      IsPowerSmall N (fun k => ∑ γ, ENNReal.ofReal (ω k γ) *
        (((ν k γ).prod volume).restrict (E k γ)) (Good k γ)ᶜ) := by
  rcases hp with ⟨_, hNt, _, _, _, _, _, _, hbase, hpure, _, _, htyp, _, _⟩
  obtain ⟨_, _, hworld⟩ := hbase
  have hEm (k : ℕ) (γ : Fin (W k)) : MeasurableSet (E k γ) :=
    ((hworld k).2.2.2.1 γ).2.2.2.2.2.2.2.1
  let bad (r : ℝ) (k : ℕ) (γ : Fin (W k)) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
    {p | ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r (obs (B k γ) (δ (N k) r) p)}
  have hobs (k : ℕ) (γ : Fin (W k)) (r : ℝ) :
      Measurable (obs (B k γ) (δ (N k) r)) := by
    unfold obs x
    fun_prop
  have hbadm : ∀ r ∈ R, ∀ k γ, MeasurableSet (bad r k γ) := by
    intro r hr k γ
    exact measurableSet_lt measurable_const
      (((hpure k γ r (hR r hr).1 (hR r hr).2).1).comp (hobs k γ r))
  have hbad : ∀ r ∈ R, IsPowerSmall N (fun k => ∑ γ, ENNReal.ofReal (ω k γ) *
      (((ν k γ).prod volume).restrict (E k γ)) (bad r k γ)) := by
    intro r hr
    obtain ⟨c, hc, htail⟩ := htyp r τ (hR r hr).1 (hR r hr).2 hτ
    refine ⟨c, hc, htail.mono (fun k hk => ?_)⟩
    refine le_trans (Finset.sum_le_sum (fun γ _ => ?_)) hk
    exact mul_le_mul' le_rfl (measure_mono (fun p hp => Or.inr hp))
  obtain ⟨Good, hGm, hGc, hGtail⟩ := finite_good_mask_powerSmall hNt R W
    (fun k γ => ((ν k γ).prod volume).restrict (E k γ))
    (fun k γ => ENNReal.ofReal (ω k γ)) bad hbadm hbad
  refine ⟨fun k γ => E k γ ∩ Good k γ, (fun _ _ => inter_subset_left),
    (fun k γ => (hEm k γ).inter (hGm k γ)), ?_, ?_⟩
  · intro k γ p hp r hr
    exact le_of_not_gt (hGc k γ p hp.2 r hr)
  · apply hGtail.mono
    refine Eventually.of_forall fun k => Finset.sum_le_sum fun γ _ => mul_le_mul' le_rfl ?_
    rw [Measure.restrict_apply ((hEm k γ).inter (hGm k γ)).compl,
      Measure.restrict_apply (hGm k γ).compl]
    exact measure_mono (fun p hp => ⟨fun h => hp.1 ⟨hp.2, h⟩, hp.2⟩)

/-- The same original-law mask can also impose the angular cap at one fixed
positive depth, as required to delete separated-normal pairs. -/
theorem problem_pure_and_angular_caps (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ)
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ →
      ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (hp : prob N K L d S η W ω ν E P B f g G)
    (R : Finset ℝ) (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ L)
    {τ u : ℝ} (hτ : 0 < τ) (hu : 0 < u) (huL : u ≤ η * L) :
    ∃ Good : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ k γ, Good k γ ⊆ E k γ) ∧
      (∀ k γ, MeasurableSet (Good k γ)) ∧
      (∀ k γ p, p ∈ Good k γ → ∀ r ∈ R,
        g k γ r (obs (B k γ) (δ (N k) r) p) ≤ ENNReal.ofReal (N k ^ (-f r + τ))) ∧
      (∀ k γ p, p ∈ Good k γ → G k γ u
        (obs (B k γ) (δ (N k) L) p, fun j : Fin 2 => ⌊(v p.1) j / δ (N k) u⌋) ≤
          ENNReal.ofReal (N k ^ (-f L - S * u + τ))) ∧
      IsPowerSmall N (fun k => ∑ γ, ENNReal.ofReal (ω k γ) *
        (((ν k γ).prod volume).restrict (E k γ)) (Good k γ)ᶜ) := by
  classical
  obtain ⟨Gp, hGpE, hGpm, hGpc, hGpt⟩ := problem_finite_pure_caps N K L d S η W ω ν E P B f g G
    hp R hR hτ
  rcases hp with ⟨_, hNt, _, _, _, _, _, _, _, _, hangular, _, _, _, htail⟩
  let aobs (k : ℕ) (γ : Fin (W k)) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :=
    (obs (B k γ) (δ (N k) L) p, fun j : Fin 2 => ⌊(v p.1) j / δ (N k) u⌋)
  have haobs (k : ℕ) (γ : Fin (W k)) : Measurable (aobs k γ) := by
    unfold aobs obs v x
    fun_prop
  let Abad (k : ℕ) (γ : Fin (W k)) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
    {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u (aobs k γ p)}
  have hAm (k : ℕ) (γ : Fin (W k)) : MeasurableSet (Abad k γ) :=
    measurableSet_lt measurable_const ((hangular k γ u hu huL).1.comp (haobs k γ))
  have hAt : IsPowerSmall N (fun k => ∑ γ, ENNReal.ofReal (ω k γ) *
      (((ν k γ).prod volume).restrict (E k γ)) (Abad k γ)) := htail u τ hu huL hτ
  let bad (i : Fin 2) (k : ℕ) (γ : Fin (W k)) :=
    if i = 0 then (Gp k γ)ᶜ else Abad k γ
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ∀ k γ, MeasurableSet (bad i k γ) := by
    intro i _ k γ
    fin_cases i
    · simpa [bad] using (hGpm k γ).compl
    · simpa [bad] using hAm k γ
  have ht : ∀ i ∈ (Finset.univ : Finset (Fin 2)), IsPowerSmall N
      (fun k => ∑ γ, ENNReal.ofReal (ω k γ) *
        (((ν k γ).prod volume).restrict (E k γ)) (bad i k γ)) := by
    intro i _
    fin_cases i
    · simpa [bad] using hGpt
    · simpa [bad] using hAt
  obtain ⟨Good, hGm, hGc, hGt⟩ := finite_good_mask_powerSmall hNt Finset.univ W
    (fun k γ => ((ν k γ).prod volume).restrict (E k γ))
    (fun k γ => ENNReal.ofReal (ω k γ)) bad hm ht
  have hmem (k : ℕ) (γ : Fin (W k)) (p : (ℕ × (Fin 6 → ℝ)) × ℝ)
      (hp : p ∈ Good k γ) : p ∈ Gp k γ := by
    simpa [bad] using hGc k γ p hp 0 (Finset.mem_univ 0)
  refine ⟨Good, (fun k γ p hp => hGpE k γ (hmem k γ p hp)), hGm, ?_, ?_, hGt⟩
  · intro k γ p hp r hr
    exact hGpc k γ p (hmem k γ p hp) r hr
  · intro k γ p hp
    have hnot : p ∉ Abad k γ := by
      simpa [bad] using
        hGc k γ p hp 1 (Finset.mem_univ 1)
    exact le_of_not_gt hnot

end Submission.Obl.k4_homogeneous_native_pair_preparation
