/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Match/MatchCor.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
/- Adapted within this LOT tree (g-oai-074) from o227 `k4_horizontal_three_projection_wide_return`,
session x0788, branch x0788, commit d1137a70, file
Submission/Obl/k4_horizontal_three_projection_wide_return/MatchCor.lean (namespace renamed into o250's). -/
import Mathlib
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Match.MatchQuad

/-!
# The frozen matching hypothesis, specialised to quadratics on finite index types

`MatchHyp` is the obligation's `Match` premise verbatim. `match_quad` restates it
for quadratics `quad (a i)` indexed by arbitrary nonempty finite types, in the
form "a probability pair law cannot be carried by close pairs whose coefficient
vectors differ by at least one".
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchCor

open MeasureTheory MatchQuad

/-- The obligation's `Match` premise, verbatim. -/
def MatchHyp : Prop := ∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → d < 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (n₁ : ℝ) ≤ N ^ (d + η) → (n₂ : ℝ) ≤ N ^ (d + η) → (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ η) → (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ η) → (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) → (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 → MeasureTheory.IsProbabilityMeasure μ → (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) → (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) → ¬ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0

/-- A bijection between discrete measurable spaces is a measurable equivalence. -/
def discreteEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] (e : α ≃ β) : α ≃ᵐ β where
  toEquiv := e
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := Measurable.of_discrete

lemma iteratedDeriv_quad_sub (c c' : Fin 3 → ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ 2) (x : ℝ) :
    iteratedDeriv j (quad c) x - iteratedDeriv j (quad c') x = iteratedDeriv j (quad (c - c')) x := by
  interval_cases j
  · simp only [iteratedDeriv_one_quad, Pi.sub_apply]; ring
  · simp only [iteratedDeriv_two_quad, Pi.sub_apply]; ring

/-- `Match` for quadratics with coefficients bounded by `3`, indexed by finite types:
a probability pair law with the two marginal ceilings cannot be carried by pairs that
are `2/N`-close at a point of `[0,1]` while their coefficient vectors differ by at
least one. -/
theorem match_quad (hM : MatchHyp) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]
      (a₁ : ι₁ → Fin 3 → ℝ) (a₂ : ι₂ → Fin 3 → ℝ) (π₁ : ι₁ → ℝ) (π₂ : ι₂ → ℝ)
      (μ : Measure ((ι₁ × ι₂) × ℝ)),
      (Fintype.card ι₁ : ℝ) ≤ N ^ (d + η) → (Fintype.card ι₂ : ℝ) ≤ N ^ (d + η) →
      (∀ i k, |a₁ i k| ≤ 3) → (∀ j k, |a₂ j k| ≤ 3) →
      (∀ i, 0 ≤ π₁ i) → (∀ j, 0 ≤ π₂ j) → (∑ i, π₁ i) = 1 → (∑ j, π₂ j) = 1 →
      IsProbabilityMeasure μ →
      (∀ i (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * volume E) →
      (∀ j (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ j) * volume E) →
      ¬ (∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0:ℝ) 1 ∧
          |quad (a₁ p.1.1) p.2 - quad (a₂ p.1.2) p.2| ≤ 2 / N ∧
          1 ≤ cnorm (a₁ p.1.1 - a₂ p.1.2)) := by
  obtain ⟨η, hη, N₀, hN₀, H⟩ := hM 2 3 (by norm_num) (by norm_num) d hd0 hd1
  refine ⟨η, hη, max (max N₀ 8) (max (8 ^ (1 / η)) (9 ^ (1 / η))),
    le_trans hN₀ (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro N hN ι₁ ι₂ _ _ _ _ _ _ a₁ a₂ π₁ π₂ μ hc₁ hc₂ ha₁ ha₂ hπ₁ hπ₂ hs₁ hs₂ hμ hm₁ hm₂ hbad
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN8' : (8:ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN8 : 8 ^ (1 / η) ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN9 : 9 ^ (1 / η) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNpos : 0 < N := by linarith
  have hNη9 : 9 ≤ N ^ η := by
    have := Real.rpow_le_rpow (by positivity) hN9 (le_of_lt hη)
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel (ne_of_gt hη), Real.rpow_one] at this
  have hNη8 : 8 ≤ N ^ η := by
    have := Real.rpow_le_rpow (by positivity) hN8 (le_of_lt hη)
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel (ne_of_gt hη), Real.rpow_one] at this
  have hNnegη : N ^ (-η) ≤ 1 / 8 := by
    rw [Real.rpow_neg (le_of_lt hNpos), one_div]
    exact inv_anti₀ (by norm_num) hNη8
  have hclose : 2 / N ≤ N ^ (-1 + η) := by
    rw [Real.rpow_add hNpos, Real.rpow_neg_one]
    rw [div_eq_mul_inv, mul_comm]
    gcongr
    linarith
  have hquarter : 2 / N ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hNpos (by norm_num)]; linarith
  -- transport to `Fin`
  let e₁ := discreteEquiv (Fintype.equivFin ι₁)
  let e₂ := discreteEquiv (Fintype.equivFin ι₂)
  let Φ : (ι₁ × ι₂) × ℝ ≃ᵐ (Fin (Fintype.card ι₁) × Fin (Fintype.card ι₂)) × ℝ :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr e₁ e₂) (MeasurableEquiv.refl ℝ)
  have hΦ : ∀ p : (ι₁ × ι₂) × ℝ, Φ p = ((e₁ p.1.1, e₂ p.1.2), p.2) := fun p => rfl
  let f₁ : Fin (Fintype.card ι₁) → ℝ → ℝ := fun i => quad (a₁ (e₁.symm i))
  let f₂ : Fin (Fintype.card ι₂) → ℝ → ℝ := fun j => quad (a₂ (e₂.symm j))
  have key := H N hN0 (Fintype.card ι₁) (Fintype.card ι₂) f₁ f₂
    (fun i => π₁ (e₁.symm i)) (fun j => π₂ (e₂.symm j)) (μ.map Φ) hc₁ hc₂
    (fun i => (contDiff_quad _).contDiffOn) (fun i => (contDiff_quad _).contDiffOn)
    (fun i j _ t ht => by
      have := abs_iteratedDeriv_quad_le (a₁ (e₁.symm i)) (B := 3) (fun k => ha₁ _ k) ht j
      linarith)
    (fun i j _ t ht => by
      have := abs_iteratedDeriv_quad_le (a₂ (e₂.symm i)) (B := 3) (fun k => ha₂ _ k) ht j
      linarith)
    (fun i => hπ₁ _) (fun j => hπ₂ _)
    (by rw [← hs₁]; exact Equiv.sum_comp e₁.symm.toEquiv π₁)
    (by rw [← hs₂]; exact Equiv.sum_comp e₂.symm.toEquiv π₂)
    ⟨by rw [MeasurableEquiv.map_apply]; simp⟩
    (fun i E hE => by
      rw [MeasurableEquiv.map_apply]
      have : Φ ⁻¹' {p | p.1.1 = i ∧ p.2 ∈ E} = {p | p.1.1 = e₁.symm i ∧ p.2 ∈ E} := by
        ext p
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hΦ]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by rw [← h1]; simp, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; simp, h2⟩
      rw [this]; exact hm₁ _ E hE)
    (fun j E hE => by
      rw [MeasurableEquiv.map_apply]
      have : Φ ⁻¹' {p | p.1.2 = j ∧ p.2 ∈ E} = {p | p.1.2 = e₂.symm j ∧ p.2 ∈ E} := by
        ext p
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hΦ]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by rw [← h1]; simp, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; simp, h2⟩
      rw [this]; exact hm₂ _ E hE)
  apply key
  rw [MeasurableEquiv.map_apply]
  refine measure_mono_null ?_ (ae_iff.mp hbad)
  intro p hpS
  simp only [Set.mem_ofPred_eq]
  intro hp
  apply hpS
  obtain ⟨hx, hval, hnorm⟩ := hp
  simp only [Set.mem_ofPred_eq, hΦ, f₁, f₂, MeasurableEquiv.symm_apply_apply]
  refine ⟨hx, le_trans hval hclose, ?_⟩
  have hv : |quad (a₁ p.1.1 - a₂ p.1.2) p.2| ≤ 1 / 4 := by
    rw [← quad_sub]; exact le_trans hval hquarter
  rcases deriv_separation _ hnorm hx hv with h | h
  · refine ⟨1, le_refl _, by norm_num, ?_⟩
    rw [iteratedDeriv_quad_sub _ _ (le_refl _) (by norm_num)]
    linarith
  · refine ⟨2, by norm_num, le_refl _, ?_⟩
    rw [iteratedDeriv_quad_sub _ _ (by norm_num) (le_refl _)]
    linarith

/-- `Match` for quadratics with coefficients bounded by `L`, indexed by finite types:
a probability pair law with the two marginal ceilings cannot be carried by pairs that
are `2/N`-close at a point of `[0,1]` while their coefficient vectors differ by at
least one. -/
theorem match_quadL (hM : MatchHyp) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ L : ℝ, 1 ≤ L → ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]
      (a₁ : ι₁ → Fin 3 → ℝ) (a₂ : ι₂ → Fin 3 → ℝ) (π₁ : ι₁ → ℝ) (π₂ : ι₂ → ℝ)
      (μ : Measure ((ι₁ × ι₂) × ℝ)),
      (Fintype.card ι₁ : ℝ) ≤ N ^ (d + η) → (Fintype.card ι₂ : ℝ) ≤ N ^ (d + η) →
      (∀ i k, |a₁ i k| ≤ L) → (∀ j k, |a₂ j k| ≤ L) →
      (∀ i, 0 ≤ π₁ i) → (∀ j, 0 ≤ π₂ j) → (∑ i, π₁ i) = 1 → (∑ j, π₂ j) = 1 →
      IsProbabilityMeasure μ →
      (∀ i (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * volume E) →
      (∀ j (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ j) * volume E) →
      ¬ (∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0:ℝ) 1 ∧
          |quad (a₁ p.1.1) p.2 - quad (a₂ p.1.2) p.2| ≤ 2 / N ∧
          1 ≤ cnorm (a₁ p.1.1 - a₂ p.1.2)) := by
  obtain ⟨η, hη, N₀, hN₀, H⟩ := hM 2 3 (by norm_num) (by norm_num) d hd0 hd1
  refine ⟨η, hη, fun L hL => ⟨max (max N₀ 8) (max (8 ^ (1 / η)) ((3 * L) ^ (1 / η))),
    le_trans hN₀ (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩⟩
  intro N hN ι₁ ι₂ _ _ _ _ _ _ a₁ a₂ π₁ π₂ μ hc₁ hc₂ ha₁ ha₂ hπ₁ hπ₂ hs₁ hs₂ hμ hm₁ hm₂ hbad
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN8' : (8:ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN8 : 8 ^ (1 / η) ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN9 : (3 * L) ^ (1 / η) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNpos : 0 < N := by linarith
  have hNη9 : 3 * L ≤ N ^ η := by
    have h3L : (0:ℝ) ≤ 3 * L := by linarith
    have := Real.rpow_le_rpow (Real.rpow_nonneg h3L _) hN9 (le_of_lt hη)
    rwa [← Real.rpow_mul h3L, one_div_mul_cancel (ne_of_gt hη), Real.rpow_one] at this
  have hNη8 : 8 ≤ N ^ η := by
    have := Real.rpow_le_rpow (by positivity) hN8 (le_of_lt hη)
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel (ne_of_gt hη), Real.rpow_one] at this
  have hNnegη : N ^ (-η) ≤ 1 / 8 := by
    rw [Real.rpow_neg (le_of_lt hNpos), one_div]
    exact inv_anti₀ (by norm_num) hNη8
  have hclose : 2 / N ≤ N ^ (-1 + η) := by
    rw [Real.rpow_add hNpos, Real.rpow_neg_one]
    rw [div_eq_mul_inv, mul_comm]
    gcongr
    linarith
  have hquarter : 2 / N ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hNpos (by norm_num)]; linarith
  -- transport to `Fin`
  let e₁ := discreteEquiv (Fintype.equivFin ι₁)
  let e₂ := discreteEquiv (Fintype.equivFin ι₂)
  let Φ : (ι₁ × ι₂) × ℝ ≃ᵐ (Fin (Fintype.card ι₁) × Fin (Fintype.card ι₂)) × ℝ :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr e₁ e₂) (MeasurableEquiv.refl ℝ)
  have hΦ : ∀ p : (ι₁ × ι₂) × ℝ, Φ p = ((e₁ p.1.1, e₂ p.1.2), p.2) := fun p => rfl
  let f₁ : Fin (Fintype.card ι₁) → ℝ → ℝ := fun i => quad (a₁ (e₁.symm i))
  let f₂ : Fin (Fintype.card ι₂) → ℝ → ℝ := fun j => quad (a₂ (e₂.symm j))
  have key := H N hN0 (Fintype.card ι₁) (Fintype.card ι₂) f₁ f₂
    (fun i => π₁ (e₁.symm i)) (fun j => π₂ (e₂.symm j)) (μ.map Φ) hc₁ hc₂
    (fun i => (contDiff_quad _).contDiffOn) (fun i => (contDiff_quad _).contDiffOn)
    (fun i j _ t ht => by
      have := abs_iteratedDeriv_quad_le (a₁ (e₁.symm i)) (B := L) (fun k => ha₁ _ k) ht j
      linarith)
    (fun i j _ t ht => by
      have := abs_iteratedDeriv_quad_le (a₂ (e₂.symm i)) (B := L) (fun k => ha₂ _ k) ht j
      linarith)
    (fun i => hπ₁ _) (fun j => hπ₂ _)
    (by rw [← hs₁]; exact Equiv.sum_comp e₁.symm.toEquiv π₁)
    (by rw [← hs₂]; exact Equiv.sum_comp e₂.symm.toEquiv π₂)
    ⟨by rw [MeasurableEquiv.map_apply]; simp⟩
    (fun i E hE => by
      rw [MeasurableEquiv.map_apply]
      have : Φ ⁻¹' {p | p.1.1 = i ∧ p.2 ∈ E} = {p | p.1.1 = e₁.symm i ∧ p.2 ∈ E} := by
        ext p
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hΦ]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by rw [← h1]; simp, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; simp, h2⟩
      rw [this]; exact hm₁ _ E hE)
    (fun j E hE => by
      rw [MeasurableEquiv.map_apply]
      have : Φ ⁻¹' {p | p.1.2 = j ∧ p.2 ∈ E} = {p | p.1.2 = e₂.symm j ∧ p.2 ∈ E} := by
        ext p
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hΦ]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by rw [← h1]; simp, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; simp, h2⟩
      rw [this]; exact hm₂ _ E hE)
  apply key
  rw [MeasurableEquiv.map_apply]
  refine measure_mono_null ?_ (ae_iff.mp hbad)
  intro p hpS
  simp only [Set.mem_ofPred_eq]
  intro hp
  apply hpS
  obtain ⟨hx, hval, hnorm⟩ := hp
  simp only [Set.mem_ofPred_eq, hΦ, f₁, f₂, MeasurableEquiv.symm_apply_apply]
  refine ⟨hx, le_trans hval hclose, ?_⟩
  have hv : |quad (a₁ p.1.1 - a₂ p.1.2) p.2| ≤ 1 / 4 := by
    rw [← quad_sub]; exact le_trans hval hquarter
  rcases deriv_separation _ hnorm hx hv with h | h
  · refine ⟨1, le_refl _, by norm_num, ?_⟩
    rw [iteratedDeriv_quad_sub _ _ (le_refl _) (by norm_num)]
    linarith
  · refine ⟨2, by norm_num, le_refl _, ?_⟩
    rw [iteratedDeriv_quad_sub _ _ (by norm_num) (le_refl _)]
    linarith

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchCor
