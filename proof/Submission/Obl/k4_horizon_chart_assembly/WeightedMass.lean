import Submission.Obl.k4_horizon_chart_assembly.IsoCodes
import Submission.Obl.k4_horizon_chart_assembly.Selections
import Submission.Obl.k4_horizon_chart_assembly.GroupPreparation

/-!
# The kernel inputs of a world and its mass balance

For one world (prior `ν`, event `E`, native test `P`, scale `B`) on the isotropic fine mesh
`ρ = q/D`: the kernel's good set of block `j` (normalized incidences in heavy fine cells), the
code table of group `Γ` (codes met by the heavy cells it visits), and the per-world balance

  `total ≤ ∑ selected + light + s + (4 L₀ C τ₀ D^ζ / (s θ q²)) · total`

from the per-group identities `selected + q · residual = group mass` and the kernel's residual
bound, summed over the blocks and the native groups.
-/

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory MvPolynomial
open scoped ENNReal BigOperators

noncomputable section

/-! ## Kernel inputs -/

/-- The heavy fine cells of a world on the isotropic mesh `q/D`, at floor `θ`. -/
def worldHeavy (ν : Measure Trajectory) (E : Set Incidence) (B a q θ : ℝ) (D : ℕ) :
    Set ((Fin 3 → ℤ) × ℤ) :=
  heavySet ν E (worldCell (q / D) (q / D) B a) (θ * (q / D) ^ 3)

/-- The incidences in heavy fine cells. -/
def heavyIncidences (ν : Measure Trajectory) (E : Set Incidence) (B a q θ : ℝ) (D : ℕ) :
    Set Incidence :=
  worldCell (q / D) (q / D) B a ⁻¹' worldHeavy ν E B a q θ D

/-- The kernel's good set of block `j`. -/
def blockGood (ν : Measure Trajectory) (E : Set Incidence) (B a q θ : ℝ) (D j : ℕ) :
    Set Incidence :=
  timeLift ((j : ℝ) * q) q ⁻¹' heavyIncidences ν E B a q θ D

/-- The light incidences of a world: those whose fine cell weighs less than `θ ρ³`. -/
def worldLight (ν : Measure Trajectory) (E : Set Incidence) (B a q θ : ℝ) (D : ℕ) :
    Set Incidence :=
  {p | p ∈ E ∧ (ν.prod volume) (E ∩ worldCell (q / D) (q / D) B a ⁻¹'
    {worldCell (q / D) (q / D) B a p}) < ENNReal.ofReal (θ * (q / D) ^ 3)}

/-- The kernel's code table of group `Γ` of block `j`. -/
def groupTable (ν : Measure Trajectory) (E : Set Incidence) (P : MvPolynomial (Fin 4) ℝ)
    (B K H a q θ R : ℝ) (D j : ℕ) (Γ : (Fin 2 → ℤ) × ℤ) : Finset (ℤ × (Fin 2 → ℤ)) :=
  isoKernelCodes (worldHeavy ν E B a q θ D)
    (groupVisits P B K H a q (q / D) (q / D) (derivativeEvent E P (B / K)) j Γ)
    (isoCodes D R j Γ.1)

theorem measurableSet_of_countable_type {Z : Type*} [MeasurableSpace Z] [Countable Z]
    [MeasurableSingletonClass Z] (S : Set Z) : MeasurableSet S :=
  S.to_countable.measurableSet

theorem heavyIncidences_measurable (ν : Measure Trajectory) (E : Set Incidence)
    (B a q θ : ℝ) (D : ℕ) : MeasurableSet (heavyIncidences ν E B a q θ D) :=
  (measurable_worldCell _ _ B a) (measurableSet_of_countable_type _)

theorem blockGood_measurable (ν : Measure Trajectory) (E : Set Incidence)
    (B a q θ : ℝ) (D j : ℕ) : MeasurableSet (blockGood ν E B a q θ D j) :=
  (measurable_timeLift _ q) (heavyIncidences_measurable ν E B a q θ D)

theorem worldHeavy_finite (ν : Measure Trajectory) [IsFiniteMeasure ν]
    {E : Set Incidence} (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (B a : ℝ) {q θ : ℝ}
    (hq : 0 < q) (hθ : 0 < θ) {D : ℕ} (hD : 0 < D) :
    (worldHeavy ν E B a q θ D).Finite := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  exact heavySet_finite ν hunit (measurable_worldCell _ _ B a) (by positivity)

/-- The code-table hypothesis of the kernel for group `Γ` of block `j`. -/
theorem groupTable_mem (ν : Measure Trajectory) [IsFiniteMeasure ν]
    {E : Set Incidence} (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (P : MvPolynomial (Fin 4) ℝ) {B K H a q θ R : ℝ} (hq : 0 < q) (hθ : 0 < θ)
    (hR : 1 ≤ R) {D : ℕ} (hD : 0 < D) (j : ℕ) (Γ : (Fin 2 → ℤ) × ℤ) :
    ∀ p ∈ normalizedEvent (derivativeEvent E P (B / K)) ((j : ℝ) * q) q ∩
        blockGood ν E B a q θ D j,
      p.1 ∈ nativeGroup P B K H ((j : ℝ) * q) q a Γ →
      (⌊p.2 * (D : ℝ)⌋, fun e : Fin 2 => ⌊(D : ℝ) *
        (groupIntercept q a ((j : ℝ) * q) (R * q) Γ p.1 +
          p.2 • groupVelocity q (R * q) p.1) e⌋) ∈ groupTable ν E P B K H a q θ R D j Γ := by
  intro p hp hpU
  obtain ⟨⟨hpt, hpE⟩, hpG⟩ := hp
  have ht := (mem_prod.mp hpt).2
  apply mem_isoKernelCodes (worldHeavy_finite ν hunit B a hq hθ hD) hpG
  · refine ⟨timeLift ((j : ℝ) * q) q p, hpE, hpU, ?_, rfl⟩
    simp only [timeLift, mem_Ico]
    constructor <;> nlinarith [ht.1, ht.2]
  · exact normalized_code_mem_isoCodes B a hq hR hD j Γ p

/-! ## Total table size of a world -/

/-- The kernel tables of all groups of a world have total size at most four times the native
multiplicity times the number of heavy cells. -/
theorem sum_groupTable_card_le (ν : Measure Trajectory) [IsFiniteMeasure ν]
    {E : Set Incidence} (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {B K H a q θ R : ℝ} (hB : 0 < B) (hK : 0 ≤ K) (hH : 1 ≤ H)
    (hcoeff : ∀ e, |P.coeff e| ≤ H) (hBinv : B⁻¹ ≤ H)
    (ha : 0 < a) (ha1 : a ≤ 1) (hq : 0 < q) (hqa : q ≤ a) (hθ : 0 < θ) {D : ℕ} (hD : 0 < D)
    (hmesh : 4131 * H * (3 * H + 1) ^ 2 * (q / D) ≤ a)
    (I : Finset (ℕ × ((Fin 2 → ℤ) × ℤ))) (hI : ∀ i ∈ I, (i.1 : ℝ) * q ≤ 1) :
    (∑ i ∈ I, ((groupTable ν E P B K H a q θ R D i.1 i.2).card : ℝ)) ≤
      4 * nativeMultiplicity K * ((ν.prod volume).real E / (θ * (q / D) ^ 3)) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hfin := worldHeavy_finite ν hunit B a hq hθ hD
  have h := sum_isoKernelCodes_card_le I hfin
    (fun i => groupVisits P B K H a q (q / D) (q / D) (derivativeEvent E P (B / K)) i.1 i.2)
    (fun i => isoCodes D R i.1 i.2.1) (fun i Z => isoCodes_card_le D R i.1 i.2.1 Z)
    (L := nativeMultiplicity K) (by
      intro Z _ F hF hvis
      exact groupVisits_card_le P hP hB hK hH hcoeff hBinv ha ha1 hq hqa hD le_rfl
        (div_le_self hq.le hD1) hmesh (inter_subset_left) hunit Z F
        (fun i hi => hI i (hF hi)) hvis)
  have hcard := heavySet_card_le ν hunit (measurable_worldCell (q / D) (q / D) B a)
    (show 0 < θ * (q / D) ^ 3 by positivity)
  have hL : 0 ≤ nativeMultiplicity K := by unfold nativeMultiplicity; positivity
  calc
    _ ≤ 4 * nativeMultiplicity K * (hfin.toFinset.card : ℝ) := h
    _ ≤ 4 * nativeMultiplicity K * ((ν.prod volume).real E / (θ * (q / D) ^ 3)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)

end

end Submission.Obl.k4_horizon_chart_assembly

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory MvPolynomial
open scoped ENNReal BigOperators

noncomputable section

/-! ## Partition of a world's mass into blocks and native groups -/

theorem nativeEligible_measurable (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (B : ℝ) {K H : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H) :
    MeasurableSet {l : Trajectory | nativeEligible P B K H l} := by
  have heq : {l : Trajectory | nativeEligible P B K H l} =
      ⋃ Γ : (Fin 2 → ℤ) × ℤ, nativeGroup P B K H 0 1 1 Γ := by
    ext l
    simp only [mem_setOf_eq, mem_iUnion, nativeGroup]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun Γ => nativeGroup_measurable P hP B 0 hK hH one_pos one_pos Γ)

theorem derivativeEvent_measurable {E : Set Incidence} (hE : MeasurableSet E)
    (P : MvPolynomial (Fin 4) ℝ) (f : ℝ) : MeasurableSet (derivativeEvent E P f) :=
  hE.inter (Submission.Obl.k4_quadratic_atlas_normalization.measurableSet_derivativeFloorSet P f)

/-- Up to a null set, a world's incidences are those of eligible trajectories with the native
derivative floor. -/
theorem mass_eq_eligible (ν : Measure Trajectory) [SFinite ν]
    {E : Set Incidence} (hE : MeasurableSet E)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) {B K H : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hbox : ∀ p ∈ E, (p.1.1 : ℝ) ≤ H ∧ ∀ e, |p.1.2 e| ≤ H)
    (hupper : ∀ᵐ l ∂ν, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖yl l t‖ + ‖vl l‖ ≤ K ∧ |eval (xl l t) P| ≤ K ∧
      |eval (xl l t) (pderiv (3 : Fin 4) P)| ≤ K * B ∧
      |eval (xl l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K * B ^ 2)
    (hlower : ∀ᵐ p ∂(ν.prod volume).restrict E,
      B / K ≤ |eval (xl p.1 p.2) (pderiv (3 : Fin 4) P)|) :
    (ν.prod volume) E = (ν.prod volume)
      (derivativeEvent E P (B / K) ∩ ({l | nativeEligible P B K H l} ×ˢ univ)) := by
  set E₁ := derivativeEvent E P (B / K) ∩ ({l | nativeEligible P B K H l} ×ˢ univ)
  have hE₁ : MeasurableSet E₁ := (derivativeEvent_measurable hE P _).inter
    ((nativeEligible_measurable P hP B hK hH).prod MeasurableSet.univ)
  have hsub : E₁ ⊆ E := fun p hp => hp.1.1
  have hae : ∀ᵐ p ∂(ν.prod volume).restrict E, p ∈ E₁ := by
    filter_upwards [nativeEligible_ae ν E hE P B K H hbox hupper, hlower,
      ae_restrict_mem hE] with p h1 h2 h3
    exact ⟨⟨h3, h2⟩, h1, mem_univ _⟩
  have hnull : ((ν.prod volume).restrict E) E₁ᶜ = 0 := ae_iff.mp hae
  calc
    (ν.prod volume) E = ((ν.prod volume).restrict E) univ := by
      rw [Measure.restrict_apply_univ]
    _ = ((ν.prod volume).restrict E) E₁ := by
      rw [← measure_add_measure_compl hE₁, hnull, add_zero]
    _ = (ν.prod volume) E₁ := by
      rw [Measure.restrict_apply hE₁, inter_eq_left.mpr hsub]

/-- The blocks partition the eligible incidences. -/
theorem eligible_mass_eq_sum_blocks (ν : Measure Trajectory) [SFinite ν]
    {E : Set Incidence} (hE : MeasurableSet E) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) {B K H : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (T : ℕ) :
    (ν.prod volume) (derivativeEvent E P (B / K) ∩ ({l | nativeEligible P B K H l} ×ˢ univ)) =
      ∑ j ∈ Finset.range (2 ^ T), (ν.prod volume) (derivativeEvent E P (B / K) ∩
        ({l | nativeEligible P B K H l} ×ˢ
          Ico ((j : ℝ) * ((2 : ℝ) ^ T)⁻¹) ((j : ℝ) * ((2 : ℝ) ^ T)⁻¹ + ((2 : ℝ) ^ T)⁻¹))) := by
  set E₁ := derivativeEvent E P (B / K) ∩ ({l | nativeEligible P B K H l} ×ˢ univ)
  have hE₁ : MeasurableSet E₁ := (derivativeEvent_measurable hE P _).inter
    ((nativeEligible_measurable P hP B hK hH).prod MeasurableSet.univ)
  have hunit₁ : E₁ ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun p hp => hunit hp.1.1
  have hJ : 0 < 2 ^ T := by positivity
  have h := sum_block_incidence ν E₁ hE₁ hunit₁ hJ
  rw [← h, Finset.sum_range (fun j => (ν.prod volume) (derivativeEvent E P (B / K) ∩
        ({l | nativeEligible P B K H l} ×ˢ
          Ico ((j : ℝ) * ((2 : ℝ) ^ T)⁻¹) ((j : ℝ) * ((2 : ℝ) ^ T)⁻¹ + ((2 : ℝ) ^ T)⁻¹))))]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ext p
  simp only [E₁, Submission.Obl.k4_scalar_marked_coefficient_smoothing.timeCell,
    mem_inter_iff, mem_prod, mem_univ, and_true, true_and, mem_Ico, mem_setOf_eq]
  have h2 : ((2 ^ T : ℕ) : ℝ) = (2 : ℝ) ^ T := by push_cast; ring
  rw [h2]
  simp only [div_eq_mul_inv, add_mul, one_mul]
  tauto

/-- The native groups of a block partition its eligible incidences. -/
theorem block_mass_eq_sum_groups (ν : Measure Trajectory) [SFinite ν]
    {E : Set Incidence} (hE : MeasurableSet E)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) {B K H a q s : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hq : 0 < q) (ha : 0 < a) (hs : s ∈ Icc (0 : ℝ) 1) :
    (ν.prod volume) (derivativeEvent E P (B / K) ∩
        ({l | nativeEligible P B K H l} ×ˢ Ico s (s + q))) =
      ∑ Γ ∈ midpointGroupUniverse q a K,
        (ν.prod volume) (selectedEvent E (nativeGroup P B K H s q a Γ) P (B / K) s q) := by
  classical
  have hunion : derivativeEvent E P (B / K) ∩
      ({l | nativeEligible P B K H l} ×ˢ Ico s (s + q)) =
      ⋃ Γ ∈ midpointGroupUniverse q a K,
        selectedEvent E (nativeGroup P B K H s q a Γ) P (B / K) s q := by
    ext p
    simp only [mem_iUnion, selectedEvent_eq, mem_inter_iff, mem_prod, mem_setOf_eq,
      exists_prop]
    constructor
    · rintro ⟨hd, hel, ht⟩
      exact ⟨midpointGroupCode P s q a p.1.2,
        nativeGroup_mem_universe P B K H s q a hq ha hK hs hel, hd, ⟨hel, rfl⟩, ht⟩
    · rintro ⟨Γ, -, hd, hU, ht⟩
      exact ⟨hd, hU.1, ht⟩
  rw [hunion]
  apply measure_biUnion_finset
  · intro Γ _ Γ' _ hne
    apply Set.disjoint_left.mpr
    intro p hp hp'
    change p ∈ selectedEvent E (nativeGroup P B K H s q a Γ) P (B / K) s q at hp
    change p ∈ selectedEvent E (nativeGroup P B K H s q a Γ') P (B / K) s q at hp'
    rw [selectedEvent_eq] at hp hp'
    exact Set.disjoint_left.mp (nativeGroup_disjoint P B K H s q a hne) hp.2.1 hp'.2.1
  · intro Γ _
    change MeasurableSet (selectedEvent E (nativeGroup P B K H s q a Γ) P (B / K) s q)
    rw [selectedEvent_eq]
    exact (derivativeEvent_measurable hE P _).inter
      ((nativeGroup_measurable P hP B s hK hH hq ha Γ).prod measurableSet_Ico)

theorem Ico_block_disjoint {q : ℝ} (hq : 0 < q) {j j' : ℕ} (hne : j ≠ j') :
    Disjoint (Ico ((j : ℝ) * q) ((j : ℝ) * q + q)) (Ico ((j' : ℝ) * q) ((j' : ℝ) * q + q)) := by
  apply Set.disjoint_left.mpr
  intro t ht ht'
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have h1 : ((j : ℝ) + 1) ≤ j' := by exact_mod_cast h
    nlinarith [ht.2, ht'.1]
  · have h1 : ((j' : ℝ) + 1) ≤ j := by exact_mod_cast h
    nlinarith [ht.1, ht'.2]

/-- The light parts of the kernel residuals of all groups add up to at most the light mass. -/
theorem light_sum_le (ν : Measure Trajectory) [SFinite ν]
    {E : Set Incidence} (hE : MeasurableSet E)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) {B K H a q θ : ℝ} {D : ℕ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hq : 0 < q) (ha : 0 < a) (J : ℕ)
    (Res : ℕ → (Fin 2 → ℤ) × ℤ → Set Trajectory)
    (hRes : ∀ j Γ, Res j Γ ⊆ nativeGroup P B K H ((j : ℝ) * q) q a Γ) :
    (∑ j ∈ Finset.range J, ∑ Γ ∈ midpointGroupUniverse q a K,
      ENNReal.ofReal q * (ν.prod volume)
        (normalizedEvent (derivativeEvent E P (B / K)) ((j : ℝ) * q) q ∩
          (blockGood ν E B a q θ D j)ᶜ ∩ (Res j Γ ×ˢ univ))) ≤
      (ν.prod volume) (worldLight ν E B a q θ D) := by
  classical
  set dE := derivativeEvent E P (B / K)
  set Hv := heavyIncidences ν E B a q θ D
  let S : ℕ × ((Fin 2 → ℤ) × ℤ) → Set Incidence := fun i =>
    (dE ∩ Hvᶜ) ∩ (nativeGroup P B K H ((i.1 : ℝ) * q) q a i.2 ×ˢ
      Ico ((i.1 : ℝ) * q) ((i.1 : ℝ) * q + q))
  have hdEm : MeasurableSet (dE ∩ Hvᶜ) :=
    (derivativeEvent_measurable hE P _).inter (heavyIncidences_measurable ν E B a q θ D).compl
  have hterm : ∀ (j : ℕ) (Γ : (Fin 2 → ℤ) × ℤ), ENNReal.ofReal q * (ν.prod volume)
      (normalizedEvent dE ((j : ℝ) * q) q ∩ (blockGood ν E B a q θ D j)ᶜ ∩ (Res j Γ ×ˢ univ)) ≤
      (ν.prod volume) (S (j, Γ)) := by
    intro j Γ
    have hU := nativeGroup_measurable P hP B ((j : ℝ) * q) hK hH hq ha Γ
    rw [← normalized_incidence_mass ν hdEm hU ((j : ℝ) * q) hq]
    apply mul_le_mul_right
    apply measure_mono
    rintro p ⟨⟨⟨hpt, hpE⟩, hpG⟩, hpR⟩
    refine ⟨⟨hpt, hpE, hpG⟩, ?_⟩
    exact ⟨hRes j Γ (mem_prod.mp hpR).1, mem_univ _⟩
  calc
    _ ≤ ∑ j ∈ Finset.range J, ∑ Γ ∈ midpointGroupUniverse q a K, (ν.prod volume) (S (j, Γ)) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun Γ _ => hterm j Γ))
    _ = ∑ i ∈ Finset.range J ×ˢ midpointGroupUniverse q a K, (ν.prod volume) (S i) := by
      rw [Finset.sum_product]
    _ = (ν.prod volume) (⋃ i ∈ Finset.range J ×ˢ midpointGroupUniverse q a K, S i) := by
      symm
      apply measure_biUnion_finset
      · rintro ⟨j, Γ⟩ _ ⟨j', Γ'⟩ _ hne
        apply Set.disjoint_left.mpr
        rintro p ⟨-, hp1, hp2⟩ ⟨-, hp1', hp2'⟩
        by_cases hj : j = j'
        · subst hj
          have hΓ : Γ ≠ Γ' := fun h => hne (by rw [h])
          exact Set.disjoint_left.mp (nativeGroup_disjoint P B K H _ q a hΓ) hp1 hp1'
        · exact Set.disjoint_left.mp (Ico_block_disjoint hq hj) hp2 hp2'
      · rintro ⟨j, Γ⟩ _
        exact hdEm.inter ((nativeGroup_measurable P hP B _ hK hH hq ha Γ).prod measurableSet_Ico)
    _ ≤ (ν.prod volume) (worldLight ν E B a q θ D) := by
      apply measure_mono
      intro p hp
      simp only [mem_iUnion] at hp
      obtain ⟨i, -, ⟨hpd, hpH⟩, -⟩ := hp
      refine ⟨hpd.1, ?_⟩
      have : ¬ (ENNReal.ofReal (θ * (q / D) ^ 3) ≤
          (ν.prod volume) (E ∩ worldCell (q / D) (q / D) B a ⁻¹'
            {worldCell (q / D) (q / D) B a p})) := hpH
      exact lt_of_not_ge this

/-- The duration parts of the kernel residuals add up to at most `s`. -/
theorem duration_sum_le (ν : Measure Trajectory) [IsProbabilityMeasure ν]
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) {B K H a q σ : ℝ} {T : ℕ}
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hq : 0 < q) (ha : 0 < a) (hσ : 0 ≤ σ)
    (hqT : q = ((2 : ℝ) ^ T)⁻¹)
    (Res : ℕ → (Fin 2 → ℤ) × ℤ → Set Trajectory)
    (hRes : ∀ j Γ, Res j Γ ⊆ nativeGroup P B K H ((j : ℝ) * q) q a Γ) :
    (∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K,
      ENNReal.ofReal q * (ENNReal.ofReal σ * ν (Res j Γ))) ≤ ENNReal.ofReal σ := by
  classical
  have hblock : ∀ j : ℕ, (∑ Γ ∈ midpointGroupUniverse q a K, ν (Res j Γ)) ≤ 1 := by
    intro j
    calc
      (∑ Γ ∈ midpointGroupUniverse q a K, ν (Res j Γ)) ≤
          ∑ Γ ∈ midpointGroupUniverse q a K, ν (nativeGroup P B K H ((j : ℝ) * q) q a Γ) :=
        Finset.sum_le_sum (fun Γ _ => measure_mono (hRes j Γ))
      _ = ν (⋃ Γ ∈ midpointGroupUniverse q a K, nativeGroup P B K H ((j : ℝ) * q) q a Γ) := by
        symm
        apply measure_biUnion_finset
        · intro Γ _ Γ' _ hne
          exact nativeGroup_disjoint P B K H _ q a hne
        · intro Γ _
          exact nativeGroup_measurable P hP B _ hK hH hq ha Γ
      _ ≤ ν univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  calc
    _ = ∑ j ∈ Finset.range (2 ^ T), ENNReal.ofReal q * (ENNReal.ofReal σ *
        ∑ Γ ∈ midpointGroupUniverse q a K, ν (Res j Γ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ ∑ _j ∈ Finset.range (2 ^ T), ENNReal.ofReal q * (ENNReal.ofReal σ * 1) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_right (mul_le_mul_right (hblock j) _) _)
    _ = ENNReal.ofReal σ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, ← mul_assoc]
      have h2 : ((2 ^ T : ℕ) : ℝ≥0∞) * ENNReal.ofReal q = 1 := by
        rw [hqT, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        push_cast
        rw [mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
      rw [h2, one_mul]

theorem incidence_mass_lt_top (ν : Measure Trajectory) [IsFiniteMeasure ν]
    {E : Set Incidence} (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) : (ν.prod volume) E < ⊤ := by
  calc
    (ν.prod volume) E ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hunit
    _ = ν univ * volume (Icc (0 : ℝ) 1) := Measure.prod_prod _ _
    _ < ⊤ := by
      rw [Real.volume_Icc]
      exact ENNReal.mul_lt_top (measure_lt_top ν univ) ENNReal.ofReal_lt_top

/-- The table parts of the kernel residuals add up to a fixed multiple of the world's mass. -/
theorem table_sum_le (ν : Measure Trajectory) [IsFiniteMeasure ν]
    {E : Set Incidence} (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {B K H a q θ R C τ₀ σ ζ : ℝ} {D T : ℕ} (hB : 0 < B) (hK : 0 ≤ K) (hH : 1 ≤ H)
    (hcoeff : ∀ e, |P.coeff e| ≤ H) (hBinv : B⁻¹ ≤ H)
    (ha : 0 < a) (ha1 : a ≤ 1) (hqa : q ≤ a) (hθ : 0 < θ) (hD : 0 < D)
    (hmesh : 4131 * H * (3 * H + 1) ^ 2 * (q / D) ≤ a)
    (hσ : 0 < σ) (hC : 0 ≤ C) (hτ₀ : 0 ≤ τ₀) (hqT : q = ((2 : ℝ) ^ T)⁻¹) :
    (∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K,
      ENNReal.ofReal q * ENNReal.ofReal (C * τ₀ * (D : ℝ) ^ ζ / (σ * (D : ℝ) ^ 3) *
        ((groupTable ν E P B K H a q θ R D j Γ).card : ℝ))) ≤
      ENNReal.ofReal (4 * nativeMultiplicity K * C * τ₀ * (D : ℝ) ^ ζ / (σ * θ * q ^ 2)) *
        (ν.prod volume) E := by
  classical
  have hq : 0 < q := by rw [hqT]; positivity
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  set c₀ := C * τ₀ * (D : ℝ) ^ ζ / (σ * (D : ℝ) ^ 3) with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hI : ∀ i ∈ Finset.range (2 ^ T) ×ˢ midpointGroupUniverse q a K, (i.1 : ℝ) * q ≤ 1 := by
    intro i hi
    have h1 : i.1 < 2 ^ T := Finset.mem_range.mp (Finset.mem_product.mp hi).1
    have h2 : (i.1 : ℝ) ≤ (2 : ℝ) ^ T := by exact_mod_cast h1.le
    rw [hqT]
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact h2
  have hsum := sum_groupTable_card_le ν hunit P hP (R := R) hB hK hH hcoeff hBinv ha ha1 hq hqa
    hθ hD hmesh _ hI
  rw [Finset.sum_product] at hsum
  set M := (ν.prod volume).real E
  have hfin := incidence_mass_lt_top ν hunit
  have hterm : ∀ j Γ, ENNReal.ofReal q * ENNReal.ofReal (c₀ *
      ((groupTable ν E P B K H a q θ R D j Γ).card : ℝ)) =
      ENNReal.ofReal (q * c₀ * ((groupTable ν E P B K H a q θ R D j Γ).card : ℝ)) := by
    intro j Γ
    rw [← ENNReal.ofReal_mul hq.le, mul_assoc]
  have hinner : ∀ j, (∑ Γ ∈ midpointGroupUniverse q a K,
      ENNReal.ofReal (q * c₀ * ((groupTable ν E P B K H a q θ R D j Γ).card : ℝ))) =
      ENNReal.ofReal (∑ Γ ∈ midpointGroupUniverse q a K,
        q * c₀ * ((groupTable ν E P B K H a q θ R D j Γ).card : ℝ)) := by
    intro j
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro Γ _
    exact mul_nonneg (mul_nonneg hq.le hc₀0) (Nat.cast_nonneg _)
  have hinner0 : ∀ j ∈ Finset.range (2 ^ T), 0 ≤ ∑ Γ ∈ midpointGroupUniverse q a K,
      q * c₀ * ((groupTable ν E P B K H a q θ R D j Γ).card : ℝ) := by
    intro j _
    exact Finset.sum_nonneg (fun Γ _ => mul_nonneg (mul_nonneg hq.le hc₀0) (Nat.cast_nonneg _))
  calc
    _ = ∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K,
          ENNReal.ofReal (q * c₀ * ((groupTable ν E P B K H a q θ R D j Γ).card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro Γ _
      exact hterm j Γ
    _ = ENNReal.ofReal (∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K,
          q * c₀ * ((groupTable ν E P B K H a q θ R D j Γ).card : ℝ)) := by
      rw [ENNReal.ofReal_sum_of_nonneg hinner0]
      exact Finset.sum_congr rfl (fun j _ => hinner j)
    _ = ENNReal.ofReal (q * c₀ * ∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K,
          ((groupTable ν E P B K H a q θ R D j Γ).card : ℝ)) := by
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
    _ ≤ ENNReal.ofReal (q * c₀ * (4 * nativeMultiplicity K * (M / (θ * (q / D) ^ 3)))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ENNReal.ofReal (4 * nativeMultiplicity K * C * τ₀ * (D : ℝ) ^ ζ / (σ * θ * q ^ 2) * M) := by
      congr 1
      rw [hc₀]
      field_simp
    _ = ENNReal.ofReal (4 * nativeMultiplicity K * C * τ₀ * (D : ℝ) ^ ζ / (σ * θ * q ^ 2)) *
        (ν.prod volume) E := by
      have hL : 0 ≤ nativeMultiplicity K := by unfold nativeMultiplicity; positivity
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact ENNReal.ofReal_toReal hfin.ne

/-! ## The mass balance of one world -/

/-- The mass balance of one world: given, for every block and native group, the selected mass
and residual of the kernel's charts (exact identity) and the kernel's residual bound, the
world's total incidence mass is at most the selected mass plus the light mass plus `s` plus a
fixed multiple of the total mass. -/
theorem world_mass_balance (ν : Measure Trajectory) [IsProbabilityMeasure ν]
    {E : Set Incidence} (hE : MeasurableSet E) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {B K H a q θ R C τ₀ σ ζ : ℝ} {D T : ℕ}
    (hB : 0 < B) (hK : 0 ≤ K) (hH : 1 ≤ H) (hcoeff : ∀ e, |P.coeff e| ≤ H)
    (hBinv : B⁻¹ ≤ H)
    (hbox : ∀ p ∈ E, (p.1.1 : ℝ) ≤ H ∧ ∀ e, |p.1.2 e| ≤ H)
    (hupper : ∀ᵐ l ∂ν, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖yl l t‖ + ‖vl l‖ ≤ K ∧ |eval (xl l t) P| ≤ K ∧
      |eval (xl l t) (pderiv (3 : Fin 4) P)| ≤ K * B ∧
      |eval (xl l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K * B ^ 2)
    (hlower : ∀ᵐ p ∂(ν.prod volume).restrict E,
      B / K ≤ |eval (xl p.1 p.2) (pderiv (3 : Fin 4) P)|)
    (ha : 0 < a) (ha1 : a ≤ 1) (hqa : q ≤ a) (hθ : 0 < θ) (hD : 0 < D)
    (hmesh : 4131 * H * (3 * H + 1) ^ 2 * (q / D) ≤ a)
    (hσ : 0 < σ) (hC : 0 ≤ C) (hτ₀ : 0 ≤ τ₀) (hqT : q = ((2 : ℝ) ^ T)⁻¹)
    (Sel : ℕ → (Fin 2 → ℤ) × ℤ → ℝ≥0∞) (Res : ℕ → (Fin 2 → ℤ) × ℤ → Set Trajectory)
    (hRes : ∀ j Γ, Res j Γ ⊆ nativeGroup P B K H ((j : ℝ) * q) q a Γ)
    (hid : ∀ j ∈ Finset.range (2 ^ T), ∀ Γ ∈ midpointGroupUniverse q a K,
      Sel j Γ + ENNReal.ofReal q * (ν.prod volume)
        (normalizedEvent (derivativeEvent E P (B / K)) ((j : ℝ) * q) q ∩ (Res j Γ ×ˢ univ)) =
      (ν.prod volume) (selectedEvent E (nativeGroup P B K H ((j : ℝ) * q) q a Γ) P (B / K)
        ((j : ℝ) * q) q))
    (hres : ∀ j ∈ Finset.range (2 ^ T), ∀ Γ ∈ midpointGroupUniverse q a K,
      (ν.prod volume)
        (normalizedEvent (derivativeEvent E P (B / K)) ((j : ℝ) * q) q ∩ (Res j Γ ×ˢ univ)) ≤
      (ν.prod volume) (normalizedEvent (derivativeEvent E P (B / K)) ((j : ℝ) * q) q ∩
          (blockGood ν E B a q θ D j)ᶜ ∩ (Res j Γ ×ˢ univ)) +
        ENNReal.ofReal σ * ν (Res j Γ) +
        ENNReal.ofReal (C * τ₀ * (D : ℝ) ^ ζ / (σ * (D : ℝ) ^ 3) *
          ((groupTable ν E P B K H a q θ R D j Γ).card : ℝ))) :
    (ν.prod volume) E ≤
      (∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K, Sel j Γ) +
      (ν.prod volume) (worldLight ν E B a q θ D) + ENNReal.ofReal σ +
      ENNReal.ofReal (4 * nativeMultiplicity K * C * τ₀ * (D : ℝ) ^ ζ / (σ * θ * q ^ 2)) *
        (ν.prod volume) E := by
  have hq : 0 < q := by rw [hqT]; positivity
  have hH0 : 0 ≤ H := by linarith
  have hblk := eligible_mass_eq_sum_blocks ν hE hunit P hP (B := B) hK hH0 T
  rw [← hqT] at hblk
  set N : ℕ → (Fin 2 → ℤ) × ℤ → ℝ≥0∞ := fun j Γ => (ν.prod volume)
    (normalizedEvent (derivativeEvent E P (B / K)) ((j : ℝ) * q) q ∩ (Res j Γ ×ˢ univ))
  set Lt : ℕ → (Fin 2 → ℤ) × ℤ → ℝ≥0∞ := fun j Γ => (ν.prod volume)
    (normalizedEvent (derivativeEvent E P (B / K)) ((j : ℝ) * q) q ∩
      (blockGood ν E B a q θ D j)ᶜ ∩ (Res j Γ ×ˢ univ))
  set Tb : ℕ → (Fin 2 → ℤ) × ℤ → ℝ≥0∞ := fun j Γ => ENNReal.ofReal
    (C * τ₀ * (D : ℝ) ^ ζ / (σ * (D : ℝ) ^ 3) * ((groupTable ν E P B K H a q θ R D j Γ).card : ℝ))
  have hlight := light_sum_le ν hE P hP (θ := θ) (D := D) hK hH0 hq ha (2 ^ T) Res hRes
  have hdur := duration_sum_le ν P hP hK hH0 hq ha hσ.le hqT Res hRes
  have htab := table_sum_le ν hunit P hP (R := R) (C := C) (τ₀ := τ₀) (σ := σ) (ζ := ζ)
    hB hK hH hcoeff hBinv ha ha1 hqa hθ hD hmesh hσ hC hτ₀ hqT
  calc
    (ν.prod volume) E = ∑ j ∈ Finset.range (2 ^ T), (ν.prod volume)
        (derivativeEvent E P (B / K) ∩
          ({l | nativeEligible P B K H l} ×ˢ Ico ((j : ℝ) * q) ((j : ℝ) * q + q))) := by
      rw [mass_eq_eligible ν hE P hP hK hH0 hbox hupper hlower, hblk]
    _ = ∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K,
        (ν.prod volume) (selectedEvent E (nativeGroup P B K H ((j : ℝ) * q) q a Γ) P (B / K)
          ((j : ℝ) * q) q) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply block_mass_eq_sum_groups ν hE P hP hK hH0 hq ha
      have hj' : (j : ℝ) ≤ (2 : ℝ) ^ T := by
        exact_mod_cast (Finset.mem_range.mp hj).le
      refine ⟨by positivity, ?_⟩
      rw [hqT, ← div_eq_mul_inv, div_le_one (by positivity)]
      exact hj'
    _ = ∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K,
        (Sel j Γ + ENNReal.ofReal q * N j Γ) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro Γ hΓ
      exact (hid j hj Γ hΓ).symm
    _ ≤ ∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K,
        (Sel j Γ + (ENNReal.ofReal q * Lt j Γ +
          ENNReal.ofReal q * (ENNReal.ofReal σ * ν (Res j Γ)) +
          ENNReal.ofReal q * Tb j Γ)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro Γ hΓ
      refine add_le_add le_rfl ?_
      calc
        ENNReal.ofReal q * N j Γ ≤
            ENNReal.ofReal q * (Lt j Γ + ENNReal.ofReal σ * ν (Res j Γ) + Tb j Γ) :=
          mul_le_mul_right (hres j hj Γ hΓ) _
        _ = _ := by rw [mul_add, mul_add]
    _ = (∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K, Sel j Γ) +
        (∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K,
          ENNReal.ofReal q * Lt j Γ) +
        (∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K,
          ENNReal.ofReal q * (ENNReal.ofReal σ * ν (Res j Γ))) +
        (∑ j ∈ Finset.range (2 ^ T), ∑ Γ ∈ midpointGroupUniverse q a K,
          ENNReal.ofReal q * Tb j Γ) := by
      simp only [Finset.sum_add_distrib]
      ring
    _ ≤ _ := by
      gcongr

end

end Submission.Obl.k4_horizon_chart_assembly
