-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TwoScaleUse.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LipschitzOneScale
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.RobustTransversality
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSInterface

/-!
# Using the two-scale interface

Bridges between `fineMult` (from `TSInterface`) and the `through` counts used in the Lipschitz
lemmas, the shading-mass measure `massMeasure` (`massMeasure Y S = ∑ i, vol (Y i ∩ S)`), and the
bound on the coarse labels met by a fine grid cube (`card_act_le`).
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

theorem fineMult_eq_card_through {n : ℕ} (Y : Fin n → Set Space) (p : Space) :
    fineMult Y p = (through Y p).card := by
  classical
  rw [fineMult, ← Set.ncard_coe_finset]
  congr 1; ext i; simp [mem_through]

theorem ncard_fibre_eq {n k : ℕ} (Y : Fin n → Set Space) (a : Fin n → Fin k) (j : Fin k)
    (p : Space) : {i | a i = j ∧ p ∈ Y i}.ncard = ((through Y p).filter fun i => a i = j).card := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1; ext i; simp [mem_through, and_comm]

theorem ncard_cone_eq {n : ℕ} (Y : Fin n → Set Space) (v : Fin n → Space) (u : Space) (β : ℝ)
    (p : Space) : {l | p ∈ Y l ∧ min ‖v l - u‖ ‖v l + u‖ ≤ β}.ncard =
      ((through Y p).filter fun l => min ‖v l - u‖ ‖v l + u‖ ≤ β).card := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1; ext i; simp [mem_through]


/-- The shading-mass measure of a family: the volume weighted by the multiplicity. -/
noncomputable def massMeasure {n : ℕ} (Y : Fin n → Set Space) : Measure Space :=
  volume.withDensity fun p => (fineMult Y p : ℝ≥0∞)

theorem fineMult_eq_sum_indicator {n : ℕ} (Y : Fin n → Set Space) (p : Space) :
    (fineMult Y p : ℝ≥0∞) = ∑ i, (Y i).indicator 1 p := by
  classical
  rw [fineMult_eq_card_through, Finset.card_eq_sum_ones, Nat.cast_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => p ∈ Y i)]
  have h0 : ∑ i ∈ Finset.univ.filter (fun i => p ∉ Y i), (Y i).indicator (1 : Space → ℝ≥0∞) p = 0 :=
    Finset.sum_eq_zero fun i hi => indicator_of_notMem (Finset.mem_filter.1 hi).2 _
  rw [h0, add_zero]
  have hthr : through Y p = Finset.univ.filter (fun i => p ∈ Y i) := by
    ext i; simp [mem_through]
  rw [hthr]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [indicator_of_mem (Finset.mem_filter.1 hi).2]; simp

theorem measurable_fineMult {n : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i)) :
    Measurable fun p => (fineMult Y p : ℝ≥0∞) := by
  have : (fun p => (fineMult Y p : ℝ≥0∞)) = fun p => ∑ i, (Y i).indicator 1 p := by
    funext p; exact fineMult_eq_sum_indicator Y p
  rw [this]
  exact Finset.measurable_sum _ fun i _ => measurable_one.indicator (hY i)

theorem massMeasure_apply {n : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i))
    {S : Set Space} (hS : MeasurableSet S) :
    massMeasure Y S = ∑ i, volume (Y i ∩ S) := by
  rw [massMeasure, withDensity_apply _ hS]
  simp_rw [fineMult_eq_sum_indicator]
  rw [lintegral_finsetSum _ fun i _ => measurable_one.indicator (hY i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_indicator_one (hY i), Measure.restrict_apply (hY i)]

/-- The contracted image of a fine grid cube of side `sL` with `λ sL ≤ s` meets at most `8`
coarse grid cubes of side `s`. -/
theorem exists_coarse_indices {s sL lam : ℝ} (hs : 0 < s) (hsL : 0 < sL) (hlam : 0 < lam)
    (hfit : lam * sL ≤ s) (m : Fin 3 → ℤ) :
    ∃ C : Finset (Fin 3 → ℤ), C.card ≤ 8 ∧
      ∀ p ∈ gridCube sL m, cubeIndex s (lam • p) ∈ C := by
  classical
  set c₀ : Fin 3 → ℤ := fun j => ⌊lam * (sL * m j) / s⌋
  refine ⟨Fintype.piFinset fun j => {c₀ j, c₀ j + 1}, ?_, ?_⟩
  · rw [Fintype.card_piFinset]
    calc ∏ j, ({c₀ j, c₀ j + 1} : Finset ℤ).card ≤ ∏ _j : Fin 3, 2 :=
          Finset.prod_le_prod' fun j _ => Finset.card_le_two
      _ = 8 := by simp
  · intro p hp
    rw [Fintype.mem_piFinset]
    intro j
    obtain ⟨h1, h2⟩ := hp j
    have hpj : (lam • p) j = lam * p j := by simp
    simp only [cubeIndex, hpj, Finset.mem_insert, Finset.mem_singleton]
    have hlo : lam * (sL * m j) / s ≤ lam * p j / s :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hlam.le) hs.le
    have hhi : lam * p j / s < lam * (sL * m j) / s + 1 := by
      rw [div_add_one hs.ne', div_lt_div_iff_of_pos_right hs]
      nlinarith
    have hf1 : c₀ j ≤ ⌊lam * p j / s⌋ := Int.floor_mono hlo
    have hf2 : ⌊lam * p j / s⌋ ≤ c₀ j + 1 := by
      have := Int.floor_le_floor (le_of_lt hhi)
      rw [Int.floor_add_one] at this
      exact this
    omega


theorem corner_mem_gridCube {s : ℝ} (hs : 0 < s) (c : Fin 3 → ℤ) :
    (WithLp.toLp 2 fun j => s * (c j : ℝ) : Space) ∈ gridCube s c := by
  intro j
  simp only [PiLp.toLp_apply]
  constructor
  · exact le_rfl
  · linarith

/-- The number of coarse shadings containing a grid cube is the coarse multiplicity on it. -/
theorem card_labels_le {k : ℕ} {Yt : Fin k → Set Space} {s : ℝ} (hs : 0 < s)
    {M : Fin k → Finset (Fin 3 → ℤ)} (hYt : ∀ j, Yt j = ⋃ m ∈ M j, gridCube s m) {Cc : ℝ}
    (hmult : ∀ q, (fineMult Yt q : ℝ) ≤ Cc) (c : Fin 3 → ℤ) :
    ((Finset.univ.filter fun j => c ∈ M j).card : ℝ) ≤ Cc := by
  classical
  set q : Space := WithLp.toLp 2 fun j => s * (c j : ℝ)
  have hq := corner_mem_gridCube hs c
  refine le_trans (le_of_eq ?_) (hmult q)
  rw [fineMult_eq_card_through]
  congr 2
  ext j
  rw [Finset.mem_filter, mem_through, hYt j, mem_iUnion_gridCube_iff hs,
    cubeIndex_eq_of_mem hs hq]
  simp

/-- The coarse labels of the tubes through a fine cube are at most `8 Cc`. -/
theorem card_act_le {n k : ℕ} {Y' : Fin n → Set Space} {Yt : Fin k → Set Space}
    {a : Fin n → Fin k} {s sL lam : ℝ} (hs : 0 < s) (hsL : 0 < sL) (hlam : 0 < lam)
    (hfit : lam * sL ≤ s) {M : Fin k → Finset (Fin 3 → ℤ)}
    (hYt : ∀ j, Yt j = ⋃ m ∈ M j, gridCube s m) (hcontr : ∀ i, lam • Y' i ⊆ Yt (a i))
    {Cc : ℕ} (hCc : ∀ c, (Finset.univ.filter fun j => c ∈ M j).card ≤ Cc) (m : Fin 3 → ℤ) :
    ∃ Act : Finset (Fin k), Act.card ≤ 8 * Cc ∧
      ∀ p ∈ gridCube sL m, ∀ i ∈ through Y' p, a i ∈ Act := by
  classical
  obtain ⟨C, hCcard, hC⟩ := exists_coarse_indices hs hsL hlam hfit m
  refine ⟨C.biUnion fun c => Finset.univ.filter fun j => c ∈ M j, ?_, ?_⟩
  · calc (C.biUnion fun c => Finset.univ.filter fun j => c ∈ M j).card
        ≤ ∑ c ∈ C, (Finset.univ.filter fun j => c ∈ M j).card := Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ C, Cc := Finset.sum_le_sum fun c _ => hCc c
      _ = C.card * Cc := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 8 * Cc := Nat.mul_le_mul_right _ hCcard
  · intro p hp i hi
    rw [mem_through] at hi
    have h1 := hcontr i (Set.smul_mem_smul_set hi)
    rw [hYt, mem_iUnion_gridCube_iff hs] at h1
    exact Finset.mem_biUnion.2 ⟨_, hC p hp, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
