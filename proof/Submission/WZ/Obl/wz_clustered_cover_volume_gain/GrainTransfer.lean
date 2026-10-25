-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.GrainTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

def assignedFiber {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    (k : Fin N) : Set Space := {p | ∃ i, f i = k ∧ p ∈ Y i}

def fiberBodyCount {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    (k : Fin N) (p : Space) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => f i = k), (Y i).indicator (fun _ => (1 : ℝ)) p

theorem measurable_assignedFiber {n N : ℕ} (f : Fin n → Fin N)
    {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i)) (k : Fin N) :
    MeasurableSet (assignedFiber f Y k) := by
  have he : assignedFiber f Y k = ⋃ i ∈ Finset.univ.filter (fun i => f i = k), Y i := by
    ext p
    simp [assignedFiber]
  rw [he]
  exact Finset.measurableSet_biUnion _ (fun i _ => hY i)

theorem sum_fiberBodyCount {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space) (p : Space) :
    ∑ k, fiberBodyCount f Y k p = bodyCount Y p := by
  rw [bodyCount_eq_sum]
  exact Finset.sum_fiberwise Finset.univ f (fun i => (Y i).indicator (fun _ => (1 : ℝ)) p)

theorem fiberBodyCount_eq_ncard {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    (k : Fin N) (p : Space) :
    fiberBodyCount f Y k p = ({i : Fin n | f i = k ∧ p ∈ Y i}.ncard : ℝ) := by
  classical
  simp [fiberBodyCount, ncard_eq_toFinset_card', Set.indicator, Finset.sum_boole,
    Finset.filter_filter]

/-- Disjoint grain shadings in one fibre make the assignment injective at every point. -/
theorem active_fiber_ncard {L N : ℕ} (γ : Fin L → Fin N) (H : Fin L → Set Space)
    (hdisj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H i) (H j))
    (R : Fin N → Prop) (p : Space) :
    {k : Fin N | R k ∧ p ∈ assignedFiber γ H k}.ncard =
      {j : Fin L | R (γ j) ∧ p ∈ H j}.ncard := by
  have hinj : Set.InjOn γ {j : Fin L | R (γ j) ∧ p ∈ H j} := by
    intro i hi j hj he
    by_contra hne
    exact Set.disjoint_left.mp (hdisj i j hne he) hi.2 hj.2
  have he : γ '' {j : Fin L | R (γ j) ∧ p ∈ H j} =
      {k : Fin N | R k ∧ p ∈ assignedFiber γ H k} := by
    ext k
    constructor
    · rintro ⟨j, ⟨hjR, hjH⟩, rfl⟩
      exact ⟨hjR, j, rfl, hjH⟩
    · rintro ⟨hkR, j, hjk, hjH⟩
      exact ⟨j, ⟨hjk ▸ hkR, hjH⟩, hjk⟩
  rw [← he, hinj.ncard_image]

theorem bodyCount_assignedFiber {L N : ℕ} (γ : Fin L → Fin N) (H : Fin L → Set Space)
    (hdisj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H i) (H j)) (p : Space) :
    bodyCount (assignedFiber γ H) p = bodyCount H p := by
  have h := congrArg (fun k : ℕ => (k : ℝ)) (active_fiber_ncard γ H hdisj (fun _ => True) p)
  simpa only [bodyCount, true_and] using h

/-- Intersecting every fine shading with a set chosen in its fibre preserves the
whole original fibre count at retained points. -/
theorem fiberBodyCount_restrict {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    (C : Fin N → Set Space) (k : Fin N) (p : Space) :
    fiberBodyCount f (fun i => Y i ∩ C (f i)) k p =
      (C k).indicator (fun _ => fiberBodyCount f Y k p) p := by
  classical
  by_cases hp : p ∈ C k
  · rw [indicator_of_mem hp]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : f i = k := (Finset.mem_filter.mp hi).2
    by_cases hpi : p ∈ Y i <;> simp [hik, hp, hpi]
  · rw [indicator_of_notMem hp]
    apply Finset.sum_eq_zero
    intro i hi
    have hik : f i = k := (Finset.mem_filter.mp hi).2
    exact indicator_of_notMem (fun h => hp (hik ▸ h.2)) _

theorem ofReal_bodyCount {n : ℕ} (Y : Fin n → Set Space) (p : Space) :
    ENNReal.ofReal (bodyCount Y p) = ∑ i, (Y i).indicator (fun _ => (1 : ENNReal)) p := by
  classical
  simp [bodyCount, ncard_eq_toFinset_card', Set.indicator, Finset.sum_boole]

theorem lintegral_bodyCount {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) :
    (∫⁻ p, ENNReal.ofReal (bodyCount Y p)) = ∑ i, volume (Y i) := by
  simp_rw [ofReal_bodyCount]
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hY i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_indicator_const (hY i), one_mul]

/-- Integrating a comparison of pointwise finite counts compares total shading masses. -/
theorem body_mass_le_of_count {n k : ℕ} {Y : Fin n → Set Space} {Z : Fin k → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) (hZ : ∀ i, MeasurableSet (Z i))
    {m : ℝ} (hm : 0 ≤ m) (hcount : ∀ p, m * bodyCount Y p ≤ bodyCount Z p) :
    ENNReal.ofReal m * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) := by
  rw [← lintegral_bodyCount hY, ← lintegral_bodyCount hZ,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro p
  dsimp only
  rw [← ENNReal.ofReal_mul hm]
  exact ENNReal.ofReal_le_ofReal (hcount p)

theorem body_mass_le_mul_of_count {n k : ℕ} {Y : Fin n → Set Space} {Z : Fin k → Set Space}
    (hY : ∀ i, MeasurableSet (Y i)) (hZ : ∀ i, MeasurableSet (Z i))
    {m : ℝ} (hm : 0 ≤ m) (hcount : ∀ p, bodyCount Y p ≤ m * bodyCount Z p) :
    ∑ i, volume (Y i) ≤ ENNReal.ofReal m * ∑ i, volume (Z i) := by
  rw [← lintegral_bodyCount hY, ← lintegral_bodyCount hZ,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro p
  dsimp only
  rw [← ENNReal.ofReal_mul hm]
  exact ENNReal.ofReal_le_ofReal (hcount p)

theorem sum_indicator_bodyCount {N : ℕ} (C : Fin N → Set Space) (p : Space) (m : ℝ) :
    (∑ k, (C k).indicator (fun _ => m) p) = m * bodyCount C p := by
  classical
  rw [bodyCount_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hp : p ∈ C k <;> simp [hp]

theorem restrict_fiber_count_bounds {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    (C : Fin N → Set Space) {m M : ℝ}
    (hbound : ∀ k p, p ∈ C k → m ≤ fiberBodyCount f Y k p ∧ fiberBodyCount f Y k p ≤ M)
    (p : Space) :
    m * bodyCount C p ≤ bodyCount (fun i => Y i ∩ C (f i)) p ∧
      bodyCount (fun i => Y i ∩ C (f i)) p ≤ M * bodyCount C p := by
  classical
  rw [← sum_fiberBodyCount f (fun i => Y i ∩ C (f i)) p,
    ← sum_indicator_bodyCount C p m, ← sum_indicator_bodyCount C p M]
  constructor
  · apply Finset.sum_le_sum
    intro k _
    rw [fiberBodyCount_restrict]
    by_cases hp : p ∈ C k
    · simpa only [indicator_of_mem hp] using (hbound k p hp).1
    · simp only [indicator_of_notMem hp, le_refl]
  · apply Finset.sum_le_sum
    intro k _
    rw [fiberBodyCount_restrict]
    by_cases hp : p ∈ C k
    · simpa only [indicator_of_mem hp] using (hbound k p hp).2
    · simp only [indicator_of_notMem hp, le_refl]

theorem assignedFiber_mono {n N : ℕ} (f : Fin n → Fin N) {Y Z : Fin n → Set Space}
    (hYZ : ∀ i, Y i ⊆ Z i) (k : Fin N) : assignedFiber f Y k ⊆ assignedFiber f Z k := by
  rintro p ⟨i, hik, hi⟩
  exact ⟨i, hik, hYZ i hi⟩

theorem assignedFiber_restrict {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    (C : Fin N → Set Space) (hCY : ∀ k, C k ⊆ assignedFiber f Y k) (k : Fin N) :
    assignedFiber f (fun i => Y i ∩ C (f i)) k = C k := by
  ext p
  constructor
  · rintro ⟨i, hik, _, hiC⟩
    exact hik ▸ hiC
  · intro hp
    obtain ⟨i, hik, hi⟩ := hCY k hp
    exact ⟨i, hik, hi, hik.symm ▸ hp⟩

/-- Refining disjoint grain shadings induces a refinement of the original fine
shadings. A common fine multiplicity level loses at most a factor two in mass. -/
theorem grain_refinement_transfer {n N L : ℕ} (f : Fin n → Fin N) (γ : Fin L → Fin N)
    (Z : Fin n → Set Space) (H H' : Fin L → Set Space) {m t : ℝ}
    (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hZm : ∀ i, MeasurableSet (Z i)) (hHm : ∀ j, MeasurableSet (H j))
    (hH'm : ∀ j, MeasurableSet (H' j)) (hH'H : ∀ j, H' j ⊆ H j)
    (hdisj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H i) (H j))
    (heq : ∀ k, assignedFiber γ H k = assignedFiber f Z k)
    (hlevel : ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m)
    (hretain : ENNReal.ofReal t * ∑ j, volume (H j) ≤ ∑ j, volume (H' j)) :
    ∃ W : Fin n → Set Space, (∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i) ∧
      ENNReal.ofReal (t / 2) * ∑ i, volume (Z i) ≤ ∑ i, volume (W i) ∧
      ∀ k, assignedFiber f W k = assignedFiber γ H' k := by
  let C := assignedFiber γ H
  let C' := assignedFiber γ H'
  let W : Fin n → Set Space := fun i => Z i ∩ C' (f i)
  have hCm : ∀ k, MeasurableSet (C k) := measurable_assignedFiber γ hHm
  have hC'm : ∀ k, MeasurableSet (C' k) := measurable_assignedFiber γ hH'm
  have hWm : ∀ i, MeasurableSet (W i) := fun i => (hZm i).inter (hC'm (f i))
  have hC'Z : ∀ k, C' k ⊆ assignedFiber f Z k := by
    intro k
    exact (assignedFiber_mono γ hH'H k).trans (heq k).subset
  have hrestr : (fun i => Z i ∩ C (f i)) = Z := by
    funext i
    apply inter_eq_left.mpr
    intro p hp
    rw [show C (f i) = assignedFiber f Z (f i) from heq (f i)]
    exact ⟨i, rfl, hp⟩
  have hH'disj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H' i) (H' j) :=
    fun i j hij hγ => (hdisj i j hij hγ).mono (hH'H i) (hH'H j)
  have hOrig : ∀ p, bodyCount Z p ≤ (2 * m) * bodyCount H p := by
    intro p
    have hh := (restrict_fiber_count_bounds f Z C
      (fun k p hp => hlevel k p ((heq k).subset hp)) p).2
    rw [hrestr] at hh
    simpa only [C, bodyCount_assignedFiber γ H hdisj p] using hh
  have hNew : ∀ p, m * bodyCount H' p ≤ bodyCount W p := by
    intro p
    have hh := (restrict_fiber_count_bounds f Z C'
      (fun k p hp => hlevel k p (hC'Z k hp)) p).1
    simpa only [C', bodyCount_assignedFiber γ H' hH'disj p] using hh
  have hOrigMass := body_mass_le_mul_of_count hZm hHm (by positivity : 0 ≤ 2 * m) hOrig
  have hNewMass := body_mass_le_of_count hH'm hWm hm hNew
  refine ⟨W, fun i => ⟨hWm i, inter_subset_left⟩, ?_, assignedFiber_restrict f Z C' hC'Z⟩
  calc
    _ ≤ ENNReal.ofReal (t / 2) * (ENNReal.ofReal (2 * m) * ∑ j, volume (H j)) :=
      mul_le_mul' le_rfl hOrigMass
    _ = ENNReal.ofReal m * (ENNReal.ofReal t * ∑ j, volume (H j)) := by
      rw [← mul_assoc (ENNReal.ofReal (t / 2)) (ENNReal.ofReal (2 * m)),
        ← mul_assoc (ENNReal.ofReal m) (ENNReal.ofReal t),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hm]
      congr 2
      ring
    _ ≤ ENNReal.ofReal m * ∑ j, volume (H' j) := mul_le_mul' le_rfl hretain
    _ ≤ _ := hNewMass

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
