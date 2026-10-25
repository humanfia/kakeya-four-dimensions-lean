import Mathlib

namespace Submission.Obl.k4_original_observation_atlas_encoding

open MeasureTheory Set Finset
open scoped ENNReal

/-- A finite list maximizing a nonnegative weight vector, with a prescribed size bound. -/
theorem exists_best_list {β : Type*} [Fintype β] (v : β → ℝ≥0∞) (K : ℕ) :
    ∃ S : Finset β, S.card ≤ K ∧
      ∀ T : Finset β, T.card ≤ K → ∑ b ∈ T, v b ≤ ∑ b ∈ S, v b := by
  classical
  let A : Finset (Finset β) := univ.filter (fun S => S.card ≤ K)
  have hA : A.Nonempty := ⟨∅, by simp [A]⟩
  obtain ⟨S, hS, hmax⟩ := A.exists_max_image (fun S => ∑ b ∈ S, v b) hA
  exact ⟨S, (mem_filter.mp hS).2, fun T hT => hmax T (by simp [A, hT])⟩

/-- Success for unnormalized densities and an observable list rule. -/
noncomputable def listMass {X β : Type*} [MeasurableSpace X] [Fintype β]
    (μ : Measure X) (p : β → X → ℝ≥0∞) (L : X → Finset β) : ℝ≥0∞ :=
  ∑ b, ∫⁻ x, {x | b ∈ L x}.indicator (p b) x ∂μ

theorem listMass_eq_lintegral {X β : Type*} [MeasurableSpace X] [Fintype β]
    (μ : Measure X) (p : β → X → ℝ≥0∞) (hp : ∀ b, Measurable (p b))
    (L : X → Finset β) (hL : ∀ b, MeasurableSet {x | b ∈ L x}) :
    listMass μ p L = ∫⁻ x, ∑ b ∈ L x, p b x ∂μ := by
  classical
  rw [listMass, ← lintegral_finsetSum _ (fun b _ => (hp b).indicator (hL b))]
  apply lintegral_congr
  intro x
  simp only [indicator_apply, mem_ofPred_eq]
  simpa using (sum_filter (s := univ) (fun b => b ∈ L x) (fun b => p b x)).symm

theorem listMass_change {X β : Type*} [MeasurableSpace X] [Fintype β]
    (μ : Measure X) (p q : β → X → ℝ≥0∞)
    (hp : ∀ b, Measurable (p b)) (hq : ∀ b, Measurable (q b))
    (L : X → Finset β) (hL : ∀ b, MeasurableSet {x | b ∈ L x}) :
    listMass μ p L ≤ listMass μ q L +
      ∑ b, ∫⁻ x, ((p b x - q b x) + (q b x - p b x)) ∂μ := by
  classical
  rw [listMass, listMass, ← sum_add_distrib]
  apply sum_le_sum
  intro b _
  calc
    _ ≤ ∫⁻ x, {x | b ∈ L x}.indicator (q b) x +
        ((p b x - q b x) + (q b x - p b x)) ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : b ∈ L x
      · simp only [indicator_apply, mem_ofPred_eq, hx, ↓reduceIte]
        calc
          p b x ≤ q b x + (p b x - q b x) := le_add_tsub
          _ ≤ q b x + ((p b x - q b x) + (q b x - p b x)) :=
            add_le_add le_rfl le_self_add
      · simp only [indicator_apply, mem_ofPred_eq, hx, ↓reduceIte]
        exact zero_le
    _ = _ := lintegral_add_left ((hq b).indicator (hL b)) _

/-- A list on a countable observation partition, chosen by finite maximization, retains
the success of any measurable list after two charges of the density approximation error. -/
theorem recover_cell_lists {X C β : Type*} [MeasurableSpace X]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C] [Fintype β]
    (μ : Measure X) (p q : β → X → ℝ≥0∞)
    (hp : ∀ b, Measurable (p b)) (hq : ∀ b, Measurable (q b))
    (code : X → C) (hcode : Measurable code) (corner : C → X)
    (hcorner : ∀ c, code (corner c) = c)
    (hconstant : ∀ b x y, code x = code y → q b x = q b y)
    (K : ℕ) (L : X → Finset β) (hL : ∀ b, MeasurableSet {x | b ∈ L x})
    (hLK : ∀ x, (L x).card ≤ K) :
    ∃ table : C → Finset β, (∀ c, (table c).card ≤ K) ∧
      listMass μ p L ≤ listMass μ p (fun x => table (code x)) +
        2 * ∑ b, ∫⁻ x, ((p b x - q b x) + (q b x - p b x)) ∂μ := by
  classical
  choose table htable hmax using fun c => exists_best_list (fun b => q b (corner c)) K
  have hmeas (b : β) : MeasurableSet {x | b ∈ table (code x)} :=
    hcode ((Set.to_countable {c | b ∈ table c}).measurableSet)
  have hqtable : listMass μ q L ≤ listMass μ q (fun x => table (code x)) := by
    rw [listMass_eq_lintegral μ q hq L hL,
      listMass_eq_lintegral μ q hq _ hmeas]
    apply lintegral_mono
    intro x
    have hvalues (b : β) : q b (corner (code x)) = q b x :=
      hconstant b _ _ (hcorner _)
    simpa only [hvalues] using hmax (code x) (L x) (hLK x)
  refine ⟨table, htable, ?_⟩
  have hfirst := listMass_change μ p q hp hq L hL
  have hlast := listMass_change μ q p hq hp _ hmeas
  have heq : (∑ b, ∫⁻ x, ((q b x - p b x) + (p b x - q b x)) ∂μ) =
      ∑ b, ∫⁻ x, ((p b x - q b x) + (q b x - p b x)) ∂μ := by
    simp only [add_comm]
  rw [heq] at hlast
  calc
    listMass μ p L ≤ _ := hfirst
    _ ≤ (listMass μ p (fun x => table (code x)) +
        ∑ b, ∫⁻ x, ((p b x - q b x) + (q b x - p b x)) ∂μ) +
        ∑ b, ∫⁻ x, ((p b x - q b x) + (q b x - p b x)) ∂μ :=
      add_le_add (hqtable.trans hlast) le_rfl
    _ = _ := by rw [two_mul, add_assoc]

theorem weighted_filtered_listMass {X W β : Type*} [MeasurableSpace X]
    [Fintype W] [DecidableEq W] [Fintype β] (μ : Measure X) (v : W → ℝ≥0∞) (γ : β → W)
    (p : β → X → ℝ≥0∞) (L : W → X → Finset β) :
    (∑ w, v w * listMass μ (fun b x => if γ b = w then p b x else 0) (L w)) =
      ∑ b, v (γ b) * ∫⁻ x, {x | b ∈ L (γ b) x}.indicator (p b) x ∂μ := by
  classical
  have hterm (w : W) (b : β) :
      (∫⁻ x, {x | b ∈ L w x}.indicator (fun x => if γ b = w then p b x else 0) x ∂μ) =
        if γ b = w then ∫⁻ x, {x | b ∈ L w x}.indicator (p b) x ∂μ else 0 := by
    by_cases h : γ b = w <;> simp [h]
  simp_rw [listMass, hterm, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  simp

theorem recover_world_lists {X C W β : Type*} [MeasurableSpace X]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]
    [Fintype W] [Fintype β]
    (μ : Measure X) (p q : β → X → ℝ≥0∞)
    (hp : ∀ b, Measurable (p b)) (hq : ∀ b, Measurable (q b))
    (v : W → ℝ≥0∞) (hv : ∑ w, v w = 1) (γ : β → W)
    (code : X → C) (hcode : Measurable code) (corner : C → X)
    (hcorner : ∀ c, code (corner c) = c)
    (hconstant : ∀ b x y, code x = code y → q b x = q b y)
    (K : ℕ) (L : W → X → Finset β)
    (hL : ∀ w b, MeasurableSet {x | b ∈ L w x}) (hLK : ∀ w x, (L w x).card ≤ K) :
    ∃ table : W → C → Finset β, (∀ w c, (table w c).card ≤ K) ∧
      (∑ b, v (γ b) * ∫⁻ x, {x | b ∈ L (γ b) x}.indicator (p b) x ∂μ) ≤
        (∑ b, v (γ b) * ∫⁻ x, {x | b ∈ table (γ b) (code x)}.indicator (p b) x ∂μ) +
          2 * ∑ b, ∫⁻ x, ((p b x - q b x) + (q b x - p b x)) ∂μ := by
  classical
  let pw : W → β → X → ℝ≥0∞ := fun w b x => if γ b = w then p b x else 0
  let qw : W → β → X → ℝ≥0∞ := fun w b x => if γ b = w then q b x else 0
  have hpw (w : W) (b : β) : Measurable (pw w b) := by
    by_cases h : γ b = w <;> simp only [pw, h, ↓reduceIte] <;> fun_prop
  have hqw (w : W) (b : β) : Measurable (qw w b) := by
    by_cases h : γ b = w <;> simp only [qw, h, ↓reduceIte] <;> fun_prop
  have hconst (w : W) : ∀ b x y, code x = code y → qw w b x = qw w b y := by
    intro b x y hxy
    by_cases h : γ b = w <;> simp only [qw, h, ↓reduceIte]
    exact hconstant b x y hxy
  choose table ht hs using fun w => recover_cell_lists μ (pw w) (qw w)
    (hpw w) (hqw w) code hcode corner hcorner (hconst w) K (L w) (hL w) (hLK w)
  let e := ∑ b, ∫⁻ x, ((p b x - q b x) + (q b x - p b x)) ∂μ
  have he (w : W) :
      (∑ b, ∫⁻ x, ((pw w b x - qw w b x) + (qw w b x - pw w b x)) ∂μ) ≤ e := by
    apply sum_le_sum
    intro b _
    by_cases h : γ b = w
    · simp only [pw, qw, h, ↓reduceIte, le_refl]
    · simp only [pw, qw, h, ↓reduceIte, tsub_self, add_zero, lintegral_zero]
      exact zero_le
  refine ⟨table, ht, ?_⟩
  rw [← weighted_filtered_listMass μ v γ p L,
    ← weighted_filtered_listMass μ v γ p (fun w x => table w (code x))]
  change (∑ w, v w * listMass μ (pw w) (L w)) ≤
    (∑ w, v w * listMass μ (pw w) (fun x => table w (code x))) + 2 * e
  calc
    _ ≤ ∑ w, v w * (listMass μ (pw w) (fun x => table w (code x)) + 2 * e) := by
      apply sum_le_sum
      intro w _
      have hs' : listMass μ (pw w) (L w) ≤
          listMass μ (pw w) (fun x => table w (code x)) + 2 * e :=
        (hs w).trans (add_le_add le_rfl (by gcongr; exact he w))
      gcongr
    _ = _ := by simp_rw [mul_add]; rw [sum_add_distrib, ← sum_mul, hv, one_mul]

end Submission.Obl.k4_original_observation_atlas_encoding
