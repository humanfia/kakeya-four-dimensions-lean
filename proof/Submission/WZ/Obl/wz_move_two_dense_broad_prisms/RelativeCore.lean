-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.RelativeCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.ShadingAtoms
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.WeightedPruning

/-! A relative incidence core: lower row masses and a fixed fraction of the
original incidence count at every retained point. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set
open scoped ENNReal
open wz_clustered_cover_volume_gain.Parent

/-- Simultaneous row pruning and pointwise fraction retention. The point cost is
a fraction of incidence mass, rather than a constant times union volume. -/
theorem relative_shading_core {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (Y : ι → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ∞) (cost : ι → ENNReal) (t : ENNReal) :
    ∃ Z : ι → Set X, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (∑ i, μ (Y i)) ≤ (∑ i, μ (Z i)) + (∑ i, cost i) + t * ∑ i, μ (Y i) ∧
      (∀ i, (Z i).Nonempty → cost i ≤ μ (Z i)) ∧
      ∀ p ∈ ⋃ i, Z i,
        t * ({i | p ∈ Y i}.ncard : ENNReal) ≤ ({i | p ∈ Z i}.ncard : ENNReal) := by
  classical
  let allEdges : Finset (ι × Finset ι) := Finset.univ.filter (fun e => e.1 ∈ e.2)
  let w : Finset ι → ENNReal := fun A => μ (shadingAtom Y A)
  obtain ⟨edges, hsub, hmass, hrows, hcols⟩ := weighted_bipartite_core allEdges
    Prod.fst Prod.snd (fun e => w e.2) cost (fun A => t * A.card * w A)
  let clean := edges.filter (fun e => w e.2 ≠ 0)
  let Z := atomicShading Y clean
  have hZμ (i : ι) : μ (Z i) = μ (atomicShading Y edges i) :=
    atomicShading_remove_null_mass μ hY edges i
  have hZY (i : ι) : Z i ⊆ Y i := by
    apply atomicShading_subset
    intro e he
    exact (Finset.mem_filter.mp (hsub (Finset.mem_filter.mp he).1)).2
  have hfull : (∑ e ∈ allEdges, w e.2) = ∑ i, μ (Y i) := by
    rw [← atomicShading_mass μ hY]
    simp only [allEdges, atomicShading_full]
  have hkept : (∑ e ∈ edges, w e.2) = ∑ i, μ (Z i) := by
    simp_rw [hZμ]
    exact (atomicShading_mass μ hY edges).symm
  have hcolcost : (∑ A : Finset ι, t * A.card * w A) = t * ∑ i, μ (Y i) := by
    simp_rw [mul_assoc]
    rw [← hfull, ← Finset.mul_sum]
    congr 1
    simp only [allEdges, Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro A _
    rw [← Finset.sum_filter]
    simp
  refine ⟨Z, fun i => ⟨atomicShading_measurable hY clean i, hZY i⟩,
    by simpa only [hfull, hkept, hcolcost] using hmass, ?_, ?_⟩
  · intro i hi
    obtain ⟨p, hp⟩ := hi
    have hei : (i, shadingPattern Y p) ∈ edges :=
      (Finset.mem_filter.mp (mem_atomicShading.mp hp).2).1
    have hh := hrows i ⟨(i, shadingPattern Y p), Finset.mem_filter.mpr ⟨hei, rfl⟩⟩
    rw [hZμ]
    have hr := atomicShading_row_mass μ hY edges id i
    simpa [Finset.sum_filter] using hh.trans_eq hr.symm
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    let A := shadingPattern Y p
    letI : DecidablePred (fun e : ι × Finset ι => e.2 = A) :=
      fun _ => Classical.propDecidable _
    have hpY : p ∈ ⋃ j, Y j := mem_iUnion.mpr ⟨i, hZY i hi⟩
    have hiClean : (i, A) ∈ clean := (mem_atomicShading.mp hi).2
    have hA0 : w A ≠ 0 := (Finset.mem_filter.mp hiClean).2
    have hAfin : w A ≠ ∞ := shadingAtom_finite_volume μ hfin A
    have hcolumn := hcols A
      ⟨(i, A), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiClean).1, rfl⟩⟩
    have hcolumnSum : (∑ e ∈ edges.filter (fun e => e.2 = A), w e.2) =
        ((edges.filter fun e => e.2 = A).card : ENNReal) * w A := by
      calc
        _ = ∑ _e ∈ edges.filter (fun e => e.2 = A), w A :=
          Finset.sum_congr rfl (fun e he => congrArg w (Finset.mem_filter.mp he).2)
        _ = _ := by simp
    rw [hcolumnSum] at hcolumn
    have hcard : (edges.filter fun e => e.2 = A).card =
        (Finset.univ.filter fun j => p ∈ Z j).card := by
      apply Finset.card_bij (fun e _ => e.1)
      · intro e he
        obtain ⟨heEdges, heA⟩ := Finset.mem_filter.mp he
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply mem_atomicShading.mpr
        refine ⟨hpY, Finset.mem_filter.mpr ⟨?_, hA0⟩⟩
        change (e.1, A) ∈ edges
        simpa only [← heA, Prod.eta] using heEdges
      · intro e he e' he' hee'
        exact Prod.ext hee' ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp he').2.symm)
      · intro j hj
        have hjClean : (j, A) ∈ clean := (mem_atomicShading.mp (Finset.mem_filter.mp hj).2).2
        exact ⟨(j, A), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hjClean).1, rfl⟩, rfl⟩
    have hAcard : A.card = {j | p ∈ Y j}.ncard := by
      simp [A, shadingPattern, Set.ncard_eq_toFinset_card']
    rw [hcard, hAcard] at hcolumn
    have hZcard : (Finset.univ.filter fun j => p ∈ Z j).card = {j | p ∈ Z j}.ncard := by
      have he : {j | p ∈ Z j} = (Finset.univ.filter (fun j => p ∈ Z j) : Set ι) := by
        ext j
        simp
      rw [he, Set.ncard_coe_finset]
    rw [hZcard] at hcolumn
    exact (ENNReal.mul_le_mul_iff_left hA0 hAfin).mp hcolumn

/-- Spending one quarter of the mass on row thresholds retains at least half
of the mass and at least one quarter of the incidences at every surviving point. -/
theorem relative_shading_core_half {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (Y : ι → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ∞) (cost : ι → ENNReal)
    (hbudget : (∑ i, cost i) ≤ (1/4 : ENNReal) * ∑ i, μ (Y i)) :
    ∃ Z : ι → Set X, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1/2 : ENNReal) * (∑ i, μ (Y i)) ≤ ∑ i, μ (Z i) ∧
      (∀ i, (Z i).Nonempty → cost i ≤ μ (Z i)) ∧
      ∀ p ∈ ⋃ i, Z i,
        ({i | p ∈ Y i}.ncard : ℝ) ≤ 4 * ({i | p ∈ Z i}.ncard : ℝ) := by
  have hq : ENNReal.ofReal (1 / 4 : ℝ) = (1/4 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hhf : ENNReal.ofReal (1 / 2 : ℝ) = (1/2 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hqq : (1/4 : ENNReal) + 1/4 = 1/2 := by
    rw [← hq, ← ENNReal.ofReal_add (by norm_num) (by norm_num), ← hhf]
    norm_num
  have hhh : (1/2 : ENNReal) + 1/2 = 1 := by
    rw [← hhf, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  obtain ⟨Z, hZ, hmass, hdense, hcount⟩ := relative_shading_core μ Y hY hfin cost (1/4)
  refine ⟨Z, hZ, ?_, hdense, ?_⟩
  · have hh : (∑ i, μ (Y i)) ≤ (∑ i, μ (Z i)) +
        (1/2 : ENNReal) * ∑ i, μ (Y i) := by
      refine hmass.trans ?_
      calc
        _ ≤ (∑ i, μ (Z i)) + (1/4 : ENNReal) * (∑ i, μ (Y i)) +
            (1/4 : ENNReal) * ∑ i, μ (Y i) :=
          add_le_add (add_le_add le_rfl hbudget) le_rfl
        _ = _ := by rw [add_assoc, ← add_mul, hqq]
    have he : (1/2 : ENNReal) * (∑ i, μ (Y i)) + (1/2 : ENNReal) * (∑ i, μ (Y i)) =
        ∑ i, μ (Y i) := by rw [← add_mul, hhh, one_mul]
    nth_rw 1 [← he] at hh
    exact ENNReal.le_of_add_le_add_right
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr (fun i _ => hfin i))) hh
  · intro p hp
    have hh := ENNReal.toReal_mono (by simp) (hcount p hp)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at hh
    linarith

/-- Relative pruning can be done in every member of a finite family, with one
aggregate budget. The pointwise incidence guarantee holds separately in each
member of the family. -/
theorem relative_shading_core_family {X κ ι : Type*} [MeasurableSpace X]
    [Fintype κ] [Fintype ι] (μ : Measure X) (Y : κ → ι → Set X)
    (hY : ∀ k i, MeasurableSet (Y k i))
    (hfin : ∀ k i, μ (Y k i) ≠ ∞) (cost : κ → ι → ENNReal) (t : ENNReal) :
    ∃ Z : κ → ι → Set X, (∀ k i, MeasurableSet (Z k i) ∧ Z k i ⊆ Y k i) ∧
      (∑ k, ∑ i, μ (Y k i)) ≤ (∑ k, ∑ i, μ (Z k i)) +
        (∑ k, ∑ i, cost k i) + t * ∑ k, ∑ i, μ (Y k i) ∧
      (∀ k i, (Z k i).Nonempty → cost k i ≤ μ (Z k i)) ∧
      ∀ k p, p ∈ ⋃ i, Z k i →
        t * ({i | p ∈ Y k i}.ncard : ENNReal) ≤ ({i | p ∈ Z k i}.ncard : ENNReal) := by
  classical
  choose Z hZ hmass hdense hcount using
    fun k => relative_shading_core μ (Y k) (hY k) (hfin k) (cost k) t
  refine ⟨Z, hZ, ?_, hdense, hcount⟩
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hmass k)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hh

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
