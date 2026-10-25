/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- The actual path index of an earlier control in the current block. -/
def previousBlockIndex (n : ℕ) (i : Fin (n % 3)) : Finset.Iic n :=
  ⟨n - n % 3 + (i.1+1), by
    have hi := i.2
    have hm := Nat.mod_le n 3
    simp only [Finset.mem_Iic]
    omega⟩

/-- Controls already drawn in the current block of three switches. -/
def previousBlockControls {X C : Type*} (control : X → C) (n : ℕ)
    (h : (i : Finset.Iic n) → X) (i : Fin (n % 3)) : C :=
  control (h (previousBlockIndex n i))

theorem previousBlockControls_measurable {X C : Type*}
    [MeasurableSpace X] [MeasurableSpace C]
    (control : X → C) (hcontrol : Measurable control) (n : ℕ) :
    Measurable (previousBlockControls control n) := by
  exact measurable_pi_iff.mpr (fun i =>
    hcontrol.comp (measurable_pi_apply (previousBlockIndex n i)))

noncomputable def historyBasisPencil {X C : Type*} (control : X → C)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (n : ℕ) :
    Set ((((i : Finset.Iic n) → X)) × C) :=
  {z | Metric.infDist (v z.2)
    (Submodule.span ℝ (Set.range (fun i => v (previousBlockControls control n z.1 i))) :
      Set (EuclideanSpace ℝ (Fin 3))) < r}

theorem historyBasisPencil_measurable {X C : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (control : X → C) (hcontrol : Measurable control)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (n : ℕ) :
    MeasurableSet (historyBasisPencil control v r n) := by
  let B : Set ((Fin (n % 3) → C) × C) := {z | Metric.infDist (v z.2)
    (Submodule.span ℝ (Set.range (fun i => v (z.1 i))) : Set (EuclideanSpace ℝ (Fin 3))) < r}
  have hB : MeasurableSet B := (Set.to_countable B).measurableSet
  let f : ((((i : Finset.Iic n) → X)) × C) → ((Fin (n % 3) → C) × C) :=
    fun z => (previousBlockControls control n z.1,z.2)
  have hf : Measurable f :=
    ((previousBlockControls_measurable control hcontrol n).comp
      (measurable_fst : Measurable (fun z : (((i : Finset.Iic n) → X)) × C => z.1))).prodMk
        measurable_snd
  change MeasurableSet (f ⁻¹' B)
  exact hB.preimage hf

theorem historyBasisPencil_span_rank_lt {X C : Type*} (control : X → C)
    (v : C → EuclideanSpace ℝ (Fin 3)) (n : ℕ) (h : (i : Finset.Iic n) → X) :
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i => v (previousBlockControls control n h i)))) < 3 := by
  have hm := finrank_range_le_card (R := ℝ)
    (fun i => v (previousBlockControls control n h i))
  have hcard : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i => v (previousBlockControls control n h i)))) ≤ n % 3 := by
    simpa only [Set.finrank, Fintype.card_fin] using hm
  exact hcard.trans_lt (Nat.mod_lt n (by decide))

/-- Retain a long next line outside the pencil of the preceding controls
in its block of three. These are the actual unnormalized decisions. -/
noncomputable def basisPencilRetention {X C : Type*} (control : X → C)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (Long : Set X) (n : ℕ)
    (h : (i : Finset.Iic n) → X) (y : X) : ENNReal :=
  {z : (((i : Finset.Iic n) → X)) × X |
    z.2 ∈ Long ∧ (z.1,control z.2) ∉ historyBasisPencil control v r n}.indicator
      (fun _ => 1) (h,y)

theorem basisPencilRetention_measurable {X C : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (control : X → C) (hcontrol : Measurable control)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (Long : Set X)
    (hLong : MeasurableSet Long) (n : ℕ) :
    Measurable (Function.uncurry (basisPencilRetention control v r Long n)) := by
  have hP := (historyBasisPencil_measurable control hcontrol v r n).preimage
    (measurable_fst.prodMk (hcontrol.comp measurable_snd))
  exact measurable_const.indicator ((hLong.preimage measurable_snd).inter hP.compl)

theorem basisPencilRetention_ne_zero_iff {X C : Type*} (control : X → C)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (Long : Set X)
    (n : ℕ) (h : (i : Finset.Iic n) → X) (y : X) :
    basisPencilRetention control v r Long n h y ≠ 0 ↔
      y ∈ Long ∧ (h,control y) ∉ historyBasisPencil control v r n := by
  classical
  simp only [basisPencilRetention, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem basisPencilRetention_le_long {X C : Type*} (control : X → C)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (Long : Set X)
    (n : ℕ) (h : (i : Finset.Iic n) → X) (y : X) :
    basisPencilRetention control v r Long n h y ≤ Long.indicator (fun _ => 1) y := by
  classical
  by_cases hy : y ∈ Long <;>
    by_cases hp : (h,control y) ∈ historyBasisPencil control v r n <;>
      simp [basisPencilRetention, hy, hp]

theorem basisPencilRetention_defect {X C : Type*} (control : X → C)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (Long : Set X)
    (n : ℕ) (h : (i : Finset.Iic n) → X) (y : X) :
    1 - basisPencilRetention control v r Long n h y ≤
      Longᶜ.indicator (fun _ => 1) y +
        (historyBasisPencil control v r n).indicator (fun _ => 1) (h,control y) := by
  classical
  by_cases hy : y ∈ Long <;>
    by_cases hp : (h,control y) ∈ historyBasisPencil control v r n <;>
      simp [basisPencilRetention, hy, hp] <;> norm_num

end Submission.Lib.K4PolynomialNorming


namespace Submission.Lib.K4PolynomialNorming

theorem basisPencilRetention_le_one {X C : Type*} (control : X → C)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (Long : Set X)
    (n : ℕ) (h : (i : Finset.Iic n) → X) (y : X) :
    basisPencilRetention control v r Long n h y ≤ 1 := by
  classical
  apply (basisPencilRetention_le_long control v r Long n h y).trans
  by_cases hy : y ∈ Long <;> simp [hy]

/-- The preceding controls in a block of three are exactly the earlier
members of that block's actual direction triple. -/
theorem previousBlockControls_range {X C Y : Type*}
    (control : X → C) (v : C → Y) (x : ℕ → X) (b : ℕ) (j : Fin 3) :
    Set.range (fun i => v (previousBlockControls control (3*b+j.1)
      (Preorder.frestrictLe (3*b+j.1) x) i)) =
        (fun i : Fin 3 => v (control (x (3*b+i.1+1)))) '' Set.Iio j := by
  have hj := j.2
  have hmod : (3*b+j.1) % 3 = j.1 := by omega
  ext u
  constructor
  · rintro ⟨i,hi⟩
    have hi' : i.1 < j.1 := by simpa only [hmod] using i.2
    let k : Fin 3 := ⟨i.1,hi'.trans hj⟩
    refine ⟨k,hi',?_⟩
    change v (control (x ((3*b+j.1) - (3*b+j.1)%3 + (i.1+1)))) = u at hi
    have hidx : (3*b+j.1) - (3*b+j.1)%3 + (i.1+1) = 3*b+i.1+1 := by omega
    rw [hidx] at hi
    exact hi
  · rintro ⟨k,hkj,hk⟩
    have hk' : k.1 < (3*b+j.1)%3 := by
      rw [hmod]
      exact hkj
    let i : Fin ((3*b+j.1)%3) := ⟨k.1,hk'⟩
    refine ⟨i,?_⟩
    change v (control (x ((3*b+j.1) - (3*b+j.1)%3 + (i.1+1)))) = u
    have hidx : (3*b+j.1) - (3*b+j.1)%3 + (i.1+1) = 3*b+k.1+1 := by
      dsimp only [i]
      omega
    rw [hidx]
    exact hk

theorem block_pencil_avoidance_distances {X C : Type*}
    (control : X → C) (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ)
    (x : ℕ → X) (b : ℕ)
    (havoid : ∀ j : Fin 3,
      (Preorder.frestrictLe (3*b+j.1) x,control (x (3*b+j.1+1))) ∉
        historyBasisPencil control v r (3*b+j.1)) :
    ∀ j : Fin 3, r ≤ Metric.infDist (v (control (x (3*b+j.1+1))))
      (Submodule.span ℝ
        ((fun i : Fin 3 => v (control (x (3*b+i.1+1)))) '' Set.Iio j) :
          Set (EuclideanSpace ℝ (Fin 3))) := by
  intro j
  have h := havoid j
  change ¬Metric.infDist (v (control (x (3*b+j.1+1))))
    (Submodule.span ℝ (Set.range (fun i => v (previousBlockControls control (3*b+j.1)
      (Preorder.frestrictLe (3*b+j.1) x) i))) : Set (EuclideanSpace ℝ (Fin 3))) < r at h
  have hr := le_of_not_gt h
  rw [previousBlockControls_range control v x b j] at hr
  exact hr

/-- Six concrete retained decisions give two separated direction triples
and six long actual next states. -/
theorem six_basis_retention_certificates {X C : Type*}
    (control : X → C) (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (Long : Set X)
    (x : ℕ → X)
    (hret : ∀ k < 6, basisPencilRetention control v r Long k
      (Preorder.frestrictLe k x) (x (k+1)) ≠ 0) :
    (∀ k < 6, x (k+1) ∈ Long) ∧
      (∀ b : Fin 2, ∀ j : Fin 3, r ≤ Metric.infDist (v (control (x (3*b.1+j.1+1))))
        (Submodule.span ℝ
          ((fun i : Fin 3 => v (control (x (3*b.1+i.1+1)))) '' Set.Iio j) :
            Set (EuclideanSpace ℝ (Fin 3)))) := by
  constructor
  · intro k hk
    exact ((basisPencilRetention_ne_zero_iff control v r Long k
      (Preorder.frestrictLe k x) (x (k+1))).mp (hret k hk)).1
  · intro b
    apply block_pencil_avoidance_distances control v r x b.1
    intro j
    have hk : 3*b.1+j.1 < 6 := by have hb := b.2; have hj := j.2; omega
    exact ((basisPencilRetention_ne_zero_iff control v r Long (3*b.1+j.1)
      (Preorder.frestrictLe (3*b.1+j.1) x) (x (3*b.1+j.1+1))).mp
        (hret (3*b.1+j.1) hk)).2

end Submission.Lib.K4PolynomialNorming

