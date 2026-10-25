import Submission.Obl.k4_horizontal_strict_parameter_step.AffineUpgrade
import Submission.Lib.K4FinitePlankAtlases.Assignments
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/JetFamilies.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set MeasureTheory
open Submission.Lib.K4FinitePlankAtlases

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The two fixed-time coordinates supplied by a normalized first-jet cover. -/
def jetCoordinates (r : α → Fin 2 → ℝ) (p q : α → ℝ)
    (D p₀ q₀ t₀ : ℝ) (F A : Fin 2 → ℝ) (l : α) : Fin 2 → ℝ :=
  ![r l 0 + t₀ * r l 1 - F 0 * ((p l - p₀) / D) - F 1 * ((q l - q₀) / D),
    r l 1 - A 0 * ((p l - p₀) / D) - A 1 * ((q l - q₀) / D)]

def jetCode (r : α → Fin 2 → ℝ) (p q : α → ℝ)
    (D p₀ q₀ t₀ w : ℝ) (F A : Fin 2 → ℝ) (l : α) : ℤ × ℤ :=
  (⌊jetCoordinates r p q D p₀ q₀ t₀ F A l 0 / w⌋,
    ⌊jetCoordinates r p q D p₀ q₀ t₀ F A l 1 / w⌋)

theorem measurable_jetCode {r : α → Fin 2 → ℝ} {p q : α → ℝ}
    (hr : Measurable r) (hp : Measurable p) (hq : Measurable q)
    (D p₀ q₀ t₀ w : ℝ) (F A : Fin 2 → ℝ) :
    Measurable (jetCode r p q D p₀ q₀ t₀ w F A) := by
  have hr₀ := (measurable_pi_apply (0 : Fin 2)).comp hr
  have hr₁ := (measurable_pi_apply (1 : Fin 2)).comp hr
  have hp' := (hp.sub_const p₀).div_const D
  have hq' := (hq.sub_const q₀).div_const D
  have hvalue := ((hr₀.add (hr₁.const_mul t₀)).sub
    (hp'.const_mul (F 0))).sub (hq'.const_mul (F 1))
  have hslope := (hr₁.sub (hp'.const_mul (A 0))).sub (hq'.const_mul (A 1))
  exact (Int.measurable_floor.comp (hvalue.div_const w)).prodMk
    (Int.measurable_floor.comp (hslope.div_const w))

/-- A finite first-jet bin list gives measurable, disjoint full-time predictor assignments
on the unchanged old parameter square. No density or prior is changed in this construction. -/
theorem jet_cover_to_family {n : ℕ} {C : Set α} (hC : MeasurableSet C)
    {r : α → Fin 2 → ℝ} {p q : α → ℝ} (hr : Measurable r)
    (hp : Measurable p) (hq : Measurable q)
    (h : Fin 6 → ℝ) (a D p₀ q₀ t₀ w K M : ℝ) (F A : Fin 2 → ℝ)
    (γ : Fin n → ℤ × ℤ) (ha : 0 ≤ a) (hD : 0 < D) (hw : 0 < w)
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hcover : ∀ l ∈ C, ∃ i, jetCode r p q D p₀ q₀ t₀ w F A l = γ i)
    (hbase : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |predictor h t p q| ≤ K)
    (hγ : ∀ i, |w * (γ i).1| ≤ M ∧ |w * (γ i).2| ≤ M)
    (hF : ∀ i, |F i| ≤ M) (hA : ∀ i, |A i| ≤ M) :
    ∃ (B : Fin n → Set α) (h' : Fin n → Fin 6 → ℝ),
      (∀ i, MeasurableSet (B i)) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i, B i ⊆ C) ∧ (⋃ i, B i) = C ∧
      (∀ i, ∀ l ∈ B i, ∀ t ∈ Icc (0 : ℝ) 1,
        |predictor h t (p l) (q l) + a * (r l 0 + t * r l 1) -
          predictor (h' i) t (p l) (q l)| ≤ 2 * a * w) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
        |predictor (h' i) t p q| ≤ K + 6 * a * M) := by
  let S : Fin n → Set α := fun i => C ∩ {l | jetCode r p q D p₀ q₀ t₀ w F A l = γ i}
  let B := firstAssignment S
  let h' : Fin n → Fin 6 → ℝ := fun i =>
    upgrade h a D p₀ q₀ t₀ (w * (γ i).1) (w * (γ i).2) F A
  have hcode := measurable_jetCode hr hp hq D p₀ q₀ t₀ w F A
  have hS : ∀ i, MeasurableSet (S i) := fun i =>
    hC.inter (measurableSet_eq_fun hcode measurable_const)
  refine ⟨B, h', measurableSet_firstAssignment S hS, firstAssignment_disjoint S,
    (fun i l hl => hl.1.1), ?_, ?_, ?_⟩
  · rw [iUnion_firstAssignment]
    ext l
    simp only [mem_iUnion, S, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨i, hl, _⟩ => hl, fun hl => by
      obtain ⟨i, hi⟩ := hcover l hl
      exact ⟨i, hl, hi⟩⟩
  · intro i l hl t ht
    have hlabel := hl.1.2
    have hv := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hw
      (jetCoordinates r p q D p₀ q₀ t₀ F A l 0)
    have hs := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hw
      (jetCoordinates r p q D p₀ q₀ t₀ F A l 1)
    have hl₀ := congrArg Prod.fst hlabel
    have hl₁ := congrArg Prod.snd hlabel
    change ⌊jetCoordinates r p q D p₀ q₀ t₀ F A l 0 / w⌋ = (γ i).1 at hl₀
    change ⌊jetCoordinates r p q D p₀ q₀ t₀ F A l 1 / w⌋ = (γ i).2 at hl₁
    rw [hl₀] at hv
    rw [hl₁] at hs
    apply upgrade_fit ha ht ht₀
    · convert hv using 1 <;> dsimp [jetCoordinates] <;> congr 1 <;> ring
    · convert hs using 1 <;> dsimp [jetCoordinates] <;> congr 1 <;> ring
  · intro i t ht p' hp' q' hq'
    exact upgrade_bound ha hD ht ht₀ hp' hq' (hbase t ht p' hp' q' hq')
      (hγ i).1 (hγ i).2 hF hA

/-- The new label-floor numerators sum to the old chart weight: the jet-list exponent
cancels precisely against the smaller scalar thickness. -/
theorem jet_floor_budget {n : ℕ} {a w d K W : ℝ} (ha : 0 ≤ a) (hw : 0 < w)
    (hW : 0 ≤ W) (hcount : (n : ℝ) ≤ K * w ^ (-d)) :
    (n : ℝ) * (W * (a * w) ^ d) ≤ K * W * a ^ d := by
  have hid : w ^ (-d) * w ^ d = 1 := by
    rw [← Real.rpow_add hw]
    simp
  calc
    (n : ℝ) * (W * (a * w) ^ d) ≤ (K * w ^ (-d)) * (W * (a * w) ^ d) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hW (Real.rpow_nonneg (by positivity) _))
    _ = K * W * a ^ d * (w ^ (-d) * w ^ d) := by rw [Real.mul_rpow ha hw.le]; ring
    _ = K * W * a ^ d := by rw [hid, mul_one]

end

end Submission.Obl.k4_horizontal_strict_parameter_step
