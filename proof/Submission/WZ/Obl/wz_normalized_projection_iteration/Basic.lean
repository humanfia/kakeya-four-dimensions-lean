-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open MeasureTheory

abbrev Space := LeanEval.Analysis.WangZahlKakeya.Space

abbrev Tube (δ : ℝ) (x v : Space) : Set Space :=
  Metric.thickening δ (segment ℝ x (x + v))

def Family (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1) ∧
  (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) ∧
  (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
    (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) ∧
  (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ Tube δ (x i) (v i)) ∧
  ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)

def Frostman (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
      ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W

def Slope (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 →
    1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1 / 100 : ℝ)

def Projection (f : ℝ → ℝ) (E : Set Space) : Set (ℝ × ℝ) :=
  (fun p : Space => (p 0 + f (p 2) * p 1, p 2)) '' E

def CoarseFine : Prop :=
  ∀ ε κ : ℝ, 0 < ε → ε < 1 → 0 < κ →
    ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
      Frostman η δ n x v → ∀ f : ℝ → ℝ, Slope f → |f 0| ≤ 1 →
      ∃ ρ : ℝ, δ ^ (1 - ε ^ 2) < ρ ∧ ρ < 1 ∧
      ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i)) ∧
      (∀ i, Z i ⊆ Y i) ∧
      ENNReal.ofReal (δ ^ κ * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Z i) ∧
      ENNReal.ofReal ((δ / ρ) ^ ε) *
        volume (Metric.thickening ρ (Projection f (⋃ i, Z i))) ≤
          volume (Projection f (⋃ i, Z i))

def Estimate (ε : ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
      Frostman η δ n x v → ∀ f : ℝ → ℝ, Slope f → |f 0| ≤ 1 →
      ENNReal.ofReal (δ ^ ε) ≤ volume (Projection f (⋃ i, Y i))

theorem family_mono {η η' δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Family η δ n x v Y) : Family η' δ n x v Y := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_⟩
  apply le_trans _ h.2.2.2.2.2.2
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη)
      (Nat.cast_nonneg n)) (sq_nonneg δ)

theorem frostman_mono {η η' δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    {n : ℕ} {x v : Fin n → Space} (h : Frostman η δ n x v) :
    Frostman η' δ n x v := by
  intro W hW
  apply (h W hW).trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη)) (Nat.cast_nonneg n)

theorem projection_mono (f : ℝ → ℝ) {E E' : Set Space} (h : E ⊆ E') :
    Projection f E ⊆ Projection f E' := Set.image_mono h

theorem projection_nonempty (f : ℝ → ℝ) {E : Set Space} (h : E.Nonempty) :
    (Projection f E).Nonempty := h.image _

theorem shading_nonempty {κ δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n)
    {Y : Fin n → Set Space}
    (hY : ENNReal.ofReal (δ ^ κ * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)) :
    (⋃ i, Y i).Nonempty := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hpos : 0 < ENNReal.ofReal (δ ^ κ * (n : ℝ) * δ ^ 2) := by positivity
  by_contra h
  have hempty : ∀ i, Y i = ∅ := by
    intro i
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact h ⟨p, Set.mem_iUnion.mpr ⟨i, hp⟩⟩
  simp only [hempty, measure_empty, Finset.sum_const_zero] at hY
  exact hpos.not_ge hY

theorem estimate_mono {ε ε' : ℝ} (hε : ε ≤ ε') (h : Estimate ε) : Estimate ε' := by
  obtain ⟨η, hη, d0, hd0, h⟩ := h
  refine ⟨η, hη, d0, hd0, ?_⟩
  intro δ hδ hd hδ1 n x v Y hY hv hF f hf hf0
  apply le_trans _ (h δ hδ hd hδ1 n x v Y hY hv hF f hf hf0)
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) hε

end WangZahlLot.Obl.wz_normalized_projection_iteration
