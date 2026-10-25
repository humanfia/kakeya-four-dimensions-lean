import Submission.Obl.k4_scalar_true_terminal_lifting.ChartMono

/-!
# Elementary facts for chart lifting

Two-candidate floors, composition of dyadic time cells, volumes of dyadic cells and of
intersections of distinct cells, and the mass bound of a selected incidence set by its
assigned prior mass times the cell length.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Filter Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- A number within one unit above `a` has one of two floors. -/
lemma floor_two {a X : ℝ} (h1 : a ≤ X) (h2 : X < a + 1) :
    ∃ s : Fin 2, ⌊X⌋ = ⌊a⌋ + ((s : ℕ) : ℤ) := by
  have hA : ⌊a⌋ ≤ ⌊X⌋ := Int.floor_mono h1
  have hB : ⌊X⌋ < ⌊a⌋ + 2 := by
    rw [Int.floor_lt]
    have := Int.lt_floor_add_one a
    push_cast
    linarith
  rcases (show ⌊X⌋ = ⌊a⌋ ∨ ⌊X⌋ = ⌊a⌋ + 1 by omega) with hX | hX
  · exact ⟨0, by simp [hX]⟩
  · exact ⟨1, by simp [hX]⟩

/-- Composition of dyadic indices: the `j₂`-th subcell of the `j₁`-th cell. -/
def jcomp {T₁ T₂ : ℕ} (j₁ : Fin (2 ^ T₁)) (j₂ : Fin (2 ^ T₂)) : Fin (2 ^ (T₁ + T₂)) :=
  ⟨(j₁ : ℕ) * 2 ^ T₂ + j₂, by
    have h1 := j₁.isLt
    have h2 := j₂.isLt
    rw [pow_add]
    calc (j₁ : ℕ) * 2 ^ T₂ + j₂ < (j₁ : ℕ) * 2 ^ T₂ + 2 ^ T₂ := by omega
      _ = ((j₁ : ℕ) + 1) * 2 ^ T₂ := by ring
      _ ≤ 2 ^ T₁ * 2 ^ T₂ := Nat.mul_le_mul_right _ h1⟩

lemma jcomp_inj {T₁ T₂ : ℕ} {j₁ j₁' : Fin (2 ^ T₁)} {j₂ j₂' : Fin (2 ^ T₂)}
    (h : jcomp j₁ j₂ = jcomp j₁' j₂') : j₁ = j₁' ∧ j₂ = j₂' := by
  have h' : (j₂ : ℕ) + (j₁ : ℕ) * 2 ^ T₂ = (j₂' : ℕ) + (j₁' : ℕ) * 2 ^ T₂ := by
    have := congrArg Fin.val h
    simp only [jcomp] at this
    omega
  have hpos : 0 < 2 ^ T₂ := by positivity
  have hj2 := j₂.isLt
  have hj2' := j₂'.isLt
  have e1 : ((j₂ : ℕ) + (j₁ : ℕ) * 2 ^ T₂) / 2 ^ T₂ = j₁ := by
    rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj2, zero_add]
  have e2 : ((j₂' : ℕ) + (j₁' : ℕ) * 2 ^ T₂) / 2 ^ T₂ = j₁' := by
    rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj2', zero_add]
  have m1 : ((j₂ : ℕ) + (j₁ : ℕ) * 2 ^ T₂) % 2 ^ T₂ = j₂ := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj2]
  have m2 : ((j₂' : ℕ) + (j₁' : ℕ) * 2 ^ T₂) % 2 ^ T₂ = j₂' := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj2']
  constructor
  · apply Fin.ext
    rw [← e1, ← e2, h']
  · apply Fin.ext
    rw [← m1, ← m2, h']

lemma mem_I_jcomp {T₁ T₂ : ℕ} (j₁ : Fin (2 ^ T₁)) (j₂ : Fin (2 ^ T₂)) (t : ℝ) :
    t ∈ I (T₁ + T₂) (jcomp j₁ j₂) ↔
      (t - ((j₁ : ℕ) : ℝ) * ((2 : ℝ) ^ T₁)⁻¹) / ((2 : ℝ) ^ T₁)⁻¹ ∈ I T₂ j₂ := by
  have ha : (0 : ℝ) < 2 ^ T₁ := by positivity
  have hb : (0 : ℝ) < 2 ^ T₂ := by positivity
  have hab : (0 : ℝ) < 2 ^ T₁ * 2 ^ T₂ := mul_pos ha hb
  have key : (t - ((j₁ : ℕ) : ℝ) * ((2 : ℝ) ^ T₁)⁻¹) / ((2 : ℝ) ^ T₁)⁻¹ =
      t * 2 ^ T₁ - ((j₁ : ℕ) : ℝ) := by
    field_simp
  rw [key]
  simp only [I, jcomp, Set.mem_Icc]
  push_cast
  rw [pow_add, div_le_iff₀ hab, le_div_iff₀ hab, div_le_iff₀ hb, le_div_iff₀ hb]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

lemma volume_I (T : ℕ) (j : Fin (2 ^ T)) :
    volume (I T j) = ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) := by
  simp only [I, Real.volume_Icc]
  congr 1
  ring

/-- Two dyadic cells with strictly ordered indices meet in a null set. -/
lemma lb_volume_I_inter_lt (T : ℕ) {j j' : Fin (2 ^ T)} (h : (j : ℕ) < (j' : ℕ)) :
    volume (I T j ∩ I T j') = 0 := by
  have hT : (0 : ℝ) < 2 ^ T := by positivity
  have hjj : ((j : ℕ) : ℝ) + 1 ≤ ((j' : ℕ) : ℝ) := by exact_mod_cast h
  have h1 : (((j : ℕ) : ℝ) + 1) / 2 ^ T ≤ ((j' : ℕ) : ℝ) / 2 ^ T :=
    div_le_div_of_nonneg_right hjj hT.le
  simp only [I, Set.Icc_inter_Icc, Real.volume_Icc, ENNReal.ofReal_eq_zero, sub_nonpos]
  calc (((j : ℕ) : ℝ) + 1) / 2 ^ T ⊓ (((j' : ℕ) : ℝ) + 1) / 2 ^ T
      ≤ (((j : ℕ) : ℝ) + 1) / 2 ^ T := inf_le_left
    _ ≤ ((j' : ℕ) : ℝ) / 2 ^ T := h1
    _ ≤ ((j : ℕ) : ℝ) / 2 ^ T ⊔ ((j' : ℕ) : ℝ) / 2 ^ T := le_sup_right

lemma volume_I_inter (T : ℕ) {j j' : Fin (2 ^ T)} (h : j ≠ j') :
    volume (I T j ∩ I T j') = 0 := by
  have hne : (j : ℕ) ≠ (j' : ℕ) := fun e => h (Fin.ext e)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact lb_volume_I_inter_lt T hlt
  · rw [Set.inter_comm]
    exact lb_volume_I_inter_lt T hlt

/-- A selected incidence set inside `A ×ˢ I T j` has mass at most `ν(A)` times the cell
length. -/
lemma mu_le_of_subset (p : Code) (k : ℕ) (a : Fin (W p k)) [SFinite (ν p k a)]
    {A' : Set (ℕ × (Fin 5 → ℝ))} {Cs : Set ((ℕ × (Fin 5 → ℝ)) × ℝ)} {T : ℕ}
    {jj : Fin (2 ^ T)} (h : Cs ⊆ A' ×ˢ I T jj) :
    mu p k a Cs ≤ ν p k a A' * ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) := by
  unfold mu
  calc ((ν p k a).prod volume).restrict (E p k a) Cs
      ≤ ((ν p k a).prod volume) Cs := Measure.restrict_apply_le _ _
    _ ≤ ((ν p k a).prod volume) (A' ×ˢ I T jj) := measure_mono h
    _ ≤ ν p k a A' * volume (I T jj) := Measure.prod_prod_le _ _
    _ = ν p k a A' * ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) := by rw [volume_I]

/-- Distinct pieces of a chart in the same world have null overlap. -/
lemma mu_inter_null_of_chart {p : Code} {B : ℕ} {r b h ε : ℝ} {isTrue : Bool} {k T n : ℕ}
    {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set (ℕ × (Fin 5 → ℝ))} {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hcd : ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (hν : ∀ a, IsProbabilityMeasure (ν p k a)) {i i' : Fin n} (hii' : i ≠ i')
    (hγ : γ i = γ i') : mu p k (γ i) (C i ∩ C i') = 0 := by
  unfold ChartData at hcd
  obtain ⟨-, -, -, h4, h5, -⟩ := hcd
  by_cases hj : j i = j i'
  · have hdisj := h4 i i' hii' hγ hj
    have hempty : C i ∩ C i' = ∅ := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hq hq'
      exact Set.disjoint_left.1 hdisj (h5 i hq).2.1 (h5 i' hq').2.1
    rw [hempty, measure_empty]
  · have hsub : C i ∩ C i' ⊆ Set.univ ×ˢ (I T (j i) ∩ I T (j i')) := by
      rintro q ⟨hq, hq'⟩
      exact ⟨Set.mem_univ _, (h5 i hq).2.2, (h5 i' hq').2.2⟩
    have := hν (γ i)
    refine nonpos_iff_eq_zero.mp ?_
    unfold mu
    calc ((ν p k (γ i)).prod volume).restrict (E p k (γ i)) (C i ∩ C i')
        ≤ ((ν p k (γ i)).prod volume) (C i ∩ C i') := Measure.restrict_apply_le _ _
      _ ≤ ((ν p k (γ i)).prod volume) (Set.univ ×ˢ (I T (j i) ∩ I T (j i'))) :=
          measure_mono hsub
      _ = ν p k (γ i) Set.univ * volume (I T (j i) ∩ I T (j i')) := Measure.prod_prod _ _
      _ = 0 := by rw [measure_univ, volume_I_inter T hj, mul_zero]

end Submission.Obl.k4_scalar_true_terminal_lifting
