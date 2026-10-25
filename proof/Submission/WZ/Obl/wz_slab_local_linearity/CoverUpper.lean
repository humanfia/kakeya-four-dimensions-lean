-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CoverUpper.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric

/-- A finite closed-ball cover with a real-valued cardinality bound. -/
def CoverUpper {X : Type*} [PseudoMetricSpace X] (S : Set X) (r N : ℝ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → X), S ⊆ ⋃ j, closedBall (c j) r ∧ (m : ℝ) ≤ N

lemma CoverUpper.of_fintype {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]
    {S : Set X} {r N : ℝ} (c : ι → X)
    (hc : S ⊆ ⋃ j, closedBall (c j) r) (hcard : (Fintype.card ι : ℝ) ≤ N) :
    CoverUpper S r N := by
  classical
  refine ⟨Fintype.card ι, fun j => c ((Fintype.equivFin ι).symm j), ?_, hcard⟩
  intro x hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hc hx)
  refine mem_iUnion.mpr ⟨Fintype.equivFin ι j, ?_⟩
  simpa only [Equiv.symm_apply_apply] using hj

lemma CoverUpper.mono_set {X : Type*} [PseudoMetricSpace X] {A B : Set X} {r N : ℝ}
    (h : CoverUpper B r N) (hAB : A ⊆ B) : CoverUpper A r N := by
  obtain ⟨m, c, hc, hm⟩ := h
  exact ⟨m, c, hAB.trans hc, hm⟩

lemma CoverUpper.mono_bound {X : Type*} [PseudoMetricSpace X] {A : Set X} {r N N' : ℝ}
    (h : CoverUpper A r N) (hNN' : N ≤ N') : CoverUpper A r N' := by
  obtain ⟨m, c, hc, hm⟩ := h
  exact ⟨m, c, hc, hm.trans hNN'⟩

lemma CoverUpper.iUnion {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]
    {A : ι → Set X} {r N : ℝ} (h : ∀ i, CoverUpper (A i) r N) :
    CoverUpper (⋃ i, A i) r ((Fintype.card ι : ℝ) * N) := by
  classical
  choose m c hc hm using h
  apply CoverUpper.of_fintype (fun j : Σ i, Fin (m i) => c j.1 j.2)
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc i hxi)
    exact mem_iUnion.mpr ⟨⟨i, j⟩, hj⟩
  · simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc ∑ i, (m i : ℝ) ≤ ∑ _ : ι, N := Finset.sum_le_sum (fun i _ => hm i)
      _ = (Fintype.card ι : ℝ) * N := by simp

/-- An integer-spaced family of radius-`r` intervals covers a radius-`n*r` interval. -/
lemma scalar_ball_subdivide {r c x : ℝ} (hr : 0 < r) (n : ℕ)
    (hx : |x - c| ≤ (n : ℝ) * r) :
    ∃ j : Fin (2 * n + 1), |x - (c + ((j : ℝ) - n) * r)| ≤ r := by
  have hab := abs_le.mp hx
  have he0 : 0 ≤ (x - c) / r + n := by
    have h : -(n : ℝ) ≤ (x - c) / r := (le_div_iff₀ hr).2 (by linarith)
    linarith
  have he1 : (x - c) / r + n < ((2 * n + 1 : ℕ) : ℝ) := by
    have h := (div_le_iff₀ hr).2 hab.2
    push_cast
    linarith
  let j : Fin (2 * n + 1) := ⟨⌊(x - c) / r + n⌋₊, (Nat.floor_lt he0).2 he1⟩
  have hj0 : (j : ℝ) ≤ (x - c) / r + n := Nat.floor_le he0
  have hj1 : (x - c) / r + n < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have heq : ((x - c) / r) * r = x - c := div_mul_cancel₀ _ hr.ne'
  have hlow := mul_le_mul_of_nonneg_right hj0 hr.le
  have hupp := mul_lt_mul_of_pos_right hj1 hr
  refine ⟨j, abs_le.mpr ?_⟩
  constructor <;> nlinarith

/-- A bounded scalar perturbation and translation cost only a fixed factor in
bottom-scale covering number. -/
lemma CoverUpper.perturb {r C b : ℝ} {A B : Set ℝ} (hr : 0 < r) (n : ℕ)
    (h : CoverUpper A r C)
    (hBA : ∀ x ∈ B, ∃ a ∈ A, |x - (a + b)| ≤ (n : ℝ) * r) :
    CoverUpper B r ((2 * (n : ℝ) + 3) * C) := by
  classical
  obtain ⟨m, c, hc, hm⟩ := h
  apply CoverUpper.of_fintype
    (fun j : Fin m × Fin (2 * (n + 1) + 1) => c j.1 + b + ((j.2 : ℝ) - (n + 1)) * r)
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := hBA x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc ha)
    have hac : |a - c j| ≤ r := by simpa only [mem_closedBall, Real.dist_eq] using hj
    have hxc : |x - (c j + b)| ≤ ((n + 1 : ℕ) : ℝ) * r := by
      calc |x - (c j + b)| ≤ |x - (a + b)| + |(a + b) - (c j + b)| := abs_sub_le _ _ _
        _ ≤ (n : ℝ) * r + r := add_le_add hxa (by simpa only [add_sub_add_right_eq_sub] using hac)
        _ = ((n + 1 : ℕ) : ℝ) * r := by push_cast; ring
    obtain ⟨k, hk⟩ := scalar_ball_subdivide hr (n + 1) hxc
    refine mem_iUnion.mpr ⟨⟨j, k⟩, ?_⟩
    simpa only [mem_closedBall, Real.dist_eq, Nat.cast_add, Nat.cast_one] using hk
  · simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    calc (m : ℝ) * (2 * (n + 1) + 1) ≤ C * (2 * (n + 1) + 1) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
      _ = (2 * (n : ℝ) + 3) * C := by ring

end WangZahlLot.Obl.wz_slab_local_linearity
