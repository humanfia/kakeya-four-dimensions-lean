-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/CellFiberChoices.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/CellFiberChoices.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/CellFiberChoices.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Lib.K4CommonLocalChoice
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.MeasureCapture

/-!
Common field and polynomial-fiber choices with original state masses.
The accepted local-choice theorem is used with zero coordinate dimension,
so there is one choice per actual finite key and no cell-count loss.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set
open Submission.Lib.K4CommonLocalChoice

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Select one occurring value bin for each finite key. The original
measure pays only the list size, independently of the number of keys. -/
theorem select_key_value_bins {n q : ℕ} (μ : Measure X) [IsFiniteMeasure μ]
    (key : X → Fin n) (hkey : Measurable key)
    (Y : X → Fin q → ℝ) (hY : Measurable Y)
    (S : Set X) (hS : MeasurableSet S) (p : ℝ) (K : ℕ)
    (hlist : ∀ k, ∃ F : Finset (Fin q → ℤ), F.card ≤ K ∧
      ∀ x ∈ S, key x = k → cell p (Y x) ∈ F) :
    ∃ (table : Fin n → Fin q → ℤ) (T : Set X),
      MeasurableSet T ∧ T ⊆ S ∧
      (∀ x, x ∈ T ↔ x ∈ S ∧ cell p (Y x) = table (key x)) ∧
      μ.real S ≤ (K : ℝ) * μ.real T := by
  obtain ⟨c, m, hT, hmass⟩ := one_scale μ key hkey
    (fun _ : X => (0 : Fin 0 → ℝ)) measurable_const Y hY S hS p K
    (fun k _ => by
      obtain ⟨F, hF, hm⟩ := hlist k
      exact ⟨F, hF, fun x hx hk _ => hm x hx hk⟩)
  let T := {x | x ∈ S ∧ color (cell p (0 : Fin 0 → ℝ)) = c (key x) ∧
    cell p (Y x) = m (key x) (cell p (0 : Fin 0 → ℝ))}
  let table : Fin n → Fin q → ℤ := fun k => m k 0
  have hzero : cell p (0 : Fin 0 → ℝ) = 0 := Subsingleton.elim _ _
  have hTmeas : MeasurableSet T := hT
  have hmem (x : X) : x ∈ T ↔ x ∈ S ∧ cell p (Y x) = table (key x) := by
    change (x ∈ S ∧ _ ∧ _) ↔ _
    rw [hzero]
    constructor
    · intro hx
      exact ⟨hx.1, hx.2.2⟩
    · intro hx
      exact ⟨hx.1, Subsingleton.elim _ _, hx.2⟩
  have hkeymass (k : Fin n) : μ.real (S ∩ key ⁻¹' {k}) ≤
      (K : ℝ) * μ.real (T ∩ key ⁻¹' {k}) := by
    have hk : μ (S ∩ key ⁻¹' {k}) ≤ (K : ENNReal) * μ (T ∩ key ⁻¹' {k}) := by
      simpa only [pow_zero, one_mul] using hmass k
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast] using
      ENNReal.toReal_mono (by finiteness) hk
  have hsum (U : Set X) (hU : MeasurableSet U) :
      (∑ k, μ.real (U ∩ key ⁻¹' {k})) = μ.real U := by
    simpa only [codeWeight, measureReal_def, Measure.restrict_apply' hU,
      univ_inter, inter_univ, inter_comm] using sum_codeWeight (μ.restrict U) key hkey
  refine ⟨table, T, hTmeas, fun x hx => (hmem x).mp hx |>.1, hmem, ?_⟩
  calc
    μ.real S = ∑ k, μ.real (S ∩ key ⁻¹' {k}) := (hsum S hS).symm
    _ ≤ ∑ k, (K : ℝ) * μ.real (T ∩ key ⁻¹' {k}) :=
      Finset.sum_le_sum fun k _ => hkeymass k
    _ = (K : ℝ) * μ.real T := by rw [← Finset.mul_sum, hsum T hTmeas]

/-- Successive field and fiber tests choose one value per key at each
stage, keeping the product fraction of the unchanged original mass. -/
theorem simultaneous_key_value_bins
    (μ : Measure X) [IsFiniteMeasure μ] (n q : ℕ → ℕ)
    (key : (i : ℕ) → X → Fin (n i)) (hkey : ∀ i, Measurable (key i))
    (Y : (i : ℕ) → X → Fin (q i) → ℝ) (hY : ∀ i, Measurable (Y i))
    (Ω : Set X) (hΩ : MeasurableSet Ω) (p : ℕ → ℝ) (K : ℕ → ℕ)
    (hlist : ∀ i k, ∃ F : Finset (Fin (q i) → ℤ), F.card ≤ K i ∧
      ∀ x ∈ Ω, key i x = k → cell (p i) (Y i x) ∈ F) :
    ∀ r : ℕ, ∃ (table : (i : ℕ) → Fin (n i) → Fin (q i) → ℤ) (T : Set X),
      MeasurableSet T ∧ T ⊆ Ω ∧
      (∀ x, x ∈ T ↔ x ∈ Ω ∧ ∀ i < r, cell (p i) (Y i x) = table i (key i x)) ∧
      μ.real Ω ≤ (∏ i ∈ Finset.range r, (K i : ℝ)) * μ.real T := by
  classical
  intro r
  induction r with
  | zero =>
    exact ⟨fun _ _ _ => 0, Ω, hΩ, subset_refl _, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨table, T, hT, hTΩ, hmem, hmass⟩ := ih
    obtain ⟨chosen, T', hT', hT'T, hmem', hmass'⟩ := select_key_value_bins μ
      (key r) (hkey r) (Y r) (hY r) T hT (p r) (K r)
      (fun k => by
        obtain ⟨F, hF, hFm⟩ := hlist r k
        exact ⟨F, hF, fun x hx => hFm x (hTΩ hx)⟩)
    let table' := Function.update table r chosen
    refine ⟨table', T', hT', hT'T.trans hTΩ, ?_, ?_⟩
    · intro x
      rw [hmem', hmem]
      constructor
      · intro hx
        refine ⟨hx.1.1, ?_⟩
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · simpa only [table', Function.update_of_ne (Nat.ne_of_lt hi)] using hx.1.2 i hi
        · simpa only [table', Function.update_self] using hx.2
      · intro hx
        refine ⟨⟨hx.1, ?_⟩, ?_⟩
        · intro i hi
          have hh := hx.2 i (Nat.lt_succ_of_lt hi)
          simpa only [table', Function.update_of_ne (Nat.ne_of_lt hi)] using hh
        · have hh := hx.2 r (Nat.lt_succ_self r)
          simpa only [table', Function.update_self] using hh
    · calc
        μ.real Ω ≤ (∏ i ∈ Finset.range r, (K i : ℝ)) * μ.real T := hmass
        _ ≤ (∏ i ∈ Finset.range r, (K i : ℝ)) * ((K r : ℝ) * μ.real T') :=
          mul_le_mul_of_nonneg_left hmass' (Finset.prod_nonneg fun _ _ => by positivity)
        _ = (∏ i ∈ Finset.range (r + 1), (K i : ℝ)) * μ.real T' := by
          rw [Finset.prod_range_succ]
          ring

/-- The key may be any finite measurable type, with no factor depending on
the number of keys. -/
theorem select_finite_key_value_bins {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {q : ℕ}
    (μ : Measure X) [IsFiniteMeasure μ] (key : X → I) (hkey : Measurable key)
    (Y : X → Fin q → ℝ) (hY : Measurable Y) (S : Set X) (hS : MeasurableSet S)
    (p : ℝ) (K : ℕ)
    (hlist : ∀ k, ∃ F : Finset (Fin q → ℤ), F.card ≤ K ∧
      ∀ x ∈ S, key x = k → cell p (Y x) ∈ F) :
    ∃ (table : I → Fin q → ℤ) (T : Set X),
      MeasurableSet T ∧ T ⊆ S ∧
      (∀ x, x ∈ T ↔ x ∈ S ∧ cell p (Y x) = table (key x)) ∧
      μ.real S ≤ (K : ℝ) * μ.real T := by
  classical
  let e := Fintype.equivFin I
  obtain ⟨table, T, hT, hTS, hmem, hmass⟩ := select_key_value_bins μ
    (e ∘ key) ((measurable_of_finite e).comp hkey) Y hY S hS p K
    (fun k => by
      obtain ⟨F, hF, hFm⟩ := hlist (e.symm k)
      refine ⟨F, hF, fun x hx hk => hFm x hx ?_⟩
      apply e.injective
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hk)
  exact ⟨fun i => table (e i), T, hT, hTS, hmem, hmass⟩

omit [MeasurableSpace X] in
/-- The selected family contains every earlier prepared edge of a
surviving state when all tested keys and value bins depend on that state. -/
theorem key_value_selection_saturated {D : Type*}
    (state : X → D) (n q : ℕ → ℕ)
    (key : (i : ℕ) → X → Fin (n i))
    (Y : (i : ℕ) → X → Fin (q i) → ℝ)
    (Ω T : Set X) (p : ℕ → ℝ) (r : ℕ)
    (table : (i : ℕ) → Fin (n i) → Fin (q i) → ℤ)
    (hT : ∀ x, x ∈ T ↔ x ∈ Ω ∧ ∀ i < r, cell (p i) (Y i x) = table i (key i x))
    (hkey : ∀ i < r, ∀ x ∈ Ω, ∀ y ∈ Ω, state x = state y → key i x = key i y)
    (hval : ∀ i < r, ∀ x ∈ Ω, ∀ y ∈ Ω, state x = state y →
      cell (p i) (Y i x) = cell (p i) (Y i y)) :
    ∀ x ∈ T, ∀ y ∈ Ω, state x = state y → y ∈ T := by
  intro x hx y hy hstate
  obtain ⟨hxΩ, hxtests⟩ := (hT x).mp hx
  apply (hT y).mpr
  refine ⟨hy, fun i hi => ?_⟩
  rw [← hkey i hi x hxΩ y hy hstate, ← hval i hi x hxΩ y hy hstate]
  exact hxtests i hi

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
