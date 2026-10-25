import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Rounding

/-!
# Atlases from finitely many label levels

At index `k` the residual model has label levels `levs k h` at the grid depths
`h * η k`, `h ≤ m k`, with `m k * η k = U`. A depth `s` is served by the level
`gridLevel (η k) (m k) s`, the last grid depth not above `s`. `withLevels`
installs these label fields in a model. Its atlas follows from the atlas body
at the grid depths, and its nesting from ancestors between consecutive levels.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

/-- The grid level serving depth `s`. -/
def gridLevel (η : ℝ) (m : ℕ) (s : ℝ) : ℕ := min m ⌊s / η⌋₊

theorem gridLevel_le (η : ℝ) (m : ℕ) (s : ℝ) : gridLevel η m s ≤ m := min_le_left _ _

theorem gridLevel_mul_le {η s : ℝ} (hη : 0 < η) (hs : 0 ≤ s) (m : ℕ) :
    (gridLevel η m s : ℝ) * η ≤ s := by
  have h1 : (gridLevel η m s : ℝ) ≤ ⌊s / η⌋₊ := by
    exact_mod_cast min_le_right _ _
  have h2 : (⌊s / η⌋₊ : ℝ) ≤ s / η := Nat.floor_le (div_nonneg hs hη.le)
  calc
    (gridLevel η m s : ℝ) * η ≤ s / η * η := mul_le_mul_of_nonneg_right (h1.trans h2) hη.le
    _ = s := div_mul_cancel₀ s hη.ne'

theorem le_gridLevel_mul_add {η s : ℝ} (hη : 0 < η) (m : ℕ)
    (hsm : s ≤ m * η) : s ≤ (gridLevel η m s : ℝ) * η + η := by
  by_cases hfl : ⌊s / η⌋₊ ≤ m
  · have heq : gridLevel η m s = ⌊s / η⌋₊ := min_eq_right hfl
    have h := Nat.lt_floor_add_one (s / η)
    rw [heq]
    have : s / η * η < ((⌊s / η⌋₊ : ℝ) + 1) * η := mul_lt_mul_of_pos_right h hη
    rw [div_mul_cancel₀ s hη.ne'] at this
    linarith
  · push_neg at hfl
    exfalso
    have h1 : ((m : ℝ) + 1) ≤ ⌊s / η⌋₊ := by exact_mod_cast hfl
    have hs0 : 0 ≤ s / η := by
      by_contra hneg
      push_neg at hneg
      have : ⌊s / η⌋₊ = 0 := Nat.floor_eq_zero.mpr (hneg.trans zero_lt_one)
      omega
    have h2 : (⌊s / η⌋₊ : ℝ) ≤ s / η := Nat.floor_le hs0
    have h3 : s / η ≤ m := by rw [div_le_iff₀ hη]; exact hsm
    linarith

theorem gridLevel_mono {η : ℝ} (hη : 0 < η) (m : ℕ) {s t : ℝ} (hst : s ≤ t) :
    gridLevel η m s ≤ gridLevel η m t :=
  min_le_min le_rfl (Nat.floor_le_floor (div_le_div_of_nonneg_right hst hη.le))

/-- Install the grid label levels in a model. -/
def withLevels {α : Type} [MeasurableSpace α] (cfg : Data α)
    (levs : ℕ → ℕ → LabelLevel α) (η : ℕ → ℝ) (m : ℕ → ℕ) : Data α :=
  { cfg with
    n := fun k s => (levs k (gridLevel (η k) (m k) s)).n
    T := fun k s => (levs k (gridLevel (η k) (m k) s)).T
    j := fun k s => (levs k (gridLevel (η k) (m k) s)).j
    A := fun k s => (levs k (gridLevel (η k) (m k) s)).A
    B := fun k s => (levs k (gridLevel (η k) (m k) s)).B
    c := fun k s => (levs k (gridLevel (η k) (m k) s)).c
    F := fun k s => (levs k (gridLevel (η k) (m k) s)).F }

theorem levelOf_withLevels {α : Type} [MeasurableSpace α] (cfg : Data α)
    (levs : ℕ → ℕ → LabelLevel α) (η : ℕ → ℝ) (m : ℕ → ℕ) (k : ℕ) (s : ℝ) :
    levelOf (withLevels cfg levs η m) k s = levs k (gridLevel (η k) (m k) s) := rfl

/-- The atlas of the grid model from the atlas body at the grid depths. -/
theorem atlas_withLevels {α : Type} [MeasurableSpace α] (cfg : Data α)
    (levs : ℕ → ℕ → LabelLevel α) (η : ℕ → ℝ) (m : ℕ → ℕ)
    (hN : ∀ k, 1 ≤ cfg.N k) (hd : 0 ≤ cfg.d) (hκ : 0 ≤ cfg.κ) (hℓ : 0 ≤ cfg.ℓ)
    (hη : ∀ k, 0 < η k) (hmη : ∀ k, (m k : ℝ) * η k = cfg.U)
    (K₁ : ℕ → ℝ) (hK₁ : ∀ k, 0 < K₁ k)
    (hcost : ∀ᶠ k in atTop, K₁ k * roundCost cfg k (η k) ≤ cfg.K k)
    (hlev : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ h ≤ m k,
      AtlasBody (withLevels cfg levs η m) k R (h * η k) (levs k h) (K₁ k)) :
    (withLevels cfg levs η m).Atlas := by
  rw [atlas_iff_body]
  intro R hR
  filter_upwards [hlev R hR, hcost] with k hk hc
  intro s hs1 hs2
  have hR0 : 0 < R := by linarith
  have hs0 : 0 ≤ s := (inv_pos.mpr hR0).le.trans hs1
  set h := gridLevel (η k) (m k) s
  have hσ : (h : ℝ) * η k ≤ s := gridLevel_mul_le (hη k) hs0 (m k)
  have hsσ : s ≤ (h : ℝ) * η k + η k := by
    apply le_gridLevel_mul_add (hη k) (m k)
    rw [hmη k]
    exact hs2
  rw [levelOf_withLevels]
  exact atlasBody_round (withLevels cfg levs η m) (hN k) hd hκ hℓ (hK₁ k) (hη k).le
    hσ hsσ hc (hk h (gridLevel_le _ _ _))

/-- Ancestors between consecutive levels give ancestors between any two. -/
theorem ancestor_of_consecutive {α : Type} (lev : ℕ → LabelLevel α) (m : ℕ)
    (hup : ∀ h, h < m → ∀ i : Fin (lev (h + 1)).n, ∃ i' : Fin (lev h).n,
      (lev (h + 1)).A i ⊆ (lev h).A i' ∧
        Data.I (lev (h + 1)).T ((lev (h + 1)).j i) ⊆ Data.I (lev h).T ((lev h).j i')) :
    ∀ h₁ h₂, h₁ ≤ h₂ → h₂ ≤ m → ∀ i : Fin (lev h₂).n, ∃ i' : Fin (lev h₁).n,
      (lev h₂).A i ⊆ (lev h₁).A i' ∧
        Data.I (lev h₂).T ((lev h₂).j i) ⊆ Data.I (lev h₁).T ((lev h₁).j i') := by
  intro h₁ h₂ h12 h2m
  induction h₂, h12 using Nat.le_induction with
  | base => exact fun i => ⟨i, le_rfl, le_rfl⟩
  | succ h₂ h12 ih =>
    intro i
    obtain ⟨i', hA', hI'⟩ := hup h₂ (by omega) i
    obtain ⟨i'', hA'', hI''⟩ := ih (by omega) i'
    exact ⟨i'', hA'.trans hA'', hI'.trans hI''⟩

/-- The nesting of the grid model from ancestors between consecutive levels. -/
theorem nested_withLevels {α : Type} [MeasurableSpace α] (cfg : Data α)
    (levs : ℕ → ℕ → LabelLevel α) (η : ℕ → ℝ) (m : ℕ → ℕ)
    (hη : ∀ k, 0 < η k)
    (hup : ∀ᶠ k in atTop, ∀ h, h < m k → ∀ i : Fin (levs k (h + 1)).n,
      ∃ i' : Fin (levs k h).n, (levs k (h + 1)).A i ⊆ (levs k h).A i' ∧
        Data.I (levs k (h + 1)).T ((levs k (h + 1)).j i) ⊆
          Data.I (levs k h).T ((levs k h).j i')) :
    (withLevels cfg levs η m).Nested := by
  intro R _
  filter_upwards [hup] with k hk
  intro s t _ hst _ i
  exact ancestor_of_consecutive (levs k) (m k) hk _ _
    (gridLevel_mono (hη k) (m k) hst.le) (gridLevel_le _ _ _) i

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
