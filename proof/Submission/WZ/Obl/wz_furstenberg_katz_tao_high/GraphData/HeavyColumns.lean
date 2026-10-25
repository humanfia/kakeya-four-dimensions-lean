-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.HeavyColumns.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/HeavyColumns.lean (82de8bd).
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.BridgeThin

/-!
# Heavy columns are Frostman

Columns `I ⊆ ℝ`, classes `J` and a relation `R y j` ("class `j` meets column `y`") of density `d`.
Suppose each class meets few columns in every window: `#{y : R y j, |y - z| ≤ ρ} ≤ A ρ^β κ` for
`ρ ≥ ρ₀` (two-ended pins along the class).  The heavy columns `H`, met by at least `d #J / 2`
classes, satisfy

* `card_heavy_ge`: `#H ≥ d #I / 2`;
* `heavy_window_le`: `#{y ∈ H : |y - z| ≤ ρ} ≤ (2/d) A ρ^β κ`;
* `heavy_frostman`: if `κ ≤ #I`, the normalized bound `#{y ∈ H : |y - z| ≤ ρ} ≤ (4/d²) A ρ^β #H`;
* `heavy_density`: the relation restricted to `H × J` has density at least `d/2`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Heavy

variable {β' : Type*}

/-- Counting a relation on a product row by row. -/
theorem card_filter_product_eq_sum (I : Finset ℝ) (J : Finset β') (R : ℝ → β' → Prop) :
    ((((I ×ˢ J).filter (fun p => R p.1 p.2))).card : ℝ) =
      ∑ y ∈ I, ((J.filter (fun j => R y j)).card : ℝ) := by
  rw [Finset.card_filter, Finset.sum_product]
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.card_filter]
  push_cast
  rfl

/-- The heavy columns. -/
noncomputable def heavyCols (I : Finset ℝ) (J : Finset β') (R : ℝ → β' → Prop) (d : ℝ) :
    Finset ℝ :=
  I.filter (fun y => d / 2 * (J.card : ℝ) ≤ ((J.filter (fun j => R y j)).card : ℝ))

theorem card_heavy_ge (I : Finset ℝ) (J : Finset β') (R : ℝ → β' → Prop) {d : ℝ}
    (hJ : J.Nonempty)
    (hdens : d * (I.card : ℝ) * J.card ≤ ((((I ×ˢ J).filter (fun p => R p.1 p.2))).card : ℝ)) :
    d / 2 * (I.card : ℝ) ≤ ((heavyCols I J R d).card : ℝ) := by
  have hJpos : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
  have hsum := card_filter_product_eq_sum I J R
  have h := many_heavy I (fun y => ((J.filter (fun j => R y j)).card : ℝ)) (c := d) hJpos
    (fun y _ => by exact_mod_cast Finset.card_filter_le _ _) (by rw [← hsum]; exact hdens)
  simpa [heavyCols] using h

theorem heavy_window_le (I : Finset ℝ) (J : Finset β') (R : ℝ → β' → Prop) {d A β κ ρ₀ : ℝ}
    (hd : 0 < d) (hJ : J.Nonempty)
    (hclass : ∀ j ∈ J, ∀ z ρ : ℝ, ρ₀ ≤ ρ →
      ((I.filter (fun y => R y j ∧ |y - z| ≤ ρ)).card : ℝ) ≤ A * ρ ^ β * κ)
    (z ρ : ℝ) (hρ : ρ₀ ≤ ρ) :
    (((heavyCols I J R d).filter (fun y => |y - z| ≤ ρ)).card : ℝ) ≤ 2 / d * (A * ρ ^ β * κ) := by
  set Hz := (heavyCols I J R d).filter (fun y => |y - z| ≤ ρ) with hHz
  have hJpos : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
  -- double count pairs (heavy column in the window, class meeting it)
  have hlow : (Hz.card : ℝ) * (d / 2 * J.card) ≤
      ∑ y ∈ Hz, ((J.filter (fun j => R y j)).card : ℝ) := by
    calc (Hz.card : ℝ) * (d / 2 * J.card) = ∑ _y ∈ Hz, d / 2 * (J.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun y hy => by
          have := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
          exact this)
  have hswap : ∑ y ∈ Hz, ((J.filter (fun j => R y j)).card : ℝ) =
      ∑ j ∈ J, ((Hz.filter (fun y => R y j)).card : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum]
    rw [Finset.sum_comm]
  have hup : ∑ j ∈ J, ((Hz.filter (fun y => R y j)).card : ℝ) ≤ J.card * (A * ρ ^ β * κ) := by
    calc ∑ j ∈ J, ((Hz.filter (fun y => R y j)).card : ℝ)
        ≤ ∑ _j ∈ J, A * ρ ^ β * κ := Finset.sum_le_sum (fun j hj => by
          refine le_trans ?_ (hclass j hj z ρ hρ)
          apply Nat.cast_le.mpr
          apply Finset.card_le_card
          intro y hy
          obtain ⟨hyH, hRy⟩ := Finset.mem_filter.mp hy
          obtain ⟨hyH', hyz⟩ := Finset.mem_filter.mp hyH
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyH').1, hRy, hyz⟩)
      _ = J.card * (A * ρ ^ β * κ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hchain : (Hz.card : ℝ) * (d / 2 * J.card) ≤ J.card * (A * ρ ^ β * κ) :=
    hlow.trans (hswap ▸ hup)
  have hd2 : 0 < d / 2 * (J.card : ℝ) := by positivity
  rw [show (2 / d * (A * ρ ^ β * κ)) = (J.card * (A * ρ ^ β * κ)) / (d / 2 * J.card) by
    field_simp]
  rw [le_div_iff₀ hd2]
  exact hchain

theorem heavy_frostman (I : Finset ℝ) (J : Finset β') (R : ℝ → β' → Prop) {d A β κ ρ₀ : ℝ}
    (hd : 0 < d) (hJ : J.Nonempty) (hA : 0 ≤ A) (hκ0 : 0 ≤ κ) (hκ : κ ≤ I.card)
    (hdens : d * (I.card : ℝ) * J.card ≤ ((((I ×ˢ J).filter (fun p => R p.1 p.2))).card : ℝ))
    (hclass : ∀ j ∈ J, ∀ z ρ : ℝ, ρ₀ ≤ ρ →
      ((I.filter (fun y => R y j ∧ |y - z| ≤ ρ)).card : ℝ) ≤ A * ρ ^ β * κ)
    (z ρ : ℝ) (hρ : ρ₀ ≤ ρ) (hρ0 : 0 ≤ ρ) :
    (((heavyCols I J R d).filter (fun y => |y - z| ≤ ρ)).card : ℝ) ≤
      4 / d ^ 2 * A * ρ ^ β * (heavyCols I J R d).card := by
  have h1 := heavy_window_le I J R hd hJ hclass z ρ hρ
  have h2 := card_heavy_ge I J R hJ hdens
  have hIH : (I.card : ℝ) ≤ 2 / d * (heavyCols I J R d).card := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]; linarith
  have hpow : 0 ≤ ρ ^ β := Real.rpow_nonneg hρ0 _
  calc (((heavyCols I J R d).filter (fun y => |y - z| ≤ ρ)).card : ℝ)
      ≤ 2 / d * (A * ρ ^ β * κ) := h1
    _ ≤ 2 / d * (A * ρ ^ β * (2 / d * (heavyCols I J R d).card)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (hκ.trans hIH) (mul_nonneg hA hpow)
    _ = 4 / d ^ 2 * A * ρ ^ β * (heavyCols I J R d).card := by ring

theorem heavy_density (I : Finset ℝ) (J : Finset β') (R : ℝ → β' → Prop) {d : ℝ} (hd : 0 < d) :
    d / 2 * ((heavyCols I J R d).card : ℝ) * J.card ≤
      (((((heavyCols I J R d) ×ˢ J).filter (fun p => R p.1 p.2))).card : ℝ) := by
  rw [card_filter_product_eq_sum]
  calc d / 2 * ((heavyCols I J R d).card : ℝ) * J.card
      = ∑ _y ∈ heavyCols I J R d, d / 2 * (J.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ y ∈ heavyCols I J R d, ((J.filter (fun j => R y j)).card : ℝ) :=
        Finset.sum_le_sum (fun y hy => (Finset.mem_filter.mp hy).2)

end Heavy

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open scoped BigOperators

/-- **A tube with a large energy ratio.**  For tubes `t ∈ T` with incidences `Ic t ≥ 0`, energies
`En t > 0` and sizes `Sz t ≥ 0` (classes times columns), if `∑ Ic ≥ I > 0`, `∑ En ≤ E` and
`∑ Sz ≤ X` (`E, X > 0`), then some tube has `Ic t ^ 2 / En t ≥ (I² / (E X)) · Sz t` and
`Ic t > 0`. -/
theorem exists_tube_energy_ratio {τ : Type*} (T : Finset τ) (Ic En Sz : τ → ℝ) {I E X : ℝ}
    (hI : 0 < I) (hE : 0 < E) (hX : 0 < X) (hIc : ∀ t ∈ T, 0 ≤ Ic t) (hEn : ∀ t ∈ T, 0 < En t)
    (hSz : ∀ t ∈ T, 0 ≤ Sz t) (hIsum : I ≤ ∑ t ∈ T, Ic t) (hEsum : ∑ t ∈ T, En t ≤ E)
    (hXsum : ∑ t ∈ T, Sz t ≤ X) :
    ∃ t ∈ T, 0 < Ic t ∧ I ^ 2 / (E * X) * Sz t ≤ Ic t ^ 2 / En t := by
  classical
  set c := I ^ 2 / (E * X) with hc
  have hc0 : 0 ≤ c := by positivity
  -- Cauchy–Schwarz: (∑ Ic)² ≤ (∑ En) (∑ Ic²/En)
  have hCS : (∑ t ∈ T, Ic t) ^ 2 ≤ (∑ t ∈ T, En t) * ∑ t ∈ T, Ic t ^ 2 / En t := by
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq T (fun t => Real.sqrt (En t))
      (fun t => Ic t / Real.sqrt (En t))
    have e1 : ∀ t ∈ T, Real.sqrt (En t) * (Ic t / Real.sqrt (En t)) = Ic t := by
      intro t ht
      have hs : 0 < Real.sqrt (En t) := Real.sqrt_pos.mpr (hEn t ht)
      field_simp
    have e2 : ∀ t ∈ T, Real.sqrt (En t) ^ 2 = En t := fun t ht =>
      Real.sq_sqrt (hEn t ht).le
    have e3 : ∀ t ∈ T, (Ic t / Real.sqrt (En t)) ^ 2 = Ic t ^ 2 / En t := by
      intro t ht
      rw [div_pow, Real.sq_sqrt (hEn t ht).le]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h2
    exact h2
  have hpos : 0 < ∑ t ∈ T, Ic t := lt_of_lt_of_le hI hIsum
  have hTne : T.Nonempty := by
    by_contra hT
    rw [Finset.not_nonempty_iff_eq_empty] at hT
    rw [hT, Finset.sum_empty] at hpos
    linarith
  have hratio : I ^ 2 / E ≤ ∑ t ∈ T, Ic t ^ 2 / En t := by
    have hEs : 0 < ∑ t ∈ T, En t := Finset.sum_pos (fun t ht => hEn t ht) hTne
    rw [div_le_iff₀ hE]
    calc I ^ 2 ≤ (∑ t ∈ T, Ic t) ^ 2 := pow_le_pow_left₀ hI.le hIsum 2
      _ ≤ (∑ t ∈ T, En t) * ∑ t ∈ T, Ic t ^ 2 / En t := hCS
      _ ≤ E * ∑ t ∈ T, Ic t ^ 2 / En t := by
          apply mul_le_mul_of_nonneg_right hEsum
          exact Finset.sum_nonneg (fun t ht => div_nonneg (sq_nonneg _) (hEn t ht).le)
      _ = (∑ t ∈ T, Ic t ^ 2 / En t) * E := by ring
  by_contra hno
  push Not at hno
  have hle : ∀ t ∈ T, Ic t ^ 2 / En t ≤ c * Sz t := by
    intro t ht
    rcases lt_or_eq_of_le (hIc t ht) with h | h
    · exact (hno t ht h).le
    · rw [← h]; simp; exact mul_nonneg hc0 (hSz t ht)
  obtain ⟨t₀, ht₀, hIt₀⟩ : ∃ t ∈ T, 0 < Ic t := by
    by_contra hz
    push Not at hz
    have : ∑ t ∈ T, Ic t ≤ 0 := Finset.sum_nonpos (fun t ht => hz t ht)
    linarith
  have hstrict : ∑ t ∈ T, Ic t ^ 2 / En t < c * ∑ t ∈ T, Sz t := by
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum hle ⟨t₀, ht₀, hno t₀ ht₀ hIt₀⟩
  have hcX : c * ∑ t ∈ T, Sz t ≤ c * X := mul_le_mul_of_nonneg_left hXsum hc0
  have e : c * X = I ^ 2 / E := by rw [hc]; field_simp
  linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
