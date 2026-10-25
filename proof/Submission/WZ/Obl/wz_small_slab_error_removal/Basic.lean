-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_slab_error_removal.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_endpoint_bootstrap.Estimates

namespace WangZahlLot.Obl.wz_small_slab_error_removal

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_endpoint_bootstrap

/-- The geometric and measurability conditions common to the two estimates. -/
def Admissible (δ : ℝ) {n : ℕ} (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1) ∧
  (∀ i, tube δ (x i) (v i) ⊆ Metric.ball (0 : Space) 1) ∧
  (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
    (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) ∧
  (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ tube δ (x i) (v i))

/-- The coefficient in the arbitrary-error estimate. -/
noncomputable def coefficient (s w ε a δ m l N : ℝ) : ℝ :=
  a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) *
    (m ^ (-(3 / 2 : ℝ)) * l * (N * δ)) ^ (-s)

/-- The restricted assertion: arbitrary convex error, small slab error. -/
def Restricted (s w : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ m : ℝ, 1 ≤ m →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ x v Y → Dense δ η Y → Katz δ m x v →
    Frostman δ (δ ^ (-η)) x v →
    ENNReal.ofReal (coefficient s w ε a δ m 1 n) ≤ volume (⋃ i, Y i)

/-- The arbitrary-error assertion. -/
def General (s w : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ x v Y → Dense δ η Y → Katz δ m x v → Frostman δ l x v →
    ENNReal.ofReal (coefficient s w ε a δ m l n) ≤ volume (⋃ i, Y i)

theorem coefficient_nonneg {s w ε a δ m l N : ℝ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hm : 0 ≤ m) (hl : 0 ≤ l) (hN : 0 ≤ N) :
    0 ≤ coefficient s w ε a δ m l N := by
  unfold coefficient
  positivity

/-- Increasing the slab constant weakens the conclusion. -/
theorem coefficient_antitone_slab {s w ε a δ m l l' N : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hδ : 0 < δ) (hm : 0 < m)
    (hl : 0 < l) (hll : l ≤ l') (hN : 0 < N) :
    coefficient s w ε a δ m l' N ≤ coefficient s w ε a δ m l N := by
  unfold coefficient
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hll (Real.rpow_nonneg hm.le _)) (by positivity)
  · linarith

/-- A slab is one of the convex sets in the Katz--Tao hypothesis. -/
theorem convex_slab (u : Space) (t r : ℝ) :
    Convex ℝ (Metric.ball (0 : Space) 1 ∩ {p : Space | |inner ℝ u p - t| ≤ r}) := by
  have h : {p : Space | |inner ℝ u p - t| ≤ r} =
      {p : Space | t - r ≤ inner ℝ u p} ∩ {p : Space | inner ℝ u p ≤ t + r} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, abs_le]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [h]
  exact (convex_ball _ _).inter
    ((convex_halfSpace_ge (innerSL ℝ u).toLinearMap.isLinear _).inter
      (convex_halfSpace_le (innerSL ℝ u).toLinearMap.isLinear _))

/-- Convex counting supplies a slab constant without any geometric decomposition. -/
theorem frostman_of_katz {δ m : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hn : 0 < n) (hK : Katz δ m x v) :
    Frostman δ (m / ((n : ℝ) * δ ^ 2)) x v := by
  intro u t r hu hr
  have h := hK _ (convex_slab u t r)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : m / ((n : ℝ) * δ ^ 2) * (n : ℝ) = m / δ ^ 2 := by
    field_simp
  rw [heq, ENNReal.ofReal_div_of_pos (sq_pos_of_pos hδ)]
  rw [ENNReal.ofReal_mul (by positivity)] at h
  have hp0 : ENNReal.ofReal (δ ^ 2) ≠ 0 := by positivity
  have hpt : ENNReal.ofReal (δ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_left hp0 hpt).mp
  calc
    _ ≤ ENNReal.ofReal m * volume
        (Metric.ball (0 : Space) 1 ∩ {p : Space | |inner ℝ u p - t| ≤ r}) := h
    _ = _ := by
      symm
      rw [mul_right_comm, ENNReal.div_mul_cancel hp0 hpt]

/-- Direct use of the restricted assertion covers all families whose slab
constant is already smaller than its threshold. -/
theorem restricted_small_slab {s w : ℝ} (hs : 0 ≤ s) (hR : Restricted s w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) →
      ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → l ≤ δ ^ (-η) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible δ x v Y → Dense δ η Y → Katz δ m x v → Frostman δ l x v →
      ENNReal.ofReal (coefficient s w ε a δ m l n) ≤ volume (⋃ i, Y i) := by
  obtain ⟨a, ha, η, hη, h⟩ := hR ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 m l hm hl hlη n x v Y hA hD hK hF
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  exact (ENNReal.ofReal_le_ofReal
    (coefficient_antitone_slab hs ha.le hδ hm0 zero_lt_one hl (Nat.cast_pos.mpr hA.1))).trans
    (h δ hδ hδ100 m hm n x v Y hA hD hK (hF.mono hlη))

end WangZahlLot.Obl.wz_small_slab_error_removal
