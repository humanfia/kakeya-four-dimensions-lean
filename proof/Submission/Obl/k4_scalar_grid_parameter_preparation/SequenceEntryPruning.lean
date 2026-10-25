import Submission.Obl.k4_scalar_grid_parameter_preparation.GridEntryPruning
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth
import Submission.Obl.k4_tempered_grid_selection.SelectionMass

/-! Restore all registered coefficient entries with a single subpower denominator. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped Classical BigOperators ENNReal

theorem exists_sequence_coefficient_entries {X : Type*} [MeasurableSpace X]
    (N K L : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hL : (∀ k, 1 ≤ L k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, L k ≤ N k ^ ε)
    (W : ℕ → ℕ) (a : X → Fin 5 → ℝ) (ha : Measurable a)
    (θ : (k : ℕ) → Fin (W k) → Measure X) (hθ : ∀ k g, θ k g Set.univ ≤ 1)
    (μ : (k : ℕ) → Fin (W k) → Measure (X × ℝ))
    (E : (k : ℕ) → Fin (W k) → Set (X × ℝ))
    (hE : ∀ k g, MeasurableSet (E k g) ∧
      ∀ z ∈ E k g, z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a z.1 e| ≤ K k)
    (Ξ : ℕ → Finset ℝ) (hΞ : ∀ k, ∀ r ∈ Ξ k, 0 < r)
    (hcard : ∀ᶠ k in atTop, ((Ξ k).card : ℝ) ≤ L k) :
    ∃ (P : ℕ → ℝ) (R : (k : ℕ) → Fin (W k) → Set (X × ℝ)),
      ((∀ k, 1 ≤ P k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, P k ≤ N k ^ ε) ∧
      (∀ k g, MeasurableSet (R k g) ∧ R k g ⊆ E k g) ∧
      (∀ᶠ k in atTop, ∀ g, μ k g (E k g \ R k g) ≤ ENNReal.ofReal (1 / (100 * K k))) ∧
      ∀ k g, ∀ r ∈ Ξ k, ∀ (q : Fin 3 → ℤ) (b : Fin 5 → ℤ),
        R k g ∩ {z | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a z) = q ∧
          scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a z.1) = b} = ∅ ∨
        ENNReal.ofReal (N k ^ (-r) / P k) *
          θ k g {l | scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a l) = b} <
          μ k g (R k g ∩ {z | physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition a z) = q ∧
            scalarMixedCoefficientTag (N k ^ (-r)) (N k ^ (-r)) (a z.1) = b}) := by
  classical
  let C : ℝ := 5000 * 111 ^ 3
  let P := fun k => ((100 * C) * K k ^ 2) * L k
  have hN₁ (k) : 1 ≤ N k := by linarith [hN k]
  have hNp (k) : 0 < N k := by linarith [hN k]
  have hKp (k) : 0 < K k := zero_lt_one.trans_le (hK.1 k)
  have hLp (k) : 0 < L k := zero_lt_one.trans_le (hL.1 k)
  have hC : 1 ≤ 100 * C := by norm_num [C]
  have hP := Submission.Obl.k4_tempered_grid_selection.subpower_mul hNp
    (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial hN₁ hNt hK hC 2) hL
  have hPp (k) : 0 < P k := zero_lt_one.trans_le (hP.1 k)
  have hex (k) (g : Fin (W k)) := finite_grid_coefficient_entry_pruning
    (σ := ↥(Ξ k)) (μ k g) (θ k g) a ha (E k g) (hE k g).1
    (fun r => N k ^ (-r.val)) (K k) (P k)
    (fun r => Real.rpow_pos_of_pos (hNp k) _)
    (fun r => Real.rpow_le_one_of_one_le_of_nonpos (hN₁ k) (neg_nonpos.mpr (hΞ k r.val r.property).le))
    (hK.1 k) (hPp k) (hE k g).2
  choose R hRm hRE hloss hfloor using hex
  refine ⟨P,R,hP,fun k g => ⟨hRm k g,hRE k g⟩,?_,?_⟩
  · filter_upwards [hcard] with k hk
    intro g
    have hc : (Fintype.card ↥(Ξ k) : ℝ) ≤ L k := by simpa only [Fintype.card_coe] using hk
    have hb : (Fintype.card ↥(Ξ k) : ℝ) * (5000 * 111 ^ 3) * K k / P k ≤ 1 / (100 * K k) := by
      calc
        _ ≤ L k * C * K k / P k := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by norm_num [C])) (hKp k).le)
          (hPp k).le
        _ = _ := by dsimp only [P,C]; field_simp [(hKp k).ne',(hLp k).ne'] <;> ring
    calc
      _ ≤ ENNReal.ofReal ((Fintype.card ↥(Ξ k) : ℝ) * (5000 * 111 ^ 3) * K k / P k) * θ k g Set.univ := hloss k g
      _ ≤ ENNReal.ofReal ((Fintype.card ↥(Ξ k) : ℝ) * (5000 * 111 ^ 3) * K k / P k) * 1 :=
        mul_le_mul' le_rfl (hθ k g)
      _ ≤ _ := by simpa only [mul_one] using ENNReal.ofReal_le_ofReal hb
  · intro k g r hr q b
    exact hfloor k g ⟨r,hr⟩ q b

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
