/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/SequencePartitionFloors.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.FinitePartitionFloors
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth
import Submission.Obl.k4_tempered_grid_selection.SelectionMass

/-! One subpower stable-floor budget on a slowly growing finite family of grids. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped Classical BigOperators ENNReal

theorem exists_sequence_partition_floors {Ω C : Type*} [MeasurableSpace Ω]
    (N K H : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hH : (∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    (W : ℕ → ℕ) (μ : (k : ℕ) → Fin (W k) → Measure Ω)
    (A : (k : ℕ) → Fin (W k) → Set Ω)
    (hA : ∀ k g, MeasurableSet (A k g) ∧ μ k g (A k g) ≠ ∞)
    (Γ : ℕ → Finset ℝ) (code : ℕ → ℝ → Ω → C)
    (hcode : ∀ k r c, MeasurableSet {p | code k r p = c}) (d : ℝ)
    (hstage : ∀ᶠ k in atTop, ((Γ k).card : ℝ) ≤ H k ∧
      ∀ g, ∀ r ∈ Γ k, (code k r '' A k g).Finite ∧
        ((code k r '' A k g).ncard : ℝ) ≤ H k * N k ^ ((2 + d) * r)) :
    ∃ (P : ℕ → ℝ) (E : (k : ℕ) → Fin (W k) → Set Ω),
      ((∀ k, 1 ≤ P k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, P k ≤ N k ^ ε) ∧
      (∀ k g, MeasurableSet (E k g) ∧ E k g ⊆ A k g) ∧
      ∀ᶠ k in atTop, ∀ g, μ k g (A k g \ E k g) ≤ ENNReal.ofReal (1 / (100 * K k)) ∧
        ∀ r ∈ Γ k, ∀ p ∈ E k g,
          ENNReal.ofReal (N k ^ (-((2 + d) * r)) / P k) ≤
            μ k g (E k g ∩ {p' | code k r p' = code k r p}) := by
  have hN₁ (k) : 1 ≤ N k := by linarith [hN k]
  have hNpos (k) : 0 < N k := by linarith [hN k]
  have hKpos (k) : 0 < K k := zero_lt_one.trans_le (hK.1 k)
  have hHpos (k) : 0 < H k := zero_lt_one.trans_le (hH.1 k)
  let P := fun k => K k * (100 * H k ^ 2)
  have hP := Submission.Obl.k4_tempered_grid_selection.subpower_mul hNpos hK
    (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
      hN₁ hNt hH (by norm_num : (1 : ℝ) ≤ 100) 2)
  have hPpos (k) : 0 < P k :=
    mul_pos (hKpos k) (mul_pos (by norm_num) (sq_pos_of_pos (hHpos k)))
  let Q : ℕ → Prop := fun k => ((Γ k).card : ℝ) ≤ H k ∧
    ∀ g, ∀ r ∈ Γ k, (code k r '' A k g).Finite ∧
      ((code k r '' A k g).ncard : ℝ) ≤ H k * N k ^ ((2 + d) * r)
  have hexGood (k) (hk : Q k) (g : Fin (W k)) :
      ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ A k g ∧
        μ k g (A k g \ E) ≤ ENNReal.ofReal (1 / (100 * K k)) ∧
        ∀ r ∈ Γ k, ∀ p ∈ E,
          ENNReal.ofReal (N k ^ (-((2 + d) * r)) / P k) ≤
            μ k g (E ∩ {p' | code k r p' = code k r p}) := by
    let w : ↥(Γ k) → ℝ := fun r => N k ^ (-((2 + d) * r.val))
    have hcount (r : ↥(Γ k)) : ((code k r.val '' A k g).ncard : ℝ) * w r ≤ H k := by
      calc
        _ ≤ (H k * N k ^ ((2 + d) * r.val)) * w r :=
          mul_le_mul_of_nonneg_right (hk.2 g r.val r.property).2
            (Real.rpow_nonneg (hNpos k).le _)
        _ = H k := by dsimp [w]; rw [mul_assoc, ← Real.rpow_add (hNpos k)]; simp
    obtain ⟨E,hEm,hsub,hloss,hfloor⟩ := simultaneous_finite_partition_floors (μ k g) (A k g)
      (hA k g).1 (hA k g).2 (fun r : ↥(Γ k) => code k r.val)
      (fun r c => hcode k r.val c) (fun r => (hk.2 g r.val r.property).1) w
      (fun r => Real.rpow_nonneg (hNpos k).le _) (H k) (P k) (hHpos k).le (hPpos k) hcount
    have hbudget : (Fintype.card ↥(Γ k) : ℝ) * H k / P k ≤ 1 / (100 * K k) := by
      have hcard : (Fintype.card ↥(Γ k) : ℝ) ≤ H k := by simpa only [Fintype.card_coe] using hk.1
      calc
        _ ≤ H k * H k / P k := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcard (hHpos k).le) (hPpos k).le
        _ = _ := by dsimp [P]; field_simp [(hHpos k).ne', (hKpos k).ne']
    refine ⟨E,hEm,hsub,hloss.trans (ENNReal.ofReal_le_ofReal hbudget),?_⟩
    intro r hr p hp
    exact hfloor ⟨r,hr⟩ p hp
  have hex (k) (g : Fin (W k)) :
      ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ A k g ∧
        (Q k → μ k g (A k g \ E) ≤ ENNReal.ofReal (1 / (100 * K k)) ∧
          ∀ r ∈ Γ k, ∀ p ∈ E,
            ENNReal.ofReal (N k ^ (-((2 + d) * r)) / P k) ≤
              μ k g (E ∩ {p' | code k r p' = code k r p})) := by
    by_cases hk : Q k
    · obtain ⟨E,hm,hs,hl,hf⟩ := hexGood k hk g
      exact ⟨E,hm,hs,fun _ => ⟨hl,hf⟩⟩
    · exact ⟨∅,MeasurableSet.empty,Set.empty_subset _,fun hc => False.elim (hk hc)⟩
  choose E hEm hsub hvalid using hex
  exact ⟨P,E,hP,fun k g => ⟨hEm k g,hsub k g⟩,hstage.mono fun k hk g => hvalid k g hk⟩

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
