/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeCellSupport.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeCellLists
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeScalarEntry
import Submission.Lib.K4CommonLocalChoice

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory

noncomputable section

theorem chartR_abs_le_two {D : ℝ} {P Q : ℤ} {b : Fin 6 → ℝ} {t : ℝ}
    (hD : 0 < D) (hP : ⌊b 0 / D⌋ = P) (hQ : ⌊b 1 / D⌋ = Q)
    (ht : t ∈ Icc (0 : ℝ) 1) : |chartR D P Q b t| ≤ 2 := by
  have hp := normalized_parameter_mem_unit hD hP
  have hq := normalized_parameter_mem_unit hD hQ
  have htp₀ := mul_nonneg ht.1 hp.1
  have htp₁ := mul_le_mul ht.2 hp.2 hp.1 zero_le_one
  apply abs_le.mpr
  dsimp only [chartR, chartP, chartQ]
  constructor
  · calc
      -2 ≤ (b 1 - (Q : ℝ) * D) / D - 2 * (t * ((b 0 - (P : ℝ) * D) / D)) := by
        linarith only [hq.1, htp₁]
      _ = _ := by ring
  · calc
      _ = (b 1 - (Q : ℝ) * D) / D - 2 * (t * ((b 0 - (P : ℝ) * D) / D)) := by ring
      _ ≤ 2 := by linarith only [hq.2, htp₀]

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Turn actual original native contact lists into the finite scalar support
table. Each center is taken at a genuine contact, so no estimate on the free
constant coefficient of a native affine entry is used. -/
theorem NativeLevel.exists_scalar_cell_support {k : ℕ} {s₀ s D A σ w L C : ℝ}
    (child : cfg.NativeLevel k s) (H : Fin 6 → ℝ) (β : Fin 3 → ℝ)
    (P Q : ℤ) (v : ℝ)
    (choice : Fin (2 ^ cfg.T k s₀) → Option (Fin (cfg.n k s₀)))
    (E : Set (α × ℝ)) (value : α × ℝ → ℝ)
    (hD : 0 < D) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hw : 0 < w)
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hE : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1 ∧
      ⌊cfg.b k p.1 0 / D⌋ = P ∧ ⌊cfg.b k p.1 1 / D⌋ = Q)
    (hwitness : ∀ p ∈ E, ∃ z, cfg.namedNativeIncidence k s₀ s choice p z)
    (hcard : ∀ c, ((cfg.nativeCellEntries k s₀ s D σ P Q choice E c).card : ℝ) ≤ C)
    (hfit : ∀ p ∈ E, ∀ z,
      cfg.namedNativeIncidence k s₀ s choice p z →
      |value p - nativeScalarEntry H β (child.L z.2) D A
        ((P : ℝ) * D) ((Q : ℝ) * D) v p.2 (chartR D P Q (cfg.b k p.1) p.2)| ≤ L * w)
    (hvariation : ∀ (i : Fin (cfg.n k s)) t t' R R',
      t ∈ Icc (0 : ℝ) 1 → t' ∈ Icc (0 : ℝ) 1 → |R| ≤ 4 → |R'| ≤ 4 →
      |t - t'| ≤ 2 * σ → |R - R'| ≤ 2 * σ →
      |nativeScalarEntry H β (child.L i) D A ((P : ℝ) * D) ((Q : ℝ) * D) v t R -
        nativeScalarEntry H β (child.L i) D A ((P : ℝ) * D) ((Q : ℝ) * D) v t' R'| ≤ w) :
    ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      (F.card : ℝ) * σ ^ 2 ≤ 81 * C * (2 * L + 7) ∧
      ∀ p ∈ E, (chartCell D σ P Q (cfg.b k p.1) p.2, ⌊value p / w⌋) ∈ F := by
  classical
  let base := fun p : α × ℝ => (![p.2, chartR D P Q (cfg.b k p.1) p.2] : Fin 2 → ℝ)
  let code := fun p : α × ℝ => chartCell D σ P Q (cfg.b k p.1) p.2
  let S := cfg.nativeCellEntries k s₀ s D σ P Q choice E
  let entry := fun (i : Fin (cfg.n k s)) (p : α × ℝ) =>
    nativeScalarEntry H β (child.L i) D A ((P : ℝ) * D) ((Q : ℝ) * D) v
      p.2 (chartR D P Q (cfg.b k p.1) p.2)
  let center := fun c z => if hz : z ∈ S c then
    entry z.2 (Classical.choose (mem_nativeCellEntries.mp hz)) else 0
  have hbase : ∀ p ∈ E, ∀ e, |base p e| ≤ 2 := by
    intro p hp e
    fin_cases e
    · change |p.2| ≤ 2
      rw [abs_of_nonneg (hE p hp).1.1]
      exact (hE p hp).1.2.trans (by norm_num)
    · exact chartR_abs_le_two hD (hE p hp).2.1 (hE p hp).2.2 (hE p hp).1
  obtain ⟨B, hB, hBcover⟩ := exists_bounded_scalar_base_table hσ hσ1 (show (0 : ℝ) ≤ 2 by norm_num)
  have hcover : ∀ p ∈ E, code p ∈ B ∧ ∃ z ∈ S (code p), |value p - center (code p) z| ≤ (L + 1) * w := by
    intro p hp
    have hpB : code p ∈ B := by
      have hb := hBcover (base p) (hbase p hp)
      convert hb using 1
      ext e
      fin_cases e <;> rfl
    obtain ⟨z, hz⟩ := hwitness p hp
    have hzS : z ∈ S (code p) := mem_nativeCellEntries.mpr ⟨p, hp, rfl, hz⟩
    let p' := Classical.choose (mem_nativeCellEntries.mp hzS)
    have hp' := Classical.choose_spec (mem_nativeCellEntries.mp hzS)
    have hp'E : p' ∈ E := hp'.1
    have hsame : Submission.Lib.K4CommonLocalChoice.cell σ (base p) =
        Submission.Lib.K4CommonLocalChoice.cell σ (base p') := by
      have he : code p = code p' := hp'.2.1.symm
      ext e
      fin_cases e
      · change ⌊p.2 / σ⌋ = ⌊p'.2 / σ⌋
        exact congrFun he 0
      · change ⌊chartR D P Q (cfg.b k p.1) p.2 / σ⌋ =
          ⌊chartR D P Q (cfg.b k p'.1) p'.2 / σ⌋
        exact congrFun he 1
    have hdist := Submission.Lib.K4CommonLocalChoice.norm_sub_lt_of_cell_eq hσ hsame
    have hd₀ : |p.2 - p'.2| ≤ 2 * σ := by
      have hh := norm_le_pi_norm (base p - base p') 0
      change |p.2 - p'.2| ≤ _ at hh
      linarith
    have hd₁ : |chartR D P Q (cfg.b k p.1) p.2 - chartR D P Q (cfg.b k p'.1) p'.2| ≤ 2 * σ := by
      have hh := norm_le_pi_norm (base p - base p') 1
      change |chartR D P Q (cfg.b k p.1) p.2 - chartR D P Q (cfg.b k p'.1) p'.2| ≤ _ at hh
      linarith
    have hvar : |entry z.2 p - entry z.2 p'| ≤ w := hvariation z.2 _ _ _ _
      (hE p hp).1 (hE p' hp'E).1 ((hbase p hp 1).trans (by norm_num))
      ((hbase p' hp'E 1).trans (by norm_num)) hd₀ hd₁
    have hfit' := hfit p hp z hz
    refine ⟨hpB, z, hzS, ?_⟩
    change |value p - (if hz : z ∈ S (code p) then
      entry z.2 (Classical.choose (mem_nativeCellEntries.mp hz)) else 0)| ≤ _
    rw [dite_eq_left hzS]
    exact (abs_sub_le (value p) (entry z.2 p) (entry z.2 p')).trans
      (by nlinarith)
  obtain ⟨F, hF, hFcover⟩ := exists_scalar_support_of_entry_lists B S center code value E hw
    (show 0 ≤ L + 1 by linarith) (fun c _ => hcard c) hcover
  refine ⟨F, ?_, hFcover⟩
  calc
    _ ≤ (B.card : ℝ) * C * (2 * (L + 1) + 5) * σ ^ 2 :=
      mul_le_mul_of_nonneg_right hF (sq_nonneg _)
    _ = ((B.card : ℝ) * σ ^ 2) * C * (2 * L + 7) := by ring
    _ ≤ 81 * C * (2 * L + 7) := by
      have hb : (B.card : ℝ) * σ ^ 2 ≤ 81 := by norm_num at hB ⊢; exact hB
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hC) (by positivity)

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
