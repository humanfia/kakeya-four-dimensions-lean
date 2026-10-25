-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Reduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Frostman
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Singleton

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file Reduction.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

/-- The exact output at a fixed scale, with the retained family indexed injectively. -/
def Output (ζ₁ ζ₂ ζ₃ δ θ : ℝ) {n : ℕ} (A : Fin n → Set Space) : Prop :=
  ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ δ ^ θ * n ≤ k ∧
    (SeparatedScales ζ₁ ζ₂ δ (fun j => A (g j)) ∨
      FlatPrisms ζ₂ ζ₃ δ (fun j => A (g j)))

/-- The geometric input still needed, restricted to families failing the easy KT case. -/
def ConcentratedCase (ξ ζ₁ ζ₂ ζ₃ ζ θ δ : ℝ) : Prop :=
  ∀ (n : ℕ) (x v : Fin n → Space),
    0 < n → (∀ i, ‖v i‖ = 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
    Distinct (fun i => Tube δ (x i) (v i)) →
    Frostman (δ ^ (-ζ)) (fun i => Tube δ (x i) (v i)) →
    (¬ ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧
      Sticky ξ δ (fun j => Tube δ (x (g j)) (v (g j)))) →
    (¬ KatzTao δ (δ ^ (-ζ₂)) (fun i => Tube δ (x i) (v i))) →
    Output ζ₁ ζ₂ ζ₃ δ θ (fun i => Tube δ (x i) (v i))

/-- The frozen trichotomy, using names for its predicates. -/
def Statement : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ∃ ζ₁ : ℝ, 0 < ζ₁ ∧
    ∀ ζ₂ ζ₃ : ℝ, 0 < ζ₃ → ζ₃ ≤ ζ₂ → ζ₂ ≤ ζ₁ →
      ∃ ζ : ℝ, 0 < ζ ∧ ∀ θ : ℝ, 0 < θ → ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∀ (n : ℕ) (x v : Fin n → Space), 0 < n → (∀ i, ‖v i‖ = 1) →
            (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
            Distinct (fun i => Tube δ (x i) (v i)) →
            Frostman (δ ^ (-ζ)) (fun i => Tube δ (x i) (v i)) →
            (¬ ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧
              Sticky ξ δ (fun j => Tube δ (x (g j)) (v (g j)))) →
            Output ζ₁ ζ₂ ζ₃ δ θ (fun i => Tube δ (x i) (v i))

/-- A fixed positive gap between the exponents absorbs the tube-volume constant. -/
lemma exists_absorption_scale {ζ ζ₂ : ℝ} (hgap : ζ < ζ₂) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      δ < 1 ∧ 384 * δ ^ (ζ₂ - ζ) ≤ 1 := by
  let a : ℝ := 1 / 384
  have ha : 0 < a := by norm_num [a]
  have hg : 0 < ζ₂ - ζ := sub_pos.mpr hgap
  let d := a ^ (1 / (ζ₂ - ζ))
  have hd : 0 < d := Real.rpow_pos_of_pos ha _
  have he : d ^ (ζ₂ - ζ) = a := by
    dsimp [d]
    rw [← Real.rpow_mul ha.le, one_div_mul_cancel hg.ne', Real.rpow_one]
  refine ⟨min (1 / 2) d, lt_min (by norm_num) hd, ?_⟩
  intro δ hδ hδd
  have hδhalf : δ ≤ 1 / 2 := hδd.trans (min_le_left _ _)
  have hh : δ ^ (ζ₂ - ζ) ≤ a := by
    rw [← he]
    exact Real.rpow_le_rpow hδ.le (hδd.trans (min_le_right _ _)) hg.le
  refine ⟨by linarith, ?_⟩
  calc
    384 * δ ^ (ζ₂ - ζ) ≤ 384 * a := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = 1 := by norm_num [a]

/-- All quantifier choices and the KT alternative reduce to the concentrated case. -/
theorem statement_of_concentrated_case
    (H : ∀ ξ : ℝ, 0 < ξ → ∃ ζ₁ : ℝ, 0 < ζ₁ ∧ ζ₁ ≤ 1 ∧
      ∀ ζ₂ ζ₃ : ℝ, 0 < ζ₃ → ζ₃ ≤ ζ₂ → ζ₂ ≤ ζ₁ →
        ∃ ζ : ℝ, 0 < ζ ∧ ζ < ζ₂ ∧
          ∀ θ : ℝ, 0 < θ → ∃ δ₀ : ℝ, 0 < δ₀ ∧
            ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ConcentratedCase ξ ζ₁ ζ₂ ζ₃ ζ θ δ) :
    Statement := by
  classical
  intro ξ hξ
  obtain ⟨ζ₁, hζ₁, hζ₁1, H₁⟩ := H ξ hξ
  refine ⟨ζ₁, hζ₁, ?_⟩
  intro ζ₂ ζ₃ hζ₃ h₃₂ h₂₁
  obtain ⟨ζ, hζ, hζ₂, H₂⟩ := H₁ ζ₂ ζ₃ hζ₃ h₃₂ h₂₁
  refine ⟨ζ, hζ, ?_⟩
  intro θ hθ
  obtain ⟨d, hd, Hd⟩ := exists_absorption_scale hζ₂
  obtain ⟨δ₀, hδ₀, H₃⟩ := H₂ θ hθ
  refine ⟨min δ₀ d, lt_min hδ₀ hd, ?_⟩
  intro δ hδ hδd n x v hn hv hball hsep hF hnot
  obtain ⟨hδ1, habsorb⟩ := Hd δ hδ (hδd.trans (min_le_right _ _))
  by_cases hKT : KatzTao δ (δ ^ (-ζ₂)) (fun i => Tube δ (x i) (v i))
  · have hB := separated_scales_of_frostman_and_katz_tao hδ hδ1 hζ₁1
      (hζ₃.le.trans h₃₂) habsorb x v hn hv hball hsep hF hKT
    refine ⟨n, id, Function.injective_id, ?_, Or.inl hB⟩
    exact mul_le_of_le_one_left (Nat.cast_nonneg n)
      (Real.rpow_le_one hδ.le hδ1.le hθ.le)
  · exact H₃ δ hδ (hδd.trans (min_le_left _ _)) n x v hn hv hball hsep hF hnot hKT

/-- The remaining geometric argument only needs exponents xi strictly between zero and two. -/
theorem statement_of_small_concentrated_case
    (H : ∀ ξ : ℝ, 0 < ξ → ξ < 2 → ∃ ζ₁ : ℝ, 0 < ζ₁ ∧ ζ₁ ≤ 1 ∧
      ∀ ζ₂ ζ₃ : ℝ, 0 < ζ₃ → ζ₃ ≤ ζ₂ → ζ₂ ≤ ζ₁ →
        ∃ ζ : ℝ, 0 < ζ ∧ ζ < ζ₂ ∧
          ∀ θ : ℝ, 0 < θ → ∃ δ₀ : ℝ, 0 < δ₀ ∧
            ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ConcentratedCase ξ ζ₁ ζ₂ ζ₃ ζ θ δ) :
    Statement := by
  apply statement_of_concentrated_case
  intro ξ hξ
  by_cases hξ2 : ξ < 2
  · exact H ξ hξ hξ2
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro ζ₂ ζ₃ hζ₃ h₃₂ h₂₁
    have hζ₂ : 0 < ζ₂ := hζ₃.trans_le h₃₂
    refine ⟨ζ₂ / 2, by positivity, by linarith, ?_⟩
    intro θ hθ
    refine ⟨1, by norm_num, ?_⟩
    intro δ hδ hδ1 n x v hn hv hball hsep hF hnot hKT
    exact (hnot (exists_sticky_subfamily_of_two_le hδ hδ1 (le_of_not_gt hξ2) x v hn hv)).elim

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
