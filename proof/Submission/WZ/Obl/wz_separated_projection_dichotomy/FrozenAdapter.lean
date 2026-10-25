-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.FrozenAdapter.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.SetNonconcAdapter

/-!
Adapter from the frozen premise of `WangZahlLot.wz_separated_projection_dichotomy`
(Proposition 8.5 in counting form, as stated by the split of o103) to the
bounded set nonconcentration principle used by the Section 8.3 reduction.

The frozen premise only quantifies over `ε < 1` and `ζ < 1`; the principle
asks for `ε ≤ 1` and `ζ ≤ 1`.  Both are reached by running the frozen
statement at `min ε (1/2)` and `min ζ (1/2)`: a smaller `ζ` weakens the line
nonconcentration hypothesis, and a smaller `ε` strengthens the covering lower
bound once `δ ≤ 1`.
-/

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- The frozen Proposition 8.5 premise, verbatim. -/
def FrozenNonconcentratedStatement : Prop :=
∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ κ : ℝ, 0 < κ ∧ ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ α δ₀ : ℝ, 0 < α ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (F G G' : Set (EuclideanSpace ℝ (Fin 2))) (H : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Fr δ (δ ^ (-κ)) F → Fr δ (δ ^ (-κ)) G → Fr δ (δ ^ (-κ)) G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') → (∀ (e : EuclideanSpace ℝ (Fin 2)) (c r : ℝ), ‖e‖ = 1 → δ ≤ r → ({b ∈ G | |inner ℝ b e - c| < r}.ncard : ℝ) ≤ (δ ^ (-κ) * r) ^ ζ * G.ncard ∧ ({b ∈ G' | |inner ℝ b e - c| < r}.ncard : ℝ) ≤ (δ ^ (-κ) * r) ^ ζ * G'.ncard) → H ⊆ F ×ˢ (G ×ˢ G') → H.Nonempty → δ ^ α * F.ncard * G.ncard * G'.ncard ≤ H.ncard → ∀ (m : ℕ) (cc : Fin m → ℝ), {t : ℝ | ∃ h ∈ H, t = inner ℝ h.1 (h.2.1 - h.2.2)} ⊆ (⋃ j, Metric.closedBall (cc j) δ) → δ ^ (ε - 1) ≤ (m : ℝ)

/-- Lowering the exponent `ζ` keeps a relative line count bound valid. -/
theorem line_count_mono_exponent {δ ℓ ζ ζ' r : ℝ} {X : Set Plane}
    (hδ : 0 < δ) (hr : δ ≤ r) (hζ' : 0 < ζ') (hζζ : ζ' ≤ ζ) {N : ℝ} (hN : N ≤ (X.ncard : ℝ))
    (h : N ≤ (δ ^ (-ℓ) * r) ^ ζ * X.ncard) :
    N ≤ (δ ^ (-ℓ) * r) ^ ζ' * X.ncard := by
  have hx : 0 < δ ^ (-ℓ) * r := mul_pos (Real.rpow_pos_of_pos hδ _) (hδ.trans_le hr)
  have hXn : (0 : ℝ) ≤ X.ncard := Nat.cast_nonneg _
  rcases le_total (δ ^ (-ℓ) * r) 1 with hx1 | hx1
  · have hp : (δ ^ (-ℓ) * r) ^ ζ ≤ (δ ^ (-ℓ) * r) ^ ζ' :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 hζζ
    exact h.trans (mul_le_mul_of_nonneg_right hp hXn)
  · have hp : 1 ≤ (δ ^ (-ℓ) * r) ^ ζ' := Real.one_le_rpow hx1 hζ'.le
    calc N ≤ (X.ncard : ℝ) := hN
      _ = 1 * X.ncard := (one_mul _).symm
      _ ≤ (δ ^ (-ℓ) * r) ^ ζ' * X.ncard := mul_le_mul_of_nonneg_right hp hXn

theorem sep_ncard_le {X : Set Plane} (hX : X.Finite) (p : Plane → Prop) :
    (({x ∈ X | p x} : Set Plane).ncard : ℝ) ≤ (X.ncard : ℝ) := by
  exact_mod_cast Set.ncard_le_ncard (Set.sep_subset X p) hX

theorem boundedSetNonconcentratedPrinciple_of_frozen
    (h : FrozenNonconcentratedStatement) : BoundedSetNonconcentratedPrinciple := by
  intro ε hε _hε1
  have hε' : 0 < min ε (1 / 2) := lt_min hε (by norm_num)
  have hε'1 : min ε (1 / 2) < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨κ, hκ, hκP⟩ := h BoundedSetFrostman rfl (min ε (1 / 2)) hε' hε'1
  refine ⟨κ, hκ, ?_⟩
  intro ζ hζ _hζ1
  have hζ' : 0 < min ζ (1 / 2) := lt_min hζ (by norm_num)
  have hζ'1 : min ζ (1 / 2) < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨α, δ₀, hα, hδ₀, hP⟩ := hκP (min ζ (1 / 2)) hζ' hζ'1
  refine ⟨α, min δ₀ 1, hα, lt_min hδ₀ one_pos, ?_⟩
  intro δ hδ hδs F G U H hF hG hU hGl hUl hsep hH hHne hden
  have hδ1 : δ ≤ 1 := hδs.trans (min_le_right _ _)
  intro m c hc
  have hcov := hP δ hδ (hδs.trans (min_le_left _ _)) F G U H hF hG hU hsep
    (fun e a r he hr => ⟨line_count_mono_exponent hδ hr hζ' (min_le_left _ _)
        (sep_ncard_le hG.1 _) (hGl e a r he hr),
      line_count_mono_exponent hδ hr hζ' (min_le_left _ _)
        (sep_ncard_le hU.1 _) (hUl e a r he hr)⟩)
    hH hHne hden m c hc
  have hp : δ ^ (ε - 1) ≤ δ ^ (min ε (1 / 2) - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith [min_le_left ε (1 / 2)])
  exact hp.trans hcov

end WangZahlLot.Obl.wz_separated_projection_dichotomy
