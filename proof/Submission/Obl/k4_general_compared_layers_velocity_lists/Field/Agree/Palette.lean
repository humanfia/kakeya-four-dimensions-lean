-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.Palette; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254, session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Defs

/-!
# Palette counting for the coefficient-agreement step

* `Parent.agree_sum_pal3_le`: three-bin palette weights over any finite set of velocity bins sum
  to at most `3`;
* `agree_bin_le_pal3_of_fine`: conditional palette domination at a fine velocity mesh `χf` gives
  domination of a coarse bin (mesh `χ ≥ χf`) by its three-bin palette weight;
* `agree_sum_tagged_le`: summing a function of the velocity tag over labels with at most `B`
  choices per tag, whose intercept tags lie within `7` of a center, costs a factor `15 B`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A bin of mesh `χ` is the floor fiber. -/
theorem agree_mem_Ico_bin_iff {χ : ℝ} (hχ : 0 < χ) (b : ℤ) (x : ℝ) :
    x ∈ Ico ((b : ℝ) * χ) (((b : ℝ) + 1) * χ) ↔ ⌊x / χ⌋ = b := by
  rw [Int.floor_eq_iff, mem_Ico, le_div_iff₀ hχ, div_lt_iff₀ hχ]

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Three-bin palette weights over any finite set of velocity bins sum to at most `3`. -/
theorem agree_sum_pal3_le (k : ℕ) {χ : ℝ} (hχ : 0 < χ) [IsProbabilityMeasure (p.π k)]
    (S : Finset ℤ) :
    ∑ a ∈ S, p.agPal3 k χ a ≤ 3 := by
  classical
  have hshift : ∀ c : ℤ, ∑ a ∈ S, p.π k {x : ℝ | ⌊x / χ⌋ = a + c} ≤ 1 := by
    intro c
    rw [← measure_biUnion_finset]
    · exact prob_le_one
    · intro a _ a' _ hne
      exact Set.disjoint_left.mpr fun x hx hx' => hne (by
        have h := hx.symm.trans hx'
        omega)
    · intro a _
      exact measurableSet_eq_fun (measurable_id.div_const χ).floor measurable_const
  have hsplit : ∀ a : ℤ, p.agPal3 k χ a ≤ p.π k {x : ℝ | ⌊x / χ⌋ = a + (-1)} +
      p.π k {x : ℝ | ⌊x / χ⌋ = a + 0} + p.π k {x : ℝ | ⌊x / χ⌋ = a + 1} := by
    intro a
    unfold agPal3
    calc p.π k (Ico (((a : ℝ) - 1) * χ) (((a : ℝ) + 2) * χ))
        ≤ p.π k ({x : ℝ | ⌊x / χ⌋ = a + (-1)} ∪ {x : ℝ | ⌊x / χ⌋ = a + 0} ∪
            {x : ℝ | ⌊x / χ⌋ = a + 1}) := by
          apply measure_mono
          intro x hx
          obtain ⟨hlo, hhi⟩ := hx
          have h1 : ((a - 1 : ℤ) : ℝ) ≤ x / χ := by
            rw [le_div_iff₀ hχ]
            push_cast
            exact hlo
          have h2 : x / χ < ((a + 2 : ℤ) : ℝ) := by
            rw [div_lt_iff₀ hχ]
            push_cast
            exact hhi
          have hb1 : a - 1 ≤ ⌊x / χ⌋ := Int.le_floor.mpr h1
          have hb2 : ⌊x / χ⌋ < a + 2 := Int.floor_lt.mpr h2
          simp only [mem_union, mem_ofPred_eq]
          generalize ⌊x / χ⌋ = b at hb1 hb2 ⊢
          omega
      _ ≤ _ := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
  calc ∑ a ∈ S, p.agPal3 k χ a ≤ ∑ a ∈ S, (p.π k {x : ℝ | ⌊x / χ⌋ = a + (-1)} +
      p.π k {x : ℝ | ⌊x / χ⌋ = a + 0} + p.π k {x : ℝ | ⌊x / χ⌋ = a + 1}) :=
        Finset.sum_le_sum fun a _ => hsplit a
    _ = ∑ a ∈ S, p.π k {x : ℝ | ⌊x / χ⌋ = a + (-1)} +
        ∑ a ∈ S, p.π k {x : ℝ | ⌊x / χ⌋ = a + 0} +
        ∑ a ∈ S, p.π k {x : ℝ | ⌊x / χ⌋ = a + 1} := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 1 + 1 + 1 := add_le_add (add_le_add (hshift _) (hshift _)) (hshift _)
    _ = 3 := by norm_num

end Parent

/-- **Coarse bins from fine-bin domination.** Conditional palette domination at a fine
velocity mesh `χf` dominates a coarse bin of mesh `χ ≥ χf` by the palette weight of the three
coarse bins around it. -/
theorem agree_bin_le_pal3_of_fine {Ω : Type*} [MeasurableSpace Ω] (θ : Measure Ω) (π : Measure ℝ)
    (vel : Ω → ℝ) (A : Set Ω) {χ χf : ℝ} (hχf : 0 < χf) (hχ : χf ≤ χ)
    (C : ℝ≥0∞) (hdom : ∀ j : ℤ, θ (A ∩ {ω | ⌊vel ω / χf⌋ = j}) ≤ C * θ A * π {x | ⌊x / χf⌋ = j})
    (a : ℤ) :
    θ (A ∩ {ω | ⌊vel ω / χ⌋ = a}) ≤ C * θ A * π (Ico (((a : ℝ) - 1) * χ) (((a : ℝ) + 2) * χ)) := by
  classical
  have hχ0 : 0 < χ := lt_of_lt_of_le hχf hχ
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℤ,
      J = Finset.Icc ⌊(a : ℝ) * χ / χf⌋ ⌊((a : ℝ) + 1) * χ / χf⌋ := ⟨_, rfl⟩
  have hcover : A ∩ {ω | ⌊vel ω / χ⌋ = a} ⊆ ⋃ j ∈ J, (A ∩ {ω | ⌊vel ω / χf⌋ = j}) := by
    intro ω hω
    obtain ⟨hA, hωa⟩ := hω
    have hbin := (agree_mem_Ico_bin_iff hχ0 a (vel ω)).mpr hωa
    obtain ⟨hlo, hhi⟩ := hbin
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_prop]
    refine ⟨⌊vel ω / χf⌋, ?_, hA, rfl⟩
    rw [hJ, Finset.mem_Icc]
    constructor
    · exact Int.floor_le_floor (div_le_div_of_nonneg_right hlo hχf.le)
    · exact Int.floor_le_floor (div_le_div_of_nonneg_right hhi.le hχf.le)
  have hunion : (⋃ j ∈ J, {x : ℝ | ⌊x / χf⌋ = j}) ⊆
      Ico (((a : ℝ) - 1) * χ) (((a : ℝ) + 2) * χ) := by
    intro x hx
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop] at hx
    obtain ⟨j, hj, hxj⟩ := hx
    rw [hJ, Finset.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    have hxbin := (agree_mem_Ico_bin_iff hχf j x).mpr hxj
    obtain ⟨hxlo, hxhi⟩ := hxbin
    have hl1 : (a : ℝ) * χ / χf - 1 < (j : ℝ) := by
      have h0 := Int.sub_one_lt_floor ((a : ℝ) * χ / χf)
      have h' : ((⌊(a : ℝ) * χ / χf⌋ : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      linarith
    have hl2 : ((a : ℝ) * χ / χf - 1) * χf = (a : ℝ) * χ - χf := by
      rw [sub_mul, div_mul_cancel₀ _ hχf.ne', one_mul]
    have hl3 : (a : ℝ) * χ - χf < (j : ℝ) * χf := by
      rw [← hl2]
      exact mul_lt_mul_of_pos_right hl1 hχf
    have hu1 : (j : ℝ) ≤ ((a : ℝ) + 1) * χ / χf := by
      have h0 := Int.floor_le (((a : ℝ) + 1) * χ / χf)
      have h' : (j : ℝ) ≤ ((⌊((a : ℝ) + 1) * χ / χf⌋ : ℤ) : ℝ) := by exact_mod_cast hj2
      linarith
    have hu2 : (j : ℝ) * χf ≤ ((a : ℝ) + 1) * χ := by
      have h0 := mul_le_mul_of_nonneg_right hu1 hχf.le
      rwa [div_mul_cancel₀ _ hχf.ne'] at h0
    constructor
    · have he : ((a : ℝ) - 1) * χ = (a : ℝ) * χ - χ := by ring
      rw [he]
      linarith
    · have he : ((a : ℝ) + 2) * χ = ((a : ℝ) + 1) * χ + χ := by ring
      have he' : ((j : ℝ) + 1) * χf = (j : ℝ) * χf + χf := by ring
      rw [he]
      linarith
  calc θ (A ∩ {ω | ⌊vel ω / χ⌋ = a})
      ≤ θ (⋃ j ∈ J, (A ∩ {ω | ⌊vel ω / χf⌋ = j})) := measure_mono hcover
    _ ≤ ∑ j ∈ J, θ (A ∩ {ω | ⌊vel ω / χf⌋ = j}) := measure_biUnion_finset_le J _
    _ ≤ ∑ j ∈ J, C * θ A * π {x | ⌊x / χf⌋ = j} := Finset.sum_le_sum fun j _ => hdom j
    _ = C * θ A * ∑ j ∈ J, π {x | ⌊x / χf⌋ = j} := by rw [Finset.mul_sum]
    _ = C * θ A * π (⋃ j ∈ J, {x : ℝ | ⌊x / χf⌋ = j}) := by
        rw [measure_biUnion_finset]
        · intro j _ j' _ hne
          exact Set.disjoint_left.mpr (fun x hx hx' => hne (hx.symm.trans hx'))
        · intro j _
          exact measurableSet_eq_fun (measurable_id.div_const χf).floor measurable_const
    _ ≤ C * θ A * π (Ico (((a : ℝ) - 1) * χ) (((a : ℝ) + 2) * χ)) :=
        mul_le_mul' le_rfl (measure_mono hunion)

/-- **Tag counting.** Over labels with at most `B` choices per tag, whose intercept tag lies
within `7` of a center determined by the velocity tag, a sum of a function of the velocity tag
costs at most `15 B` per velocity tag. -/
theorem agree_sum_tagged_le {ι : Type*} [DecidableEq ι] (T : Finset ι) (tag : ι → Fin 2 → ℤ)
    (choices : (Fin 2 → ℤ) → Finset ι) (ctr : ℤ → ℤ) {B : ℝ} (hB : 0 ≤ B)
    (hcard : ∀ g, ((choices g).card : ℝ) ≤ B)
    (hmem : ∀ i ∈ T, i ∈ choices (tag i) ∧ |tag i 1 - ctr (tag i 0)| ≤ 7) (f : ℤ → ℝ≥0∞) :
    ∑ i ∈ T, f (tag i 0) ≤ ENNReal.ofReal (15 * B) * ∑ a ∈ T.image (fun i => tag i 0), f a := by
  rw [Finset.sum_comp f (fun i => tag i 0), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  show ((T.filter fun i => tag i 0 = a).card) • f a ≤ ENNReal.ofReal (15 * B) * f a
  rw [nsmul_eq_mul]
  refine mul_le_mul' ?_ le_rfl
  have hsub : T.filter (fun i => tag i 0 = a) ⊆
      (Finset.Icc (ctr a - 7) (ctr a + 7)).biUnion (fun b => choices ![a, b]) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hiT, hia⟩ := hi
    obtain ⟨hch, hctr⟩ := hmem i hiT
    rw [Finset.mem_biUnion]
    refine ⟨tag i 1, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      rw [hia] at hctr
      have h := abs_le.mp hctr
      constructor <;> linarith [h.1, h.2]
    · have htag : tag i = ![a, tag i 1] := by
        funext x
        fin_cases x <;> simp [hia]
      rw [← htag]
      exact hch
  have hc1 : ((T.filter (fun i => tag i 0 = a)).card : ℝ) ≤ 15 * B := by
    calc ((T.filter (fun i => tag i 0 = a)).card : ℝ)
        ≤ (((Finset.Icc (ctr a - 7) (ctr a + 7)).biUnion (fun b => choices ![a, b])).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ b ∈ Finset.Icc (ctr a - 7) (ctr a + 7), ((choices ![a, b]).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ b ∈ Finset.Icc (ctr a - 7) (ctr a + 7), B := Finset.sum_le_sum fun b _ => hcard _
      _ = 15 * B := by
          rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
          have h15 : (ctr a + 7 + 1 - (ctr a - 7)).toNat = 15 := by omega
          rw [h15]
          norm_num
  calc ((T.filter (fun i => tag i 0 = a)).card : ℝ≥0∞)
      = ENNReal.ofReal ((T.filter (fun i => tag i 0 = a)).card : ℝ) :=
        (ENNReal.ofReal_natCast _).symm
    _ ≤ ENNReal.ofReal (15 * B) := ENNReal.ofReal_le_ofReal hc1

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
