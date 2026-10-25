import Submission.Obl.k4_finite_forest_width_selection.ForestCombinatorics
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

-- Adapted from this LOT tree, o119 session x0401, commit e544bb8d510e3a83494159a7c65049709823455a,
-- Submission/Obl/k4_finite_width_critical_contradiction/ForestWidthSelection.lean.

/-! Select common width bins throughout a finite forest, retaining all parents. -/
namespace Submission.Obl.k4_finite_forest_width_selection

open scoped BigOperators

/-- The number of bin vectors depends only on depth, width bound and accuracy.
The retained forest keeps a fixed fraction of the terminal mass at every level. -/
theorem forest_width_selection
    (m M : ℕ) (ε : ℝ) (hm : 0 < m) (hε : 0 < ε) :
    ∃ B : ℕ, 0 < B ∧
    ∀ (C : ℕ) (lev : Fin C → ℕ) (par : Fin C → Fin C)
      (width : Fin C → ℝ) (mass : Fin C → ENNReal) (r : ℕ → ℝ) (w q : ℝ),
    0 ≤ q → (∀ b, lev b < m ∧ |width b| ≤ (M : ℝ)) →
    (∀ b, 0 < lev b → lev (par b) + 1 = lev b) →
    (∀ b, mass b ≠ ⊤) →
    (∀ a, (∑ b, if 0 < lev b ∧ par b = a then mass b else 0) ≤ mass a) →
    0 < (∑ b, if lev b = m - 1 then mass b else 0) →
    (∀ b, (lev b = 0 → w * r 0 - q ≤ width b) ∧
      (0 < lev b → width (par b) + w * (r (lev b) - r (lev (par b))) - q ≤ width b)) →
    ∃ (C' : ℕ) (emb : Fin C' ↪ Fin C) (par' : Fin C' → Fin C') (nw : ℕ → ℝ),
    C' ≤ C ∧ (∀ b, 0 < lev (emb b) → emb (par' b) = par (emb b)) ∧
    (∀ b, |width (emb b) - nw (lev (emb b))| ≤ ε) ∧
    (∀ i, i < m → (∑ b, if lev b = m - 1 then mass b else 0) / (B : ENNReal) ≤
      ∑ b, if lev (emb b) = i then mass (emb b) else 0) ∧
    (∀ i, i < m → w * r i - (m : ℝ) * (q + 2 * ε) ≤ nw i ∧
      nw i + w * (r (m - 1) - r i) - (m : ℝ) * (q + 2 * ε) ≤ nw (m - 1)) := by
  classical
  obtain ⟨n, hn, center, bin, hbin⟩ := finite_forest_width_bins M hε
  refine ⟨n ^ m, pow_pos hn _, ?_⟩
  intro C lev par width mass r w q hq hbounds hpar hfinite hbudget hmass hwidth
  let Mode := Fin m → Fin n
  let color : Fin C → Mode := fun b i => bin (width (forestAncestor lev par b i))
  let good : Mode → Fin C → Prop := fun μ b =>
    ∀ i : Fin m, i.val ≤ lev b → color b i = μ i
  have hclosed : ∀ μ b, 0 < lev b → good μ b → good μ (par b) := by
    intro μ b hb hg i hi
    have hp := hpar b hb
    change bin (width (forestAncestor lev par (par b) i.val)) = μ i
    rw [forestAncestor_parent hpar b hb i.val hi]
    exact hg i (by omega)
  have hgood_leaf : ∀ μ b, lev b = m - 1 → (good μ b ↔ color b = μ) := by
    intro μ b hb
    constructor
    · intro hg
      exact funext fun i => hg i (by omega)
    · intro he i _
      exact congrFun he i
  let leafMass : ENNReal := ∑ b, if lev b = m - 1 then mass b else 0
  let modeMass : Mode → ENNReal := fun μ =>
    ∑ b, if lev b = m - 1 ∧ color b = μ then mass b else 0
  have hsum : ∑ μ, modeMass μ = leafMass := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : lev b = m - 1
    · simp only [hb, true_and, ite_true]
      exact Fintype.sum_ite_eq (color b) (fun _ : Mode => mass b)
    · simp [hb]
  have hleaf_finite : leafMass ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro b _
    split_ifs <;> simp_all only [ne_eq, ENNReal.zero_ne_top, not_false_eq_true]
  obtain ⟨μ, _, hμ⟩ :=
    Submission.Obl.k4_quadratic_atlas_normalization.exists_mass_ge_average
      Finset.univ modeMass leafMass.toReal
      ⟨(fun _ => ⟨0, hn⟩ : Mode), Finset.mem_univ _⟩
      (by rw [hsum, ENNReal.ofReal_toReal hleaf_finite])
  have hμ' : leafMass / (n ^ m : ℕ) ≤ modeMass μ := by
    simpa only [Finset.card_univ, Mode, Fintype.card_fun, Fintype.card_fin,
      ENNReal.ofReal_div_of_pos (by positivity : 0 < ((n ^ m : ℕ) : ℝ)),
      ENNReal.ofReal_toReal hleaf_finite, ENNReal.ofReal_natCast] using hμ
  have hmode : 0 < modeMass μ :=
    lt_of_lt_of_le (ENNReal.div_pos (ne_of_gt hmass) (by simp)) hμ'
  have hleaf : ∃ b, lev b = m - 1 ∧ good μ b := by
    by_contra! hnone
    have hzero : modeMass μ = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with hb
      · exact False.elim (hnone b hb.1 ((hgood_leaf μ b hb.1).mpr hb.2))
      · rfl
    exact (ne_of_gt hmode) hzero
  obtain ⟨leaf, hleaflev, hleafgood⟩ := hleaf
  let nw : ℕ → ℝ := fun i => if hi : i < m then center (μ ⟨i, hi⟩) else 0
  have hnwidth : ∀ b, good μ b → |width b - nw (lev b)| ≤ ε := by
    intro b hb
    have he := hb ⟨lev b, (hbounds b).1⟩ le_rfl
    have he' : bin (width b) = μ ⟨lev b, (hbounds b).1⟩ := by
      simpa only [color, forestAncestor_self] using he
    simpa only [nw, dif_pos (hbounds b).1, he'] using hbin (width b) (hbounds b).2
  let s := Finset.univ.filter (good μ)
  let e := s.orderEmbOfFin rfl
  have he_mem : ∀ b, good μ (e b) := by
    intro b
    exact (Finset.mem_filter.mp (s.orderEmbOfFin_mem rfl b)).2
  have he_surj : ∀ b, good μ b → ∃ b' : Fin s.card, e b' = b := by
    intro b hb
    have hbs : b ∈ (s : Set (Fin C)) := by simp [s, hb]
    rw [← s.range_orderEmbOfFin rfl] at hbs
    exact hbs
  let par' : Fin s.card → Fin s.card := fun b =>
    if hb : 0 < lev (e b) then
      Classical.choose (he_surj (par (e b)) (hclosed μ (e b) hb (he_mem b))) else b
  have hpar' : ∀ b, 0 < lev (e b) → e (par' b) = par (e b) := by
    intro b hb
    simpa only [par', dif_pos hb] using
      Classical.choose_spec (he_surj (par (e b)) (hclosed μ (e b) hb (he_mem b)))
  have hsum_e : ∀ i, (∑ b, if lev (e b) = i then mass (e b) else 0) =
      ∑ b, if good μ b ∧ lev b = i then mass b else 0 := by
    intro i
    calc
      _ = ∑ b ∈ Finset.univ.image e, if lev b = i then mass b else 0 := by
        rw [Finset.sum_image]
        exact fun _ _ _ _ h => e.injective h
      _ = _ := by
        rw [s.image_orderEmbOfFin_univ rfl]
        simp only [s, Finset.sum_filter, ite_and]
  refine ⟨s.card, e.toEmbedding, par', nw, ?_, hpar', fun b => hnwidth (e b) (he_mem b), ?_, ?_⟩
  · exact le_trans (Finset.card_le_univ s) (by simp)
  · intro i hi
    change leafMass / (n ^ m : ℕ) ≤ ∑ b, if lev (e b) = i then mass (e b) else 0
    rw [hsum_e i]
    have hmono := forest_layer_mass_antitone lev par mass (good μ) hpar (hclosed μ) hbudget
    apply hμ'.trans
    have heq : modeMass μ =
        ∑ b, if good μ b ∧ lev b = m - 1 then mass b else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : lev b = m - 1
      · simp only [modeMass, hb, and_true, true_and, hgood_leaf μ b hb]
      · simp only [hb, and_false, false_and, ite_false]
    rw [heq]
    exact hmono (by omega)
  · intro i hi
    let b := forestAncestor lev par leaf i
    have hb : lev b = i := forestAncestor_level hpar leaf i (by omega)
    have hb_good : good μ b := by
      have aux : ∀ j (a : Fin C), good μ a → j ≤ lev a → good μ (par^[j] a) := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          intro a ha hj
          have hp := hpar a (by omega)
          rw [Function.iterate_succ_apply]
          exact ih (par a) (hclosed μ a (by omega) ha) (by omega)
      exact aux _ leaf hleafgood (Nat.sub_le _ _)
    have hbi := hnwidth b hb_good
    rw [hb] at hbi
    have hbl := forest_width_lower hpar hwidth b
    rw [hb] at hbl
    have hfrom := forest_width_from_ancestor hpar (fun b => (hwidth b).2) leaf i (by omega)
    have hlwidth := hnwidth leaf hleafgood
    rw [hleaflev] at hlwidth hfrom
    have hiq : ((i : ℝ) + 1) * q ≤ (m : ℝ) * q :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hq
    have hmq : (((m - 1 - i : ℕ) : ℝ)) * q ≤ (m : ℝ) * q :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show m - 1 - i ≤ m by omega)) hq
    have hmε : ε ≤ (m : ℝ) * ε := by
      nlinarith only [hε, (show (1 : ℝ) ≤ m by exact_mod_cast hm)]
    constructor
    · nlinarith only [hbl, (abs_le.mp hbi).2, hiq, hmε, hε]
    · change width b + w * (r (m - 1) - r i) -
        (((m - 1 - i : ℕ) : ℝ)) * q ≤ width leaf at hfrom
      nlinarith only [hfrom, (abs_le.mp hbi).1, (abs_le.mp hlwidth).2, hmq, hmε]

end Submission.Obl.k4_finite_forest_width_selection
