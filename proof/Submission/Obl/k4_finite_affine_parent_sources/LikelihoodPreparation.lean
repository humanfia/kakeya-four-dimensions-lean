-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit cc2492748f08.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/LikelihoodPreparation.lean.
import Submission.Obl.k4_matching_palette_likelihood.Window
import Submission.Obl.k4_matching_palette_likelihood.Entropy
import Submission.Obl.k4_finite_affine_parent_sources.EntropyWindow
import Submission.Obl.k4_finite_affine_parent_sources.ReferencePruning

/-! Likelihood deletion for the unchanged prepared parent law. The entropy
estimate controls the total deleted mass; the retained joint numerators use
the original history masses and the original conditional palettes. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

open Finset Classical
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

private def finiteLabelCode (α : Type*) [Fintype α] : α → ℕ :=
  fun x => (Fintype.equivFin α x).val

private theorem finiteLabelCode_injective (α : Type*) [Fintype α] :
    Function.Injective (finiteLabelCode α) :=
  (Fin.val_injective).comp (Fintype.equivFin α).injective

private theorem posterior_code_eq
    {Ω H Z : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]
    [Fintype Z] [DecidableEq Z] (P : Ω → ℝ) (history : Ω → H) (palette : Ω → Z)
    (e : Ω) :
    Submission.Obl.k4_matching_palette_likelihood.posterior P
      (finiteLabelCode H ∘ history) (finiteLabelCode Z ∘ palette) e =
      condOwn P palette history e := by
  unfold Submission.Obl.k4_matching_palette_likelihood.posterior
    Submission.Obl.k4_matching_palette_likelihood.colorMass
    Submission.Obl.k4_matching_palette_likelihood.fiberMass
    condOwn atomMass fiberMass
  congr 1 <;> congr 1 <;> ext e' <;>
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply, Prod.mk.injEq,
      (finiteLabelCode_injective H).eq_iff, (finiteLabelCode_injective Z).eq_iff]

/-- The accepted likelihood-window estimate with arbitrary finite labels,
expressed in the same conditional-entropy convention as the path histories. -/
theorem finite_positive_log_window_le
    {Ω H Z : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]
    [Fintype Z] [DecidableEq Z]
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e) (hP1 : ∑ e, P e = 1)
    (coarse fine : Ω → H) (palette : Ω → Z)
    (hrefine : ∀ e e', fine e = fine e' → coarse e = coarse e') :
    (∑ e, P e * max 0 (Real.log (condOwn P palette fine e / condOwn P palette coarse e))) ≤
      negCondEnt P palette fine - negCondEnt P palette coarse + 1 := by
  have h := Submission.Obl.k4_matching_palette_likelihood.positive_log_window_le
    P (finiteLabelCode H ∘ coarse) (finiteLabelCode H ∘ fine)
    (finiteLabelCode Z ∘ palette) hP hP1 (by
      intro e e' he
      exact congrArg (finiteLabelCode H)
        (hrefine e e' ((finiteLabelCode_injective H) he)))
  simp only [Submission.Obl.k4_matching_palette_likelihood.entropy, posterior_code_eq] at h
  unfold negCondEnt
  linarith only [h]

/-- A likelihood cutoff removes at most the information increment plus one,
divided by the logarithmic cutoff. The conditional laws in the predicate are
always those of `P`, before any omission. -/
theorem finite_likelihood_restriction
    {Ω H Z : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype H] [DecidableEq H]
    [Fintype Z] [DecidableEq Z]
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e) (hP1 : ∑ e, P e = 1)
    (coarse fine : Ω → H) (palette : Ω → Z)
    (hrefine : ∀ e e', fine e = fine e' → coarse e = coarse e')
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ S : Finset Ω,
      1 - (negCondEnt P palette fine - negCondEnt P palette coarse + 1) / θ ≤
        ∑ e ∈ S, P e ∧
      ∀ e ∈ S, condOwn P palette fine e ≤ Real.exp θ * condOwn P palette coarse e := by
  let good : Ω → Prop := fun e =>
    condOwn P palette fine e ≤ Real.exp θ * condOwn P palette coarse e
  let S := univ.filter good
  let B := univ.filter (fun e => ¬ good e)
  have hpoint (e : Ω) (he : e ∈ B) :
      θ * P e ≤ P e * max 0 (Real.log (condOwn P palette fine e / condOwn P palette coarse e)) := by
    by_cases hz : P e = 0
    · simp only [hz, mul_zero, zero_mul, le_refl]
    have hpos : 0 < P e := lt_of_le_of_ne (hP e) (Ne.symm hz)
    have hc := condOwn_pos hP palette coarse hpos
    have hf := condOwn_pos hP palette fine hpos
    have hbad : Real.exp θ * condOwn P palette coarse e < condOwn P palette fine e :=
      lt_of_not_ge (mem_filter.mp he).2
    have hlog : θ < Real.log (condOwn P palette fine e / condOwn P palette coarse e) :=
      (Real.lt_log_iff_exp_lt (div_pos hf hc)).mpr ((lt_div_iff₀ hc).mpr hbad)
    have hbound := hlog.le.trans (le_max_right 0 _)
    simpa only [mul_comm θ] using mul_le_mul_of_nonneg_left hbound (hP e)
  have hbad : θ * (∑ e ∈ B, P e) ≤
      negCondEnt P palette fine - negCondEnt P palette coarse + 1 := by
    calc
      _ = ∑ e ∈ B, θ * P e := mul_sum _ _ _
      _ ≤ ∑ e ∈ B,
          P e * max 0 (Real.log (condOwn P palette fine e / condOwn P palette coarse e)) :=
        sum_le_sum fun e he => hpoint e he
      _ ≤ ∑ e,
          P e * max 0 (Real.log (condOwn P palette fine e / condOwn P palette coarse e)) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ B)
          (fun e _ _ => mul_nonneg (hP e) (le_max_left 0 _))
      _ ≤ _ := finite_positive_log_window_le P hP hP1 coarse fine palette hrefine
  have hpartition : (∑ e ∈ S, P e) + (∑ e ∈ B, P e) = 1 := by
    rw [← hP1]
    exact sum_filter_add_sum_filter_not univ good P
  refine ⟨S, ?_, fun e he => (mem_filter.mp he).2⟩
  have hbad' : (∑ e ∈ B, P e) ≤
      (negCondEnt P palette fine - negCondEnt P palette coarse + 1) / θ :=
    (le_div_iff₀ hθ).mpr (by simpa only [mul_comm θ] using hbad)
  linarith only [hpartition, hbad']

/-- A fixed conditional parent palette, computed before likelihood deletion. -/
def historyPalette {Ω H Z : Type*} [Fintype Ω] [DecidableEq H] [DecidableEq Z]
    (P : Ω → ℝ) (history : Ω → H) (palette : Ω → Z) (h : H) (z : Z) : ℝ :=
  fiberMass P (fun e => (history e, palette e)) (h, z) / fiberMass P history h

/-- Retaining only the good likelihood pairs gives a joint cap against the
original end-history masses. It does not replace the reference denominator
by a smaller postdeletion mass. -/
theorem likelihood_restriction_joint_cap
    {Ω H Z : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq H] [DecidableEq Z]
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e)
    (coarse fine : Ω → H) (parent : H → H) (palette : Ω → Z)
    (hrefine : ∀ e, coarse e = parent (fine e)) (S : Finset Ω) (K : ℝ) (hK : 0 ≤ K)
    (hgood : ∀ e ∈ S, condOwn P palette fine e ≤ K * condOwn P palette coarse e) :
    ∀ h z,
      fiberMass (fun e => if e ∈ S then P e else 0) (fun e => (fine e, palette e)) (h, z) ≤
        K * fiberMass P fine h * historyPalette P coarse palette (parent h) z := by
  intro h z
  have hsmall : fiberMass (fun e => if e ∈ S then P e else 0)
      (fun e => (fine e, palette e)) (h, z) ≤
      fiberMass P (fun e => (fine e, palette e)) (h, z) := by
    apply sum_le_sum
    intro e _
    split_ifs
    · rfl
    · exact hP e
  by_cases hex : ∃ e, e ∈ S ∧ fine e = h ∧ palette e = z
  · obtain ⟨e, heS, heh, hez⟩ := hex
    have hgood' := hgood e heS
    have hec : coarse e = parent h := by rw [hrefine, heh]
    simp only [condOwn, atomMass, heh, hez, hec] at hgood'
    by_cases hm : fiberMass P fine h = 0
    · have hsub : fiberMass P (fun e => (fine e, palette e)) (h, z) ≤ fiberMass P fine h :=
        finite_fiberMass_le_of_subset P hP _ _ _ _ (by
          intro e he
          exact (Prod.mk.inj he).1)
      rw [hm, mul_zero, zero_mul]
      exact hsmall.trans (hsub.trans_eq hm)
    · have hmpos : 0 < fiberMass P fine h :=
        lt_of_le_of_ne (fiberMass_nonneg hP fine h) (Ne.symm hm)
      have hj := (div_le_iff₀ hmpos).mp hgood'
      refine hsmall.trans (hj.trans_eq ?_)
      unfold historyPalette
      ring
  · have hz : fiberMass (fun e => if e ∈ S then P e else 0)
        (fun e => (fine e, palette e)) (h, z) = 0 := by
      apply sum_eq_zero
      intro e he
      have hkeys := Prod.mk.inj (mem_filter.mp he).2
      have heS : e ∉ S := fun heS => hex ⟨e, heS, hkeys.1, hkeys.2⟩
      simp only [heS, ite_false]
    rw [hz]
    exact mul_nonneg (mul_nonneg hK (fiberMass_nonneg hP fine h))
      (div_nonneg (fiberMass_nonneg hP _ _) (fiberMass_nonneg hP _ _))

/-- Selecting a low-information window and then deleting its large
likelihood ratios uses one fixed initial law for both operations. -/
theorem entropy_likelihood_window
    {Ω H Z : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype H] [DecidableEq H]
    [Fintype Z] [DecidableEq Z]
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e) (hP1 : ∑ e, P e = 1)
    (history : ℕ → Ω → H) (palette : Ω → Z)
    (hrefine : ∀ i e e', history (i + 1) e = history (i + 1) e' →
      history i e = history i e')
    {n : ℕ} (hn : 0 < n) (θ : ℝ) (hθ : 0 < θ) :
    ∃ i < n, ∃ S : Finset Ω,
      1 - (-negCondEnt P palette (history 0) / n + 1) / θ ≤ ∑ e ∈ S, P e ∧
      ∀ e ∈ S, condOwn P palette (history (i + 1)) e ≤
        Real.exp θ * condOwn P palette (history i) e := by
  obtain ⟨i, hi, hinc⟩ := entropy_window P hP palette history hn
  obtain ⟨S, hmass, hgood⟩ := finite_likelihood_restriction P hP hP1
    (history i) (history (i + 1)) palette (hrefine i) θ hθ
  refine ⟨i, hi, S, ?_, hgood⟩
  apply le_trans _ hmass
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_right _ hθ.le
  linarith only [hinc]

/-- Combining the entropy deletion with the joint numerator estimate. Every
later submeasure of the retained finite table has the same reference cap. -/
theorem finite_prepared_likelihood
    {Ω H Z : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype H] [DecidableEq H]
    [Fintype Z] [DecidableEq Z]
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e) (hP1 : ∑ e, P e = 1)
    (coarse fine : Ω → H) (parent : H → H) (palette : Ω → Z)
    (hrefine : ∀ e, coarse e = parent (fine e)) (θ : ℝ) (hθ : 0 < θ) :
    ∃ S : Finset Ω,
      1 - (negCondEnt P palette fine - negCondEnt P palette coarse + 1) / θ ≤
        ∑ e ∈ S, P e ∧
      ∀ Q : Ω → ℝ, (∀ e, Q e ≤ if e ∈ S then P e else 0) → ∀ h z,
        fiberMass Q (fun e => (fine e, palette e)) (h, z) ≤
          Real.exp θ * fiberMass P fine h * historyPalette P coarse palette (parent h) z := by
  obtain ⟨S, hmass, hgood⟩ := finite_likelihood_restriction P hP hP1
    coarse fine palette (fun e e' he => by rw [hrefine e, hrefine e', he]) θ hθ
  refine ⟨S, hmass, fun Q hQ h z => ?_⟩
  exact (sum_le_sum (fun e _ => hQ e)).trans
    (likelihood_restriction_joint_cap P hP coarse fine parent palette hrefine S
      (Real.exp θ) (Real.exp_pos θ).le hgood h z)

/-- The initial information budget depends only on the number of occupied
velocity values inside each starting history, rather than the source code's
possibly much larger cardinality. -/
theorem finite_entropy_card_upper
    {n M : ℕ} {H Z : Type*} [Fintype H] [DecidableEq H] [Fintype Z] [DecidableEq Z]
    (P : Fin n → ℝ) (hP : ∀ e, 0 ≤ P e) (hP1 : ∑ e, P e = 1)
    (history : Fin n → H) (palette : Fin n → Z) (hM : 1 ≤ M)
    (hcard : ∀ e,
      ((univ.filter (fun e' => 0 < P e' ∧ history e' = history e)).image palette).card ≤ M) :
    -negCondEnt P palette history ≤ Real.log M := by
  have hcard' (e : Fin n) :
      ((univ.filter (fun e' => 0 < P e' ∧
          (finiteLabelCode H ∘ history) e' = (finiteLabelCode H ∘ history) e)).image
        (finiteLabelCode Z ∘ palette)).card ≤ M := by
    have hfilter : univ.filter (fun e' => 0 < P e' ∧
        (finiteLabelCode H ∘ history) e' = (finiteLabelCode H ∘ history) e) =
        univ.filter (fun e' => 0 < P e' ∧ history e' = history e) := by
      ext e'
      simp only [mem_filter, mem_univ, true_and, Function.comp_apply,
        (finiteLabelCode_injective H).eq_iff]
    rw [hfilter, ← image_image, card_image_of_injective _ (finiteLabelCode_injective Z)]
    exact hcard e
  have h := Submission.Obl.k4_matching_palette_likelihood.neg_log_card_le_log_likelihood
    P (finiteLabelCode H ∘ history) (finiteLabelCode Z ∘ palette) hM hP hP1 hcard'
  change -Real.log M ≤ ∑ e, P e * Real.log
    (Submission.Obl.k4_matching_palette_likelihood.posterior P
      (finiteLabelCode H ∘ history) (finiteLabelCode Z ∘ palette) e) at h
  simp only [posterior_code_eq] at h
  unfold negCondEnt
  linarith only [h]

/-- A cardinality bound for the velocity palette gives an explicit
logarithmic information budget for the selected parent window. -/
theorem entropy_likelihood_window_of_palette_card
    {n M m : ℕ} {H Z : Type*} [Fintype H] [DecidableEq H] [Fintype Z] [DecidableEq Z]
    (P : Fin n → ℝ) (hP : ∀ e, 0 ≤ P e) (hP1 : ∑ e, P e = 1)
    (history : ℕ → Fin n → H) (palette : Fin n → Z)
    (hrefine : ∀ i e e', history (i + 1) e = history (i + 1) e' →
      history i e = history i e')
    (hM : 1 ≤ M) (hm : 0 < m)
    (hcard : ∀ e,
      ((univ.filter (fun e' => 0 < P e' ∧ history 0 e' = history 0 e)).image palette).card ≤ M)
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ i < m, ∃ S : Finset (Fin n),
      1 - (Real.log M / m + 1) / θ ≤ ∑ e ∈ S, P e ∧
      ∀ e ∈ S, condOwn P palette (history (i + 1)) e ≤
        Real.exp θ * condOwn P palette (history i) e := by
  obtain ⟨i, hi, S, hmass, hgood⟩ := entropy_likelihood_window
    P hP hP1 history palette hrefine hm θ hθ
  refine ⟨i, hi, S, ?_, hgood⟩
  apply le_trans _ hmass
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_right _ hθ.le
  have hbudget := div_le_div_of_nonneg_right
    (finite_entropy_card_upper P hP hP1 (history 0) palette hM hcard)
    (by positivity : (0 : ℝ) ≤ m)
  linarith only [hbudget]

end

end Submission.Obl.k4_finite_affine_parent_sources
