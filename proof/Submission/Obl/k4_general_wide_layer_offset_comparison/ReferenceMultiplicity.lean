import Mathlib

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open scoped ENNReal

noncomputable section

/-- A finite table with bounded fibers charges the original source weights
only by that multiplicity, independently of the number of table entries. -/
theorem sum_reference_le_of_fiber_card {E Q : Type*} [DecidableEq E] [DecidableEq Q]
    (s : Finset E) (keys : Finset Q) (key : E → Q)
    (hkey : ∀ e ∈ s, key e ∈ keys) (w : Q → ℝ≥0∞) {C : ℝ}
    (hcard : ∀ q ∈ keys, ((s.filter (fun e => key e = q)).card : ℝ) ≤ C) :
    (∑ e ∈ s, w (key e)) ≤ ENNReal.ofReal C * ∑ q ∈ keys, w q := by
  classical
  calc
    _ = ∑ q ∈ keys, ∑ e ∈ s.filter (fun e => key e = q), w (key e) :=
      (Finset.sum_fiberwise_of_maps_to hkey _).symm
    _ = ∑ q ∈ keys, ((s.filter (fun e => key e = q)).card : ℝ≥0∞) * w q := by
      apply Finset.sum_congr rfl
      intro q hq
      calc
        _ = ∑ _e ∈ s.filter (fun e => key e = q), w q := by
          apply Finset.sum_congr rfl
          intro e he
          rw [(Finset.mem_filter.mp he).2]
        _ = _ := by simp
    _ ≤ ∑ q ∈ keys, ENNReal.ofReal C * w q := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul' _ le_rfl
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (hcard q hq)
    _ = _ := (Finset.mul_sum ..).symm

/-- Two coordinate menus bound the size of a table whose full labels are
injective. The first menu is allowed to depend on the other coordinate. -/
theorem card_le_two_coordinate_menus {E P I : Type*}
    [DecidableEq E] [DecidableEq P] [DecidableEq I]
    (s : Finset E) (parent : E → P) (coarse : E → I)
    (hinj : Set.InjOn (fun e => (parent e, coarse e)) s)
    (parents : Finset P) (choices : P → Finset I)
    (hparent : ∀ e ∈ s, parent e ∈ parents)
    (hcoarse : ∀ e ∈ s, coarse e ∈ choices (parent e))
    {A B : ℝ} (hA : 0 ≤ A)
    (hchoices : ∀ Q ∈ parents, ((choices Q).card : ℝ) ≤ A)
    (hparents : (parents.card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ A * B := by
  classical
  let image := s.image (fun e => (parent e, coarse e))
  have hsub : image ⊆ parents.biUnion (fun Q => (choices Q).image (fun i => (Q, i))) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_biUnion.mpr ⟨parent e, hparent e he,
      Finset.mem_image.mpr ⟨coarse e, hcoarse e he, rfl⟩⟩
  have hcard : s.card ≤ ∑ Q ∈ parents, (choices Q).card := by
    calc
      s.card = image.card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (parents.biUnion (fun Q => (choices Q).image (fun i => (Q, i)))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ Q ∈ parents, ((choices Q).image (fun i => (Q, i))).card := Finset.card_biUnion_le
      _ ≤ ∑ Q ∈ parents, (choices Q).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_image_le
  calc
    (s.card : ℝ) ≤ ∑ Q ∈ parents, ((choices Q).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _Q ∈ parents, A := Finset.sum_le_sum fun Q hQ => hchoices Q hQ
    _ = (parents.card : ℝ) * A := by simp
    _ ≤ B * A := mul_le_mul_of_nonneg_right hparents hA
    _ = A * B := mul_comm _ _

/-- Coarse menus and the reverse true-parent count charge every compared
entry to its original fine slice with multiplicity at most `A * B`. -/
theorem compared_entry_reference_budget {E P I J D Tag : Type*}
    [Fintype E] [Fintype P] [Fintype J]
    [DecidableEq E] [DecidableEq P] [DecidableEq I] [DecidableEq J]
    [DecidableEq D] [DecidableEq Tag]
    (parent : E → P) (coarse : E → I) (fine : E → J) (domain : E → D)
    (coarseTag : I → Tag) (fineTag : J → Tag)
    (hinj : Function.Injective (fun e => (parent e, coarse e, fine e, domain e)))
    (htags : ∀ e, coarseTag (coarse e) = fineTag (fine e))
    (choices : P → Tag → Finset I)
    (hmem : ∀ e, coarse e ∈ choices (parent e) (coarseTag (coarse e)))
    {A B : ℝ} (hA : 0 ≤ A)
    (hchoices : ∀ Q tag, ((choices Q tag).card : ℝ) ≤ A)
    (hreverse : ∀ tag d j,
      ((Finset.univ.filter (fun Q : P => ∃ e,
        parent e = Q ∧ coarseTag (coarse e) = tag ∧ domain e = d ∧ fine e = j)).card : ℝ) ≤ B)
    (domains : J → Finset D) (hdom : ∀ e, domain e ∈ domains (fine e))
    (w : J → D → ℝ≥0∞) :
    (∑ e, w (fine e) (domain e)) ≤
      ENNReal.ofReal (A * B) * ∑ j, ∑ d ∈ domains j, w j d := by
  classical
  let keys : Finset (Σ _ : J, D) := Finset.univ.sigma domains
  let key : E → (Σ _ : J, D) := fun e => ⟨fine e, domain e⟩
  have hkey : ∀ e ∈ (Finset.univ : Finset E), key e ∈ keys := by
    intro e _
    exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hdom e⟩
  have hcard : ∀ q ∈ keys,
      ((Finset.univ.filter (fun e => key e = q)).card : ℝ) ≤ A * B := by
    intro q _
    let S := Finset.univ.filter (fun e => key e = q)
    have hread {e : E} (he : e ∈ S) : fine e = q.1 ∧ domain e = q.2 := by
      have hh := (Finset.mem_filter.mp he).2
      exact ⟨congrArg Sigma.fst hh, congrArg (fun x : (Σ _ : J, D) => x.2) hh⟩
    let parents : Finset P := Finset.univ.filter (fun Q => ∃ e,
      parent e = Q ∧ coarseTag (coarse e) = fineTag q.1 ∧ domain e = q.2 ∧ fine e = q.1)
    apply card_le_two_coordinate_menus S parent coarse ?_ parents
      (fun Q => choices Q (fineTag q.1)) ?_ ?_ hA
      (fun Q _ => hchoices Q _) (hreverse (fineTag q.1) q.2 q.1)
    · intro e he f hf hef
      apply hinj
      have hpar : parent e = parent f := congrArg (fun x : P × I => x.1) hef
      have hco : coarse e = coarse f := congrArg (fun x : P × I => x.2) hef
      simp only [hpar, hco, (hread he).1, (hread hf).1, (hread he).2, (hread hf).2]
    · intro e he
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, e, rfl, ?_, (hread he).2, (hread he).1⟩
      exact (htags e).trans (congrArg fineTag (hread he).1)
    · intro e he
      have hh := hmem e
      rw [(htags e).trans (congrArg fineTag (hread he).1)] at hh
      exact hh
  have hb := sum_reference_le_of_fiber_card Finset.univ keys key hkey
    (fun q => w q.1 q.2) hcard
  simpa only [keys, key, Finset.sum_sigma'] using hb

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
