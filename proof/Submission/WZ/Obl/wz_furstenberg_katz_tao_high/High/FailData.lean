-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.FailData.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/FailData.lean (064b94b).
-- Adapted from local obligation o157, branch x0675, commit c7aca52cd124.
-- Source: High/FailData.lean. Own namespaces renamed; shared definitions imported from accepted o213.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Defs
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Multiscale.PowerRegularization

/-!
# Data of a failed bush estimate at a general exponent, and its regularization

`FailData r s ε₀ η P D` is `HalfData` (x0538, `HalfExt/Defs.lean`) with the exponent `1/2`
replaced by an arbitrary `s`: the finset form of the hypotheses of
`KatzTaoFurstenbergAt r s ε₀ η` together with the failure of its conclusion.
`failData_of_not` produces it from `¬ KatzTaoFurstenbergAt r s ε₀ η`.

`FailData.regularize`: for a bounded number of arbitrary partition maps of the labels
(cells, arcs, assigned lines, ... at any scales), a subfamily `S ⊆ D` with
`|S| ≥ r ^ ε |D|` balances all of them and the bushes (`Prod.fst`), and is again
`FailData` with `η` replaced by `3 η + 2 ε`. It uses x0572's
`regularize_finite_partitions_power`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

/-- Hypotheses of the bush estimate at exponent `s`, together with the failure of its
conclusion, in finset form. -/
structure FailData (r s ε₀ η : ℝ) (P : Finset E2) (D : Finset (E2 × E2)) : Prop where
  r_pos : 0 < r
  P_ne : P.Nonempty
  P_norm : ∀ p ∈ P, ‖p‖ ≤ 4
  P_sep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → r ≤ dist p p'
  P_card : r ^ (η - 1) ≤ (P.card : ℝ)
  P_kt : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
    ((P.filter (fun p => dist p x ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r)
  D_mem : ∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1
  D_card : ∀ p ∈ P, r ^ (η - s) ≤ ((bushOf D p).card : ℝ)
  D_sep : ∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e'
  D_kt : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
    (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r) ^ s
  few_lines : ∀ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → StripSep r q q') →
    (J.card : ℝ) < r ^ (-(2 * s) - ε₀)

/-- The failure of `KatzTaoFurstenbergAt r s ε₀ η` gives `FailData`. -/
theorem failData_of_not {r s ε₀ η : ℝ} (hr : 0 < r)
    (h : ¬ KatzTaoFurstenbergAt r s ε₀ η) :
    ∃ (P : Finset E2) (D : Finset (E2 × E2)), FailData r s ε₀ η P D := by
  classical
  unfold KatzTaoFurstenbergAt at h
  push Not at h
  obtain ⟨P, D, hPfin, hPne, hDfin, hP4, hPsep, hPcard, hPkt, hDmem, hDcard, hDsep, hDkt,
    hfail⟩ := h
  refine ⟨hPfin.toFinset, hDfin.toFinset, ?_⟩
  have hbush : ∀ p : E2, ((bushOf hDfin.toFinset p : Finset E2) : Set E2) =
      {e | (p, e) ∈ D} := by
    intro p
    ext e
    simp [mem_bushOf]
  refine ⟨hr, by simpa using hPne, fun p hp => hP4 p (by simpa using hp),
    fun p hp p' hp' hne => hPsep p (by simpa using hp) p' (by simpa using hp') hne, ?_, ?_,
    fun q hq => by simpa using hDmem q (by simpa using hq), ?_, ?_, ?_, ?_⟩
  · rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    exact hPcard
  · intro x ρ hρ
    have h1 := hPkt x ρ hρ
    have heq : ((hPfin.toFinset.filter (fun p => dist p x ≤ ρ)) : Set E2) =
        P ∩ Metric.closedBall x ρ := by
      ext y; simp [Metric.mem_closedBall]
    rw [← Set.ncard_coe_finset, heq]
    exact h1
  · intro p hp
    have h1 := hDcard p (by simpa using hp)
    rw [← Set.ncard_coe_finset, hbush]
    exact h1
  · intro p e e' he he' hne
    exact hDsep p e e' (by simpa using he) (by simpa using he') hne
  · intro p hp u hu ρ hρ
    have h1 := hDkt p (by simpa using hp) u hu ρ hρ
    rw [← Set.ncard_coe_finset, bushOf_filter_eq]
    simpa using h1
  · intro J hJ hsep
    have hJsub : (↑J : Set (E2 × E2)) ⊆ D := fun q hq => by simpa using hJ hq
    have hJsep : ∀ q ∈ (↑J : Set (E2 × E2)), ∀ q' ∈ (↑J : Set (E2 × E2)), q ≠ q' →
        (r ≤ dist q.2 q'.2 ∧ r ≤ dist q.2 (-q'.2)) ∨ r ≤ |inner ℝ (q.1 - q'.1) q.2| :=
      fun q hq q' hq' hne => hsep q hq q' hq' hne
    have h1 := hfail _ hJsub hJsep
    rwa [Set.ncard_coe_finset] at h1

/-- The bush of `p` has the cardinality of the fiber of `Prod.fst` over `p`. -/
theorem card_bushOf (D : Finset (E2 × E2)) (p : E2) :
    (bushOf D p).card = (D.filter (fun q => q.1 = p)).card := by
  classical
  unfold bushOf
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  exact Prod.ext (ha'.trans hb'.symm) hab

/-- A label set lying over `P` has as many labels as the sum of its bushes. -/
theorem card_eq_sum_bushOf {P : Finset E2} {D : Finset (E2 × E2)}
    (hD : ∀ q ∈ D, q.1 ∈ P) :
    (D.card : ℝ) = ∑ p ∈ P, ((bushOf D p).card : ℝ) := by
  classical
  have h1 : D.card = ∑ p ∈ P, (D.filter (fun q => q.1 = p)).card :=
    Finset.card_eq_sum_card_fiberwise (fun q hq => hD q hq)
  rw [h1]
  push_cast
  apply Finset.sum_congr rfl
  intro p _
  rw [card_bushOf]

/-- A fixed unit vector. -/
theorem exists_unit_vector : ∃ u : E2, ‖u‖ = 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- Every bush has at most `r ^ (-η) * (2 / r) ^ s` directions. -/
theorem FailData.bush_le {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hr2 : r ≤ 2) {p : E2} (hp : p ∈ P) :
    ((bushOf D p).card : ℝ) ≤ r ^ (-η) * (2 / r) ^ s := by
  classical
  obtain ⟨u, hu⟩ := exists_unit_vector
  have hk := h.D_kt p hp u hu 2 hr2
  have hfil : (bushOf D p).filter (fun e => dist e u ≤ 2) = bushOf D p := by
    apply Finset.filter_true_of_mem
    intro e he
    have he1 : ‖e‖ = 1 := (h.D_mem (p, e) (mem_bushOf.mp he)).2
    calc dist e u = ‖e - u‖ := dist_eq_norm e u
      _ ≤ ‖e‖ + ‖u‖ := norm_sub_le e u
      _ = 2 := by rw [he1, hu]; norm_num
  rwa [hfil] at hk

/-- The number of points is at most `4 r ^ (-η) / r`. -/
theorem FailData.P_card_le {r s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hr4 : r ≤ 4) :
    (P.card : ℝ) ≤ r ^ (-η) * (4 / r) := by
  classical
  have hk := h.P_kt 0 4 hr4
  have hfil : P.filter (fun p => dist p 0 ≤ 4) = P := by
    apply Finset.filter_true_of_mem
    intro p hp
    rw [dist_zero_right]
    exact h.P_norm p hp
  rwa [hfil] at hk

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
