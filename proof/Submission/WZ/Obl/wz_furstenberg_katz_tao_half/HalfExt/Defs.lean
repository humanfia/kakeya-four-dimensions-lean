-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.Defs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.FromKatzTao
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.LowRangeGeom

/-!
# Data of a failed bush estimate at `s = 1/2`

`HalfData r ε₀ η P D` collects, with finsets, the hypotheses of
`KatzTaoFurstenbergAt r (1/2) ε₀ η` together with the failure of its conclusion: every
`StripSep`-separated subfamily of `D` has fewer than `r ^ (-1 - ε₀)` elements.
`halfData_of_not` produces it from `¬ KatzTaoFurstenbergAt r (1/2) ε₀ η`.

This is the input of the extraction `HalfExtraction` (see `HalfBridge.lean` on x0505).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- The bush of `p` inside the label set `D`. -/
noncomputable def bushOf (D : Finset (E2 × E2)) (p : E2) : Finset E2 :=
  (D.filter (fun q => q.1 = p)).image Prod.snd

theorem mem_bushOf {D : Finset (E2 × E2)} {p e : E2} : e ∈ bushOf D p ↔ (p, e) ∈ D := by
  classical
  unfold bushOf
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
    have hq' := Finset.mem_filter.mp hq
    have : q = (p, q.2) := Prod.ext hq'.2 rfl
    rw [← this]; exact hq'.1
  · intro h
    exact Finset.mem_image.mpr ⟨(p, e), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

/-- Hypotheses of the bush estimate at `s = 1/2`, together with the failure of its
conclusion, in finset form. -/
structure HalfData (r ε₀ η : ℝ) (P : Finset E2) (D : Finset (E2 × E2)) : Prop where
  r_pos : 0 < r
  P_ne : P.Nonempty
  P_norm : ∀ p ∈ P, ‖p‖ ≤ 4
  P_sep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → r ≤ dist p p'
  P_card : r ^ (η - 1) ≤ (P.card : ℝ)
  P_kt : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
    ((P.filter (fun p => dist p x ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r)
  D_mem : ∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1
  D_card : ∀ p ∈ P, r ^ (η - 1 / 2) ≤ ((bushOf D p).card : ℝ)
  D_sep : ∀ p e e', (p, e) ∈ D → (p, e') ∈ D → e ≠ e' → r ≤ dist e e'
  D_kt : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
    (((bushOf D p).filter (fun e => dist e u ≤ ρ)).card : ℝ) ≤ r ^ (-η) * (ρ / r) ^ (1 / 2 : ℝ)
  few_lines : ∀ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → StripSep r q q') →
    (J.card : ℝ) < r ^ (-1 - ε₀)

theorem bushOf_filter_eq {D : Finset (E2 × E2)} {p u : E2} {ρ : ℝ} :
    (((bushOf D p).filter (fun e => dist e u ≤ ρ)) : Set E2) =
      {e | (p, e) ∈ D ∧ dist e u ≤ ρ} := by
  classical
  ext e
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_bushOf]

/-- The failure of `KatzTaoFurstenbergAt r (1/2) ε₀ η` gives `HalfData`. -/
theorem halfData_of_not {r ε₀ η : ℝ} (hr : 0 < r)
    (h : ¬ KatzTaoFurstenbergAt r (1 / 2) ε₀ η) :
    ∃ (P : Finset E2) (D : Finset (E2 × E2)), HalfData r ε₀ η P D := by
  classical
  unfold KatzTaoFurstenbergAt at h
  push Not at h
  obtain ⟨P, D, hPfin, hPne, hDfin, hP4, hPsep, hPcard, hPkt, hDmem, hDcard, hDsep, hDkt,
    hfail⟩ := h
  refine ⟨hPfin.toFinset, hDfin.toFinset, ?_⟩
  have hbush : ∀ p : E2, ((bushOf hDfin.toFinset p : Finset E2) : Set E2) = {e | (p, e) ∈ D} := by
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
    rw [Set.ncard_coe_finset] at h1
    have : -(2 * (1 / 2 : ℝ)) - ε₀ = -1 - ε₀ := by ring
    rwa [this] at h1

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
