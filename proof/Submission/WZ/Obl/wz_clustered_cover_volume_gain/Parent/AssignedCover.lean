-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.AssignedCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.ToolkitJ

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor

open Finset MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped Classical

/-- The assigned-box output of Proposition 4.6, with one error constant throughout. -/
structure AssignedCover {N : ℕ} (R ρ K : ℝ) (y w : Fin N → Space)
    (U : Finset (Fin N)) (m a b : ℝ) (L : ℕ) (z : Fin L → Space)
    (e : Fin L → Space ≃ₗᵢ[ℝ] Space) (g : Fin N → Fin L) : Prop where
  coefficient_pos : 0 < m
  width : ρ ≤ a
  ordered : a ≤ b
  bounded : b ≤ 2 * R
  upper : ∀ W, Convex ℝ W → ENNReal.ofReal (((sub ρ y w U W).card : ℝ) * ρ ^ 2) ≤
    ENNReal.ofReal m * volume W
  covers : ∀ k ∈ U, tube ρ y w k ⊆ box a b (2 * R) (z (g k)) (e (g k))
  degree : ∀ k ∈ U,
    ((univ.filter fun i => tube ρ y w k ⊆ box a b (2 * R) (z i) (e i)).card : ℝ) ≤ K
  balanced : ∀ i i', ((U.filter fun k => g k = i).card : ℝ) ≤
    K * (U.filter fun k => g k = i').card
  rich : ∀ i, m * (a * b * (2 * R)) ≤ K * (((U.filter fun k => g k = i).card : ℝ) * ρ ^ 2)
  above : ∀ V, Convex ℝ V → ENNReal.ofReal
    (((univ.filter fun i => box a b (2 * R) (z i) (e i) ⊆ V).card : ℝ) *
      (a * b * (2 * R))) ≤ ENNReal.ofReal K * volume V
  below : ∀ i V, Convex ℝ V → ENNReal.ofReal
    ((U.filter fun k => g k = i ∧ tube ρ y w k ⊆ box a b (2 * R) (z i) (e i) ∩ V).card) *
      volume (box a b (2 * R) (z i) (e i)) ≤
    ENNReal.ofReal (K * (U.filter fun k => g k = i).card) *
      volume (box a b (2 * R) (z i) (e i) ∩ V)

theorem AssignedCover.mono {N L : ℕ} {R ρ K K' m a b : ℝ}
    {y w : Fin N → Space} {U : Finset (Fin N)} {z : Fin L → Space}
    {e : Fin L → Space ≃ₗᵢ[ℝ] Space} {g : Fin N → Fin L}
    (h : AssignedCover R ρ K y w U m a b L z e g) (hK : K ≤ K') :
    AssignedCover R ρ K' y w U m a b L z e g := by
  refine ⟨h.coefficient_pos, h.width, h.ordered, h.bounded, h.upper, h.covers,
    fun k hk => (h.degree k hk).trans hK, ?_, ?_, ?_, ?_⟩
  · intro i i'
    exact (h.balanced i i').trans (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _))
  · intro i
    exact (h.rich i).trans (mul_le_mul_of_nonneg_right hK (by positivity))
  · intro V hV
    exact (h.above V hV).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hK) _)
  · intro i V hV
    refine (h.below i V hV).trans ?_
    gcongr

theorem Fam.assigned_cover {N : ℕ} {R ρ : ℝ} {y w : Fin N → Space}
    (hF : Fam R ρ y w) (hR : 1 ≤ R) (hN : 0 < N) :
    ∃ (U : Finset (Fin N)) (m a b : ℝ) (L : ℕ) (z : Fin L → Space)
      (e : Fin L → Space ≃ₗᵢ[ℝ] Space) (g : Fin N → Fin L),
      (N : ℝ) ≤ 2 * Kc R N ρ ^ 3 * U.card ∧
      AssignedCover R ρ (2 * Kc R N ρ ^ 3) y w U m a b L z e g := by
  obtain ⟨U, m, a, b, L, z, e, g, hcard, hm, ha, hab, hb, hKT, hcov, hbal, hrich, hup, hlo⟩ :=
    hF.factor_assign hR hN
  have hK1 := Kc_one_le hR N ρ
  have hK13 : Kc R N ρ ≤ Kc R N ρ ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK1 (by norm_num : 1 ≤ 3)
  have hK23 : Kc R N ρ ^ 2 ≤ Kc R N ρ ^ 3 :=
    pow_le_pow_right₀ hK1 (by norm_num)
  refine ⟨U, m, a, b, L, z, e, g, hcard.trans ?_, hm, ha, hab, hb, hKT,
    fun k hk => (hcov k hk).1, ?_, ?_, hrich, ?_, ?_⟩
  · gcongr
  · intro k hk
    exact (hcov k hk).2.trans (by linarith)
  · intro i i'
    exact (hbal i i').trans (by gcongr)
  · intro V hV
    exact (hup V hV).trans (by gcongr; linarith)
  · intro i V hV
    exact (hlo i V hV).trans (by gcongr)

private theorem card_filter_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (j : α → β) (hj : Function.Injective j) (P : β → Prop) [DecidablePred P] :
    ((s.image j).filter P).card = (s.filter fun k => P (j k)).card := by
  classical
  rw [Finset.filter_image, Finset.card_image_of_injective _ hj]

/-- Proposition 4.6 applies directly to a selected coarse family, preserving the original
indexing and its complete fine fibers. All constants depend on the selected cardinality. -/
theorem Fam.assigned_cover_subset {N : ℕ} {R ρ : ℝ} {y w : Fin N → Space}
    (hF : Fam R ρ y w) (hR : 1 ≤ R) (Q : Finset (Fin N)) (hQ : Q.Nonempty) :
    ∃ (U : Finset (Fin N)) (m a b : ℝ) (L : ℕ) (z : Fin L → Space)
      (e : Fin L → Space ≃ₗᵢ[ℝ] Space) (g : Fin N → Fin L),
      U ⊆ Q ∧ U.Nonempty ∧ (Q.card : ℝ) ≤ 2 * Kc R Q.card ρ ^ 3 * U.card ∧
      AssignedCover R ρ (2 * Kc R Q.card ρ ^ 3) y w U m a b L z e g := by
  classical
  let j : Fin Q.card → Fin N := fun k => (Q.equivFin.symm k).1
  have hj : Function.Injective j := Subtype.val_injective.comp Q.equivFin.symm.injective
  have hjQ (k : Fin Q.card) : j k ∈ Q := (Q.equivFin.symm k).2
  obtain ⟨k₀, hk₀⟩ := hQ
  let r : Fin N → Fin Q.card := fun k =>
    if hk : k ∈ Q then Q.equivFin ⟨k, hk⟩ else Q.equivFin ⟨k₀, hk₀⟩
  have hrj (k : Fin Q.card) : r (j k) = k := by
    simp [r, hjQ, j]
  have hF' : Fam R ρ (y ∘ j) (w ∘ j) :=
    ⟨hF.pos, hF.le_one, fun k => hF.unit (j k), fun k => hF.inBall (j k)⟩
  obtain ⟨U', m, a, b, L, z, e, g', hcard, hcover⟩ :=
    hF'.assigned_cover hR (Finset.card_pos.mpr ⟨k₀, hk₀⟩)
  let U := U'.image j
  let g := g' ∘ r
  have hUg : ∀ k, g (j k) = g' k := by intro k; simp [g, hrj]
  have hUQ : U ⊆ Q := by
    intro k hk
    obtain ⟨k', -, rfl⟩ := Finset.mem_image.mp hk
    exact hjQ k'
  have hcardU : U.card = U'.card := Finset.card_image_of_injective _ hj
  have hU : U.Nonempty := by
    have hpos : (0 : ℝ) < Q.card := by exact_mod_cast (Finset.card_pos.mpr ⟨k₀, hk₀⟩)
    by_contra hn
    have hz : U.card = 0 := by simpa only [Finset.card_eq_zero] using Finset.not_nonempty_iff_eq_empty.mp hn
    rw [← hcardU, hz, Nat.cast_zero, mul_zero] at hcard
    linarith
  have hcnt (P : Fin N → Prop) [DecidablePred P] :
      (U.filter P).card = (U'.filter fun k => P (j k)).card :=
    card_filter_image U' j hj P
  have hsub (W : Set Space) : (sub ρ y w U W).card =
      (sub ρ (y ∘ j) (w ∘ j) U' W).card := hcnt _
  have hfib (i : Fin L) : (U.filter fun k => g k = i).card =
      (U'.filter fun k => g' k = i).card := by
    simpa only [hUg] using hcnt (fun k => g k = i)
  refine ⟨U, m, a, b, L, z, e, g, hUQ, hU, by simpa only [hcardU] using hcard,
    hcover.coefficient_pos, hcover.width, hcover.ordered, hcover.bounded, ?_, ?_, ?_,
    ?_, ?_, hcover.above, ?_⟩
  · intro W hW
    rw [hsub]
    exact hcover.upper W hW
  · intro k hk
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hk
    simpa only [hUg, tube, Function.comp_apply] using hcover.covers k' hk'
  · intro k hk
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hk
    exact hcover.degree k' hk'
  · intro i i'
    rw [hfib, hfib]
    exact hcover.balanced i i'
  · intro i
    rw [hfib]
    exact hcover.rich i
  · intro i V hV
    rw [hcnt (fun k => g k = i ∧ tube ρ y w k ⊆ box a b (2 * R) (z i) (e i) ∩ V), hfib]
    convert hcover.below i V hV using 1
    apply congrArg (fun s : Finset (Fin Q.card) =>
      ENNReal.ofReal (s.card : ℝ) * volume (box a b (2 * R) (z i) (e i)))
    apply Finset.filter_congr
    intro k _
    rw [hUg]
    rfl

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor
