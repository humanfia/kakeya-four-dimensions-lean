-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactIncidence.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.OrientedContactRank
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.RankedIncidence
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.BadFourCycles

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open scoped Classical
open WangZahlLot.Obl.wz_jet_close_pair_moment
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem same_orientation_of_decide_eq {a b c d s : ℝ}
    (hs : 0 < s) (hac : s ≤ |c - a|) (hbd : s ≤ |d - b|)
    (h : decide (a < c) = decide (b < d)) :
    (a < c ∧ b < d) ∨ (c < a ∧ d < b) := by
  have hacne : a ≠ c := by
    intro he
    rw [he, sub_self, abs_zero] at hac
    linarith
  have hbdne : b ≠ d := by
    intro he
    rw [he, sub_self, abs_zero] at hbd
    linarith
  by_cases ha : a < c
  · left
    exact ⟨ha, by simpa only [ha, decide_true, true_eq_decide_iff] using h⟩
  · right
    have hb : ¬b < d := by simpa only [ha, decide_false, false_eq_decide_iff] using h
    exact ⟨lt_of_le_of_ne (le_of_not_gt ha) hacne.symm,
      lt_of_le_of_ne (le_of_not_gt hb) hbdne.symm⟩

/-- A finite near-contact graph in one short window obeys the incidence
bound from canonical lens ranks. The exceptional cycles are paid by the
number of nearby contacts along each curve, with a square-root loss. -/
theorem incidence_le_of_near_contacts {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (hsep : ∀ i j, i ≠ j → 0 < dist (q i) (q j))
    (aIdx : α ↪ Fin n) (bIdx : β ↪ Fin n)
    (R : α → β → Prop) (tag : α → β → ℝ)
    {l u γ M δ η B s G : ℝ} {H ΔA ΔB : ℕ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hlu : l ≤ u) (hshort : u - l ≤ 1 / 10000)
    (hγ : 0 < γ) (hB : 1 < B) (hs : 0 < s)
    (hratio : 2 * M * B ≤ γ) (hslope : 4 * η ≤ γ * s) (hvalue : 8 * δ < γ * s ^ 2)
    (hwithinA : ∀ a a' t, t ∈ Icc l u →
      |deriv (deriv (g (aIdx a))) t - deriv (deriv (g (aIdx a'))) t| ≤ M)
    (hwithinB : ∀ b b' t, t ∈ Icc l u →
      |deriv (deriv (g (bIdx b))) t - deriv (deriv (g (bIdx b'))) t| ≤ M)
    (hcross : (∀ a b t, t ∈ Icc l u →
        γ ≤ deriv (deriv (g (aIdx a))) t - deriv (deriv (g (bIdx b))) t) ∨
      (∀ a b t, t ∈ Icc l u →
        γ ≤ deriv (deriv (g (bIdx b))) t - deriv (deriv (g (aIdx a))) t))
    (htag : ∀ a b, R a b → tag a b ∈ Icc l u)
    (hcontact : ∀ a b, R a b → NearContact δ η (g (aIdx a)) (g (bIdx b)) (tag a b))
    (hH : 1 ≤ H) (hG : 1 ≤ G)
    (hHA : ∀ a b, R a b → Fintype.card {b' // R a b' ∧ |tag a b - tag a b'| ≤ s} ≤ H)
    (hHB : ∀ a b, R a b → Fintype.card {a' // R a' b ∧ |tag a b - tag a' b| ≤ s} ≤ H)
    (hΔA : ∀ a, Fintype.card {b // R a b} ≤ ΔA)
    (hΔB : ∀ b, Fintype.card {a // R a b} ≤ ΔB)
    (hregA : (Fintype.card α : ℝ) * ΔA ≤ G * (∑ a, (Fintype.card {b // R a b} : ℝ)))
    (hregB : (Fintype.card β : ℝ) * ΔB ≤ G * (∑ a, (Fintype.card {b // R a b} : ℝ))) :
    (∑ a, (Fintype.card {b // R a b} : ℝ)) ≤
      8 * ((4 : ℝ) ^ (windowLensHeight B s l u + 1) + 1) * G * Real.sqrt (2 * H) *
        ((Fintype.card α : ℝ) + (Fintype.card β : ℝ)) *
        Real.sqrt ((Fintype.card α : ℝ) + (Fintype.card β : ℝ)) := by
  classical
  let rA : (Fin 2 ↪ α) → ℕ := fun e => windowLensRank g B s l u (aIdx (e 0)) (aIdx (e 1))
  let rB : (Fin 2 ↪ β) → ℕ := fun f => windowLensRank g B s l u (bIdx (f 0)) (bIdx (f 1))
  let colorA : (Fin 2 ↪ α) → β → Bool := fun e b => decide (tag (e 0) b < tag (e 1) b)
  let colorB : (Fin 2 ↪ β) → α → Bool := fun f a => decide (tag a (f 0) < tag a (f 1))
  let Bad : (Fin 2 ↪ α) → (Fin 2 ↪ β) → Prop := fun e f =>
    (∃ i, |tag (e i) (f 0) - tag (e i) (f 1)| ≤ s) ∨
    ∃ j, |tag (e 0) (f j) - tag (e 1) (f j)| ≤ s
  have hgapA (e : Fin 2 ↪ α) (f : Fin 2 ↪ β) (hb : ¬Bad e f) (i : Fin 2) :
      s ≤ |tag (e i) (f 1) - tag (e i) (f 0)| := by
    rw [abs_sub_comm]
    exact (lt_of_not_ge (fun h => hb (Or.inl ⟨i, h⟩))).le
  have hgapB (e : Fin 2 ↪ α) (f : Fin 2 ↪ β) (hb : ¬Bad e f) (j : Fin 2) :
      s ≤ |tag (e 1) (f j) - tag (e 0) (f j)| := by
    rw [abs_sub_comm]
    exact (lt_of_not_ge (fun h => hb (Or.inr ⟨j, h⟩))).le
  have hdistA (e : Fin 2 ↪ α) : 0 < dist (q (aIdx (e 0))) (q (aIdx (e 1))) :=
    hsep _ _ (fun h => (by decide : (0 : Fin 2) ≠ 1) (e.injective (aIdx.injective h)))
  have hdistB (f : Fin 2 ↪ β) : 0 < dist (q (bIdx (f 0))) (q (bIdx (f 1))) :=
    hsep _ _ (fun h => (by decide : (0 : Fin 2) ≠ 1) (f.injective (bIdx.injective h)))
  have hgoodA : ∀ e f, (∀ i j, R (e i) (f j)) →
      colorA e (f 0) = colorA e (f 1) → ¬Bad e f → rB f < rA e := by
    intro e f hR hcol hbad
    have horient := same_orientation_of_decide_eq hs (hgapB e f hbad 0) (hgapB e f hbad 1) hcol
    rcases hcross with hcross | hcross
    · exact windowLensRank_lt_of_same_orientation hg hjet
        (aIdx (e 0)) (aIdx (e 1)) (bIdx (f 0)) (bIdx (f 1))
        hl hu hshort (hdistA e) (hdistB f) (hwithinA (e 0) (e 1))
        hγ hB hs hratio hslope hvalue
        (htag _ _ (hR 0 0)) (htag _ _ (hR 0 1)) (htag _ _ (hR 1 0)) (htag _ _ (hR 1 1))
        horient (hcross _ _) (hcross _ _) (hcross _ _) (hcross _ _)
        (hcontact _ _ (hR 0 0)) (hcontact _ _ (hR 0 1))
        (hcontact _ _ (hR 1 0)) (hcontact _ _ (hR 1 1))
        (hgapA e f hbad 0) (hgapA e f hbad 1) (hgapB e f hbad 0) (hgapB e f hbad 1)
    · exact windowLensRank_lt_of_same_orientation_lower hg hjet
        (aIdx (e 0)) (aIdx (e 1)) (bIdx (f 0)) (bIdx (f 1))
        hl hu hshort (hdistA e) (hdistB f) (hwithinA (e 0) (e 1))
        hγ hB hs hratio hslope hvalue
        (htag _ _ (hR 0 0)) (htag _ _ (hR 0 1)) (htag _ _ (hR 1 0)) (htag _ _ (hR 1 1))
        horient (hcross _ _) (hcross _ _) (hcross _ _) (hcross _ _)
        (hcontact _ _ (hR 0 0)) (hcontact _ _ (hR 0 1))
        (hcontact _ _ (hR 1 0)) (hcontact _ _ (hR 1 1))
        (hgapA e f hbad 0) (hgapA e f hbad 1) (hgapB e f hbad 0) (hgapB e f hbad 1)
  have hcontact' a b (hR : R a b) : NearContact δ η (g (bIdx b)) (g (aIdx a)) (tag a b) := by
    simpa only [NearContact, abs_sub_comm] using hcontact a b hR
  have hgoodB : ∀ e f, (∀ i j, R (e i) (f j)) →
      colorB f (e 0) = colorB f (e 1) → ¬Bad e f → rA e < rB f := by
    intro e f hR hcol hbad
    have horient := same_orientation_of_decide_eq hs (hgapA e f hbad 0) (hgapA e f hbad 1) hcol
    rcases hcross with hcross | hcross
    · exact windowLensRank_lt_of_same_orientation_lower hg hjet
        (bIdx (f 0)) (bIdx (f 1)) (aIdx (e 0)) (aIdx (e 1))
        hl hu hshort (hdistB f) (hdistA e) (hwithinB (f 0) (f 1))
        hγ hB hs hratio hslope hvalue
        (htag _ _ (hR 0 0)) (htag _ _ (hR 1 0)) (htag _ _ (hR 0 1)) (htag _ _ (hR 1 1))
        horient (hcross _ _) (hcross _ _) (hcross _ _) (hcross _ _)
        (hcontact' _ _ (hR 0 0)) (hcontact' _ _ (hR 1 0))
        (hcontact' _ _ (hR 0 1)) (hcontact' _ _ (hR 1 1))
        (hgapB e f hbad 0) (hgapB e f hbad 1) (hgapA e f hbad 0) (hgapA e f hbad 1)
    · exact windowLensRank_lt_of_same_orientation hg hjet
        (bIdx (f 0)) (bIdx (f 1)) (aIdx (e 0)) (aIdx (e 1))
        hl hu hshort (hdistB f) (hdistA e) (hwithinB (f 0) (f 1))
        hγ hB hs hratio hslope hvalue
        (htag _ _ (hR 0 0)) (htag _ _ (hR 1 0)) (htag _ _ (hR 0 1)) (htag _ _ (hR 1 1))
        horient (hcross _ _) (hcross _ _) (hcross _ _) (hcross _ _)
        (hcontact' _ _ (hR 0 0)) (hcontact' _ _ (hR 1 0))
        (hcontact' _ _ (hR 0 1)) (hcontact' _ _ (hR 1 1))
        (hgapB e f hbad 0) (hgapB e f hbad 1) (hgapA e f hbad 0) (hgapA e f hbad 1)
  have hbad : (∑ f : Fin 2 ↪ β, ∑ e : Fin 2 ↪ α,
      if (∀ i j, R (e i) (f j)) ∧ Bad e f then (1 : ℝ) else 0) ≤
      (2 * H : ℝ) * (∑ a, (Fintype.card {b // R a b} : ℝ)) * (ΔA + ΔB) := by
    have hb := card_four_cycles_close_times_le R tag s hHA hHB hΔA hΔB
    have hedge : Fintype.card {x : α × β // R x.1 x.2} =
        ∑ a, Fintype.card {b // R a b} := by
      rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype R), Fintype.card_sigma]
    have hsum : (Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
        (∀ i j, R (p.2 i) (p.1 j)) ∧ Bad p.2 p.1} : ℝ) =
        ∑ f : Fin 2 ↪ β, ∑ e : Fin 2 ↪ α,
          if (∀ i j, R (e i) (f j)) ∧ Bad e f then (1 : ℝ) else 0 := by
      calc
        _ = ∑ p : (Fin 2 ↪ β) × (Fin 2 ↪ α),
          if (∀ i j, R (p.2 i) (p.1 j)) ∧ Bad p.2 p.1 then (1 : ℝ) else 0 := by
            simp +instances only [Bad, Fin.forall_fin_two, Fin.exists_fin_two,
              Fintype.card_subtype, Finset.sum_boole]
        _ = _ := Fintype.sum_prod_type _
    rw [← hsum]
    change (Fintype.card _ : ℝ) ≤ _
    rw [hedge] at hb
    exact_mod_cast hb
  exact incidence_le_of_ranked_cycles R rA rB (windowLensHeight B s l u)
    (fun e => windowLensRank_le_height g hB hs hlu _ _)
    (fun f => windowLensRank_le_height g hB hs hlu _ _)
    colorA colorB Bad hgoodA hgoodB
    (by
      have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith) hG (by
        simpa +instances only [Bad, Fin.forall_fin_two, Fin.exists_fin_two] using hbad) hregA hregB

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
