-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.LowRange.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.LowRangeGeom
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.Maximal
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.Counting

/-!
# The low range of the Furstenberg bush estimate (Wolff's bush argument)

Let `J₁` be a maximal separated family of labels.  Some `j₀ ∈ J₁` is close to at
least `#D / #J₁` labels; their points lie near the line of `j₀`.  Take a maximal
`λ`-separated set of these points; through each, the normals of its bush that are
`ρ₀`-far from `± j₀.2`, made `r`-separated up to sign, give lines which are
pairwise separated (two of them through points `λ` apart would have to be nearly
parallel to the line of `j₀`).  Hence `#J₁ * #J' ≥ Nb ^ 2 / (8 KT ^ 2 F λ)`.

Ported from session x0394 (o141, commit d684c60).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

open scoped Classical

lemma low_range_arith {a d P0 Pn Dj Dn Jn Nb KT F lam : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hPn : 0 < Pn) (hNb : 0 < Nb) (hKT : 0 < KT) (hF : 0 < F) (hlam : 0 < lam)
    (h1 : Pn * Nb ≤ Dn) (h2 : Dn ≤ a * Dj) (h3 : Dj ≤ P0 * (2 * KT))
    (h4 : P0 ≤ d * (F * lam * Pn)) (h5 : d * (Nb / (4 * KT)) ≤ Jn) :
    Nb ^ 2 / (8 * KT ^ 2 * F * lam) ≤ a * Jn := by
  have k1 : a * Dj ≤ a * (P0 * (2 * KT)) := mul_le_mul_of_nonneg_left h3 ha
  have k2 : a * (P0 * (2 * KT)) ≤ a * ((d * (F * lam * Pn)) * (2 * KT)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 (by positivity)) ha
  have k3 : Pn * Nb ≤ Pn * (2 * KT * F * lam * (a * d)) := by nlinarith
  have k4 : Nb ≤ 2 * KT * F * lam * (a * d) := le_of_mul_le_mul_left k3 hPn
  have k5 : a * (d * (Nb / (4 * KT))) ≤ a * Jn := mul_le_mul_of_nonneg_left h5 ha
  have k6 : a * (d * (Nb / (4 * KT))) = (a * d) * Nb / (4 * KT) := by ring
  rw [k6, div_le_iff₀ (by positivity)] at k5
  have k8 : Nb * Nb ≤ (2 * KT * F * lam * (a * d)) * Nb := mul_le_mul_of_nonneg_right k4 hNb.le
  have k9 : (2 * KT * F * lam) * ((a * d) * Nb) ≤ (2 * KT * F * lam) * (a * Jn * (4 * KT)) :=
    mul_le_mul_of_nonneg_left k5 (by positivity)
  rw [div_le_iff₀ (by positivity)]
  calc Nb ^ 2 = Nb * Nb := by ring
    _ ≤ (2 * KT * F * lam * (a * d)) * Nb := k8
    _ = (2 * KT * F * lam) * ((a * d) * Nb) := by ring
    _ ≤ (2 * KT * F * lam) * (a * Jn * (4 * KT)) := k9
    _ = a * Jn * (8 * KT ^ 2 * F * lam) := by ring

set_option maxHeartbeats 1000000 in
theorem low_range_core {r σ ρ₀ lam KT F Nb : ℝ}
    (hr : 0 < r) (hσ : 0 ≤ σ) (hρ₀r : r ≤ ρ₀) (hρ₀1 : ρ₀ ≤ 1) (hlam : 33 * r / ρ₀ ≤ lam)
    (hKT : 0 < KT) (hF : 0 < F) (hNb : 0 < Nb)
    (hfar : 2 * KT * (ρ₀ / r) ^ σ ≤ Nb / 2)
    (P : Set E2) (D : Set (E2 × E2)) (hPfin : P.Finite) (hPne : P.Nonempty) (hDfin : D.Finite)
    (hP4 : ∀ p ∈ P, ‖p‖ ≤ 4)
    (hPfr : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
      ((P ∩ Metric.closedBall x ρ).ncard : ℝ) ≤ F * ρ * P.ncard)
    (hDmem : ∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1)
    (hbush : ∀ p ∈ P, Nb ≤ ({e | (p, e) ∈ D}.ncard : ℝ))
    (hKTb : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤ KT * (ρ / r) ^ σ) :
    ∃ J ⊆ D, (∀ q ∈ J, ∀ q' ∈ J, q ≠ q' → StripSep r q q') ∧
      Nb ^ 2 / (8 * KT ^ 2 * F * lam) ≤ (J.ncard : ℝ) ^ 2 := by
  have hρ₀ : 0 < ρ₀ := lt_of_lt_of_le hr hρ₀r
  have hlam33 : 33 * r ≤ lam := by
    have : 33 * r ≤ 33 * r / ρ₀ := by rw [le_div_iff₀ hρ₀]; nlinarith
    linarith
  have hlam0 : 0 < lam := by linarith
  have hKTr : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 →
      ({e | (p, e) ∈ D ∧ dist e u ≤ r}.ncard : ℝ) ≤ KT := by
    intro p hp u hu
    have := hKTb p hp u hu r le_rfl
    rwa [div_self hr.ne', Real.one_rpow, mul_one] at this
  have hfibfin : ∀ p : E2, ({e | (p, e) ∈ D} : Set E2).Finite := by
    intro p
    have : ({e | (p, e) ∈ D} : Set E2) = Prod.snd '' (D ∩ {q | q.1 = p}) := by
      ext e; simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨(p, e), ⟨h, rfl⟩, rfl⟩
      · rintro ⟨q, ⟨hq, hq1⟩, rfl⟩; rw [← hq1]; exact hq
    rw [this]; exact (hDfin.subset Set.inter_subset_left).image _
  -- Step 1: a maximal separated family
  obtain ⟨J₁f, hJ₁D, hJ₁pair, hJ₁max⟩ := exists_maximal_pairwise hDfin.toFinset (StripSep r)
  have hJ₁D' : (J₁f : Set (E2 × E2)) ⊆ D := fun q hq => by
    simpa using hJ₁D (Finset.mem_coe.mp hq)
  -- Step 2: the neighbourhoods of the members of J₁ cover D
  set Dj : E2 × E2 → Set (E2 × E2) :=
    fun j => {q | q ∈ D ∧ (q = j ∨ ¬ StripSep r q j ∨ ¬ StripSep r j q)} with hDjdef
  have hcover : D ⊆ ⋃ j ∈ J₁f, Dj j := by
    intro q hq
    simp only [Set.mem_iUnion]
    by_cases hqJ : q ∈ J₁f
    · exact ⟨q, hqJ, hq, Or.inl rfl⟩
    · obtain ⟨j, hj, hR⟩ := hJ₁max q (by simpa using hq) hqJ
      exact ⟨j, hj, hq, Or.inr hR⟩
  have hDle : (D.ncard : ℝ) ≤ ∑ j ∈ J₁f, ((Dj j).ncard : ℝ) := by
    have hUfin : (⋃ j ∈ J₁f, Dj j).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) (fun j _ => hDfin.subset (fun q hq => hq.1))
    calc (D.ncard : ℝ) ≤ ((⋃ j ∈ J₁f, Dj j).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hcover hUfin
      _ ≤ ∑ j ∈ J₁f, ((Dj j).ncard : ℝ) := ncard_biUnion_finset_le J₁f Dj
  -- Step 3: D is large
  have hDbig : (P.ncard : ℝ) * Nb ≤ D.ncard := by
    rw [ncard_eq_sum_fibers hPfin hDfin (fun q hq => (hDmem q hq).1),
      Set.ncard_eq_toFinset_card P hPfin]
    have h1 : ∑ p ∈ hPfin.toFinset, Nb ≤ ∑ p ∈ hPfin.toFinset, ({b' | (p, b') ∈ D}.ncard : ℝ) :=
      Finset.sum_le_sum (fun p hp => hbush p (by simpa using hp))
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    linarith
  have hPpos : (0 : ℝ) < P.ncard := by
    exact_mod_cast (Set.ncard_pos hPfin).mpr hPne
  have hDpos : (0 : ℝ) < D.ncard := lt_of_lt_of_le (by positivity) hDbig
  have hJ₁ne : J₁f.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.sum_empty] at hDle
    linarith
  -- Step 4: pigeonhole
  obtain ⟨j₀, hj₀J, hj₀big⟩ : ∃ j₀ ∈ J₁f, (D.ncard : ℝ) ≤ J₁f.card * ((Dj j₀).ncard : ℝ) := by
    by_contra hcon
    push Not at hcon
    have h1 : ∑ j ∈ J₁f, (J₁f.card : ℝ) * ((Dj j).ncard : ℝ) < ∑ j ∈ J₁f, (D.ncard : ℝ) :=
      Finset.sum_lt_sum_of_nonempty hJ₁ne (fun j hj => hcon j hj)
    rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : (J₁f.card : ℝ) * D.ncard ≤ J₁f.card * ∑ j ∈ J₁f, ((Dj j).ncard : ℝ) :=
      mul_le_mul_of_nonneg_left hDle (Nat.cast_nonneg _)
    linarith
  have hj₀D : j₀ ∈ D := hJ₁D' (Finset.mem_coe.mpr hj₀J)
  have hj₀4 : ‖j₀.1‖ ≤ 4 := hP4 _ (hDmem j₀ hj₀D).1
  have hj₀u : ‖j₀.2‖ = 1 := (hDmem j₀ hj₀D).2
  have hmj₀u : ‖-j₀.2‖ = 1 := by rw [norm_neg, hj₀u]
  -- Step 5: geometry of the neighbourhood of j₀
  have hnear : ∀ q ∈ Dj j₀, |inner ℝ (q.1 - j₀.1) j₀.2| < 9 * r ∧
      (dist q.2 j₀.2 < r ∨ dist q.2 (-j₀.2) < r) := by
    intro q hq
    exact near_of_not_stripSep (hP4 _ (hDmem q hq.1).1) hj₀4 hq.2 hr
  -- Step 6: the points near the line of j₀
  set P₀ : Set E2 := Prod.fst '' Dj j₀ with hP₀def
  have hDjfin : (Dj j₀).Finite := hDfin.subset (fun q hq => hq.1)
  have hP₀fin : P₀.Finite := hDjfin.image _
  have hP₀P : P₀ ⊆ P := by
    rintro p ⟨q, hq, rfl⟩; exact (hDmem q hq.1).1
  have hP₀line : ∀ p ∈ P₀, |inner ℝ (p - j₀.1) j₀.2| < 9 * r := by
    rintro p ⟨q, hq, rfl⟩; exact (hnear q hq).1
  have hDjle : ((Dj j₀).ncard : ℝ) ≤ P₀.ncard * (2 * KT) := by
    rw [ncard_eq_sum_fibers hP₀fin hDjfin (fun q hq => ⟨q, hq, rfl⟩),
      Set.ncard_eq_toFinset_card P₀ hP₀fin]
    suffices h1 : ∑ p ∈ hP₀fin.toFinset, ({b' | (p, b') ∈ Dj j₀}.ncard : ℝ) ≤
        ∑ p ∈ hP₀fin.toFinset, (2 * KT) by
      rw [Finset.sum_const, nsmul_eq_mul] at h1; exact h1
    apply Finset.sum_le_sum
    intro p hp
    have hpP : p ∈ P := hP₀P (by simpa using hp)
    have hsub : {e | (p, e) ∈ Dj j₀} ⊆ {e | (p, e) ∈ D ∧ dist e j₀.2 ≤ r} ∪
        {e | (p, e) ∈ D ∧ dist e (-j₀.2) ≤ r} := by
      intro e he
      have h := (hnear (p, e) he).2
      rcases h with h | h
      · exact Or.inl ⟨he.1, h.le⟩
      · exact Or.inr ⟨he.1, h.le⟩
    have hfin : ({e | (p, e) ∈ D ∧ dist e j₀.2 ≤ r} ∪
        {e | (p, e) ∈ D ∧ dist e (-j₀.2) ≤ r}).Finite :=
      ((hfibfin p).subset (fun e he => he.1)).union ((hfibfin p).subset (fun e he => he.1))
    calc ((({e | (p, e) ∈ Dj j₀} : Set E2)).ncard : ℝ)
        ≤ (({e | (p, e) ∈ D ∧ dist e j₀.2 ≤ r} ∪ {e | (p, e) ∈ D ∧ dist e (-j₀.2) ≤ r}).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub hfin
      _ ≤ ({e | (p, e) ∈ D ∧ dist e j₀.2 ≤ r}.ncard : ℝ) +
            ({e | (p, e) ∈ D ∧ dist e (-j₀.2) ≤ r}.ncard : ℝ) := by
          exact_mod_cast Set.ncard_union_le _ _
      _ ≤ KT + KT := add_le_add (hKTr p hpP _ hj₀u) (hKTr p hpP _ hmj₀u)
      _ = 2 * KT := by ring
  -- Step 7: a maximal lam-separated set of points near the line of j₀
  obtain ⟨P₀'f, hP₀'P₀, hP₀'pair, hP₀'max⟩ :=
    exists_maximal_pairwise hP₀fin.toFinset (fun x y => lam ≤ dist x y)
  have hP₀'sub : ∀ p ∈ P₀'f, p ∈ P₀ := fun p hp => by simpa using hP₀'P₀ hp
  have hP₀cov : P₀ ⊆ ⋃ p' ∈ P₀'f, (P ∩ Metric.closedBall p' lam) := by
    intro p hp
    simp only [Set.mem_iUnion]
    by_cases hpJ : p ∈ P₀'f
    · exact ⟨p, hpJ, hP₀P hp, Metric.mem_closedBall_self hlam0.le⟩
    · obtain ⟨j, hj, hR⟩ := hP₀'max p (by simpa using hp) hpJ
      refine ⟨j, hj, hP₀P hp, ?_⟩
      rw [Metric.mem_closedBall]
      rcases hR with h | h
      · exact (not_le.mp h).le
      · rw [dist_comm]; exact (not_le.mp h).le
  have hP₀le : (P₀.ncard : ℝ) ≤ P₀'f.card * (F * lam * P.ncard) := by
    have hUfin : (⋃ p' ∈ P₀'f, (P ∩ Metric.closedBall p' lam)).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) (fun p' _ => hPfin.subset Set.inter_subset_left)
    calc (P₀.ncard : ℝ) ≤ ((⋃ p' ∈ P₀'f, (P ∩ Metric.closedBall p' lam)).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hP₀cov hUfin
      _ ≤ ∑ p' ∈ P₀'f, ((P ∩ Metric.closedBall p' lam).ncard : ℝ) := ncard_biUnion_finset_le _ _
      _ ≤ ∑ p' ∈ P₀'f, (F * lam * P.ncard) :=
          Finset.sum_le_sum (fun p' _ => hPfr p' lam (by linarith))
      _ = P₀'f.card * (F * lam * P.ncard) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 8: far, separated sub-bushes
  set far : E2 → Set E2 :=
    fun p => {e | (p, e) ∈ D ∧ ρ₀ ≤ dist e j₀.2 ∧ ρ₀ ≤ dist e (-j₀.2)} with hfardef
  have hB_ex : ∀ p : E2, ∃ B : Finset E2, (B : Set E2) ⊆ far p ∧
      (B : Set E2).Pairwise (NormSep r) ∧
      ∀ e ∈ far p, ∃ e' ∈ B, dist e e' < r ∨ dist e (-e') < r := by
    intro p
    exact exists_maximal_normSep (far p) (fun e he => (hDmem _ he.1).2) hr
  choose B hBfar hBsep hBcov using hB_ex
  have hfarbig : ∀ p ∈ P, Nb / 2 ≤ ((far p).ncard : ℝ) := by
    intro p hp
    set N1 : Set E2 := {e | (p, e) ∈ D ∧ dist e j₀.2 ≤ ρ₀}
    set N2 : Set E2 := {e | (p, e) ∈ D ∧ dist e (-j₀.2) ≤ ρ₀}
    have hsub : {e | (p, e) ∈ D} ⊆ far p ∪ (N1 ∪ N2) := by
      intro e he
      by_cases h1 : ρ₀ ≤ dist e j₀.2
      · by_cases h2 : ρ₀ ≤ dist e (-j₀.2)
        · exact Or.inl ⟨he, h1, h2⟩
        · exact Or.inr (Or.inr ⟨he, (not_le.mp h2).le⟩)
      · exact Or.inr (Or.inl ⟨he, (not_le.mp h1).le⟩)
    have hfin : (far p ∪ (N1 ∪ N2)).Finite :=
      (hfibfin p).subset (by rintro e (he | he | he); exacts [he.1, he.1, he.1])
    have h3 := Set.ncard_union_le (far p) (N1 ∪ N2)
    have h4 := Set.ncard_union_le N1 N2
    have h5 : ({e | (p, e) ∈ D}.ncard : ℝ) ≤ ((far p).ncard : ℝ) + N1.ncard + N2.ncard := by
      have := (Set.ncard_le_ncard hsub hfin).trans (h3.trans (Nat.add_le_add_left h4 _))
      have : (({e | (p, e) ∈ D}.ncard : ℕ) : ℝ) ≤ (((far p).ncard + (N1.ncard + N2.ncard) : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at this; linarith
    have h6 := hKTb p hp _ hj₀u ρ₀ hρ₀r
    have h7 := hKTb p hp _ hmj₀u ρ₀ hρ₀r
    have h1 := hbush p hp
    linarith
  have hBbig : ∀ p ∈ P, Nb / (4 * KT) ≤ ((B p).card : ℝ) := by
    intro p hp
    set Ns : E2 → Set E2 := fun s => {e | (p, e) ∈ D ∧ dist e s ≤ r} ∪ {e | (p, e) ∈ D ∧ dist e (-s) ≤ r}
    have hcov2 : far p ⊆ ⋃ s ∈ B p, Ns s := by
      intro e he
      obtain ⟨s, hs, hcl⟩ := hBcov p e he
      simp only [Set.mem_iUnion]
      refine ⟨s, hs, ?_⟩
      rcases hcl with h | h
      · exact Or.inl ⟨he.1, h.le⟩
      · exact Or.inr ⟨he.1, h.le⟩
    have hUfin : (⋃ s ∈ B p, Ns s).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) (fun s _ =>
        ((hfibfin p).subset (fun e he => he.1)).union ((hfibfin p).subset (fun e he => he.1)))
    have h1 : ((far p).ncard : ℝ) ≤ ∑ s ∈ B p, ((Ns s).ncard : ℝ) :=
      (by exact_mod_cast Set.ncard_le_ncard hcov2 hUfin : ((far p).ncard : ℝ) ≤ _).trans
        (ncard_biUnion_finset_le _ _)
    have h2 : ∑ s ∈ B p, ((Ns s).ncard : ℝ) ≤ ∑ s ∈ B p, (2 * KT) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsu : ‖s‖ = 1 := (hDmem _ (hBfar p hs).1).2
      have hmsu : ‖-s‖ = 1 := by rw [norm_neg, hsu]
      have h3 : ((Ns s).ncard : ℝ) ≤ ({e | (p, e) ∈ D ∧ dist e s ≤ r}.ncard : ℝ) +
          ({e | (p, e) ∈ D ∧ dist e (-s) ≤ r}.ncard : ℝ) := by
        exact_mod_cast Set.ncard_union_le _ _
      have := hKTr p hp s hsu
      have := hKTr p hp (-s) hmsu
      linarith
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h4 := hfarbig p hp
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- Step 9: the separated family through the separated points
  set J' : Set (E2 × E2) := {q | q.1 ∈ P₀'f ∧ q.2 ∈ B q.1} with hJ'def
  have hJ'D : J' ⊆ D := by
    rintro ⟨p, e⟩ ⟨_, he⟩
    exact (hBfar p he).1
  have hJ'fin : J'.Finite := hDfin.subset hJ'D
  have hJ'card : (P₀'f.card : ℝ) * (Nb / (4 * KT)) ≤ J'.ncard := by
    have hGfin : (P₀'f : Set E2).Finite := Finset.finite_toSet _
    have hGeq : hGfin.toFinset = P₀'f := by ext p; simp
    rw [ncard_eq_sum_fibers hGfin hJ'fin (fun q hq => hq.1), hGeq]
    have hfib : ∀ p ∈ P₀'f, ({b' | (p, b') ∈ J'}.ncard : ℝ) = ((B p).card : ℝ) := by
      intro p hpP
      have : ({b' | (p, b') ∈ J'} : Set E2) = (B p : Set E2) := by
        ext e; simp [hJ'def, hpP]
      rw [this, Set.ncard_coe_finset]
    rw [Finset.sum_congr rfl hfib]
    have h1 : ∑ p ∈ P₀'f, Nb / (4 * KT) ≤ ∑ p ∈ P₀'f, ((B p).card : ℝ) :=
      Finset.sum_le_sum (fun p hp => hBbig p (hP₀P (hP₀'sub p hp)))
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    linarith
  have hJ'sep : ∀ q ∈ J', ∀ q' ∈ J', q ≠ q' → StripSep r q q' := by
    rintro ⟨p, e⟩ ⟨hp, he⟩ ⟨p', e'⟩ ⟨hp', he'⟩ hne
    by_cases hpp : p = p'
    · subst hpp
      have hee : e ≠ e' := fun h => hne (by rw [h])
      exact Or.inl (hBsep p he he' hee)
    · right
      by_contra hcon
      have hoff := not_le.mp hcon
      have hfarp : e ∈ far p := hBfar p he
      have hlamp : lam ≤ dist p p' := hP₀'pair p hp p' hp' hpp
      have hl1 := hP₀line p (hP₀'sub p hp)
      have hl2 := hP₀line p' (hP₀'sub p' hp')
      have hv : |inner ℝ (p - p') j₀.2| < 18 * r := by
        have : inner ℝ (p - p') j₀.2 = inner ℝ (p - j₀.1) j₀.2 - inner ℝ (p' - j₀.1) j₀.2 := by
          rw [← inner_sub_left]; congr 1; abel
        rw [this]
        calc |inner ℝ (p - j₀.1) j₀.2 - inner ℝ (p' - j₀.1) j₀.2|
            ≤ |inner ℝ (p - j₀.1) j₀.2| + |inner ℝ (p' - j₀.1) j₀.2| := abs_sub _ _
          _ < 9 * r + 9 * r := add_lt_add hl1 hl2
          _ = 18 * r := by ring
      have heu : ‖e‖ = 1 := (hDmem _ hfarp.1).2
      have hlamv : lam ≤ ‖p - p'‖ := by rw [← dist_eq_norm]; exact hlamp
      have hsmall1 : (r / lam) ^ 2 ≤ 1 / 2 := by
        rw [div_pow, div_le_iff₀ (by positivity)]; nlinarith
      have hsmall2 : (18 * r / lam) ^ 2 ≤ 1 / 2 := by
        rw [div_pow, div_le_iff₀ (by positivity)]; nlinarith
      have hcl := normals_close_of_long_vector hlam0 heu hj₀u hlamv hoff hv hsmall1 hsmall2
      have hbound : 3 * ((r + 18 * r) / lam) ^ 2 ≤ ρ₀ ^ 2 := by
        have h1 : 33 * r / lam ≤ ρ₀ := by
          rw [div_le_iff₀ hlam0]
          have := hlam; rw [div_le_iff₀ hρ₀] at this; linarith
        have h2 : 0 ≤ 33 * r / lam := by positivity
        have h3 : 3 * ((r + 18 * r) / lam) ^ 2 ≤ (33 * r / lam) ^ 2 := by
          rw [div_pow, div_pow, ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
          nlinarith
        nlinarith
      rcases hcl with h | h
      · have : ‖e - j₀.2‖ < ρ₀ := by
          by_contra hc; have := not_lt.mp hc; nlinarith [norm_nonneg (e - j₀.2)]
        have := hfarp.2.1; rw [dist_eq_norm] at this; linarith
      · have : ‖e - -j₀.2‖ < ρ₀ := by
          by_contra hc; have := not_lt.mp hc; nlinarith [norm_nonneg (e - -j₀.2)]
        have := hfarp.2.2; rw [dist_eq_norm] at this; linarith
  -- Step 10: the two families together
  have hJ₁card : (J₁f.card : ℝ) = ((J₁f : Set (E2 × E2)).ncard : ℝ) := by
    rw [Set.ncard_coe_finset]
  have hprod : Nb ^ 2 / (8 * KT ^ 2 * F * lam) ≤ (J₁f.card : ℝ) * J'.ncard :=
    low_range_arith (Nat.cast_nonneg _) (Nat.cast_nonneg _) hPpos hNb hKT hF hlam0
      hDbig hj₀big hDjle hP₀le hJ'card
  by_cases hcmp : ((J'.ncard : ℕ) : ℝ) ≤ J₁f.card
  · refine ⟨J₁f, hJ₁D', fun q hq q' hq' hne => hJ₁pair q hq q' hq' hne, ?_⟩
    rw [← hJ₁card]
    calc Nb ^ 2 / (8 * KT ^ 2 * F * lam) ≤ (J₁f.card : ℝ) * J'.ncard := hprod
      _ ≤ (J₁f.card : ℝ) * J₁f.card := mul_le_mul_of_nonneg_left hcmp (Nat.cast_nonneg _)
      _ = (J₁f.card : ℝ) ^ 2 := by ring
  · refine ⟨J', hJ'D, hJ'sep, ?_⟩
    have hcmp' := (not_le.mp hcmp).le
    calc Nb ^ 2 / (8 * KT ^ 2 * F * lam) ≤ (J₁f.card : ℝ) * J'.ncard := hprod
      _ ≤ (J'.ncard : ℝ) * J'.ncard := mul_le_mul_of_nonneg_right hcmp' (Nat.cast_nonneg _)
      _ = (J'.ncard : ℝ) ^ 2 := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
