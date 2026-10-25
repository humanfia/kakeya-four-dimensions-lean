-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormSelect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_cover_refinement.Selection

/-!
# Simultaneous selection for the zoomed family

Colour a conflict relation on the fine tubes and one on the covers of each level (bounded
degree), keep the tubes of a heavy common colour pattern, then prune all fibres (and the whole
family) simultaneously with retention `t` relative to the FULL original fibres.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Finset
open WangZahlLot.Obl.wz_separated_cover_refinement (color_relation prune_fibres)

/-- A heavy colour pattern inside a finite set. -/
theorem heavy_pattern {I P : Type*} [Fintype P] [DecidableEq P] [Nonempty P] (S : Finset I)
    (col : I → P) (w : I → ℝ) :
    ∃ a : P, (∑ i ∈ S, w i) ≤ (Fintype.card P : ℝ) * ∑ i ∈ S.filter (fun i => col i = a), w i := by
  classical
  let mass : P → ℝ := fun a => ∑ i ∈ S.filter (fun i => col i = a), w i
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image univ mass univ_nonempty
  refine ⟨a, ?_⟩
  have hsum : ∑ b, mass b = ∑ i ∈ S, w i := by
    dsimp [mass]
    exact sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _
  rw [← hsum]
  calc ∑ b, mass b ≤ ∑ _b : P, mass a := sum_le_sum fun b hb => hmax b hb
    _ = (Fintype.card P : ℝ) * mass a := by simp

open scoped Classical in
theorem select_zoom {n L : ℕ} (k : Fin L → ℕ) (f : ∀ ℓ : Fin L, Fin n → Fin (k ℓ))
    (I : Finset (Fin n)) (w : Fin n → ℝ) {M t : ℝ} (hM : 0 < M) (ht : 0 < t)
    (hwM : ∀ i, w i ≤ M) {K : ℕ} (hK : 0 < K)
    (R₀ : Fin n → Fin n → Prop) (hR₀s : ∀ {i j}, R₀ i j → R₀ j i)
    (hR₀b : ∀ i, (univ.filter (R₀ i)).card < K)
    (R : ∀ ℓ : Fin L, Fin (k ℓ) → Fin (k ℓ) → Prop) (hRs : ∀ ℓ {i j}, R ℓ i j → R ℓ j i)
    (hRb : ∀ ℓ j, (univ.filter (R ℓ j)).card < K) :
    ∃ Q : Finset (Fin n), Q ⊆ I ∧
      (∀ i ∈ Q, ∀ i' ∈ Q, i ≠ i' → ¬ R₀ i i') ∧
      (∀ ℓ, ∀ i ∈ Q, ∀ i' ∈ Q, f ℓ i ≠ f ℓ i' → ¬ R ℓ (f ℓ i) (f ℓ i')) ∧
      (∀ ℓ j, (Q.filter (fun i => f ℓ i = j)).Nonempty →
        t * ((univ.filter (fun i => f ℓ i = j)).card : ℝ) ≤
          ((Q.filter (fun i => f ℓ i = j)).card : ℝ)) ∧
      (Q.Nonempty → t * (n : ℝ) ≤ (Q.card : ℝ)) ∧
      (∑ i ∈ I, w i) / (K : ℝ) ^ (L + 1) - M * t * ((L + 1 : ℕ) * (n : ℝ)) ≤ ∑ i ∈ Q, w i := by
  classical
  obtain ⟨c₀, hc₀⟩ := color_relation hK R₀ hR₀s hR₀b
  choose c hc using fun ℓ => color_relation hK (R ℓ) (hRs ℓ) (hRb ℓ)
  have : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hK⟩
  let col : Fin n → (Fin (L + 1) → Fin K) :=
    fun i => Fin.cases (c₀ i) (fun ℓ => c ℓ (f ℓ i))
  obtain ⟨a, ha⟩ := heavy_pattern I col w
  have hcard : (Fintype.card (Fin (L + 1) → Fin K) : ℝ) = (K : ℝ) ^ (L + 1) := by simp
  rw [hcard] at ha
  set P := I.filter (fun i => col i = a) with hP
  let F : Option (Σ ℓ : Fin L, Fin (k ℓ)) → Finset (Fin n) := fun o =>
    match o with
    | none => univ
    | some ⟨ℓ, j⟩ => univ.filter (fun i => f ℓ i = j)
  obtain ⟨Q, hQP, hret, hmass⟩ := prune_fibres P F w hM ht hwM
  have hQI : Q ⊆ I := hQP.trans (filter_subset _ _)
  have hcolQ : ∀ i ∈ Q, col i = a := fun i hi => (mem_filter.mp (hQP hi)).2
  have hFsum : ∑ o, ((F o).card : ℝ) = (L + 1 : ℕ) * (n : ℝ) := by
    rw [Fintype.sum_option]
    simp only [F, card_univ, Fintype.card_fin]
    rw [Fintype.sum_sigma]
    have hfib : ∀ ℓ : Fin L, ∑ j : Fin (k ℓ), ((univ.filter (fun i => f ℓ i = j)).card : ℝ) = n := by
      intro ℓ
      have h := sum_card_fiberwise_eq_card_filter (univ : Finset (Fin n))
        (univ : Finset (Fin (k ℓ))) (f ℓ)
      have h' : (∑ j, (univ.filter (fun i => f ℓ i = j)).card) = n := by simpa using h
      exact_mod_cast h'
    simp_rw [hfib]
    simp
    ring
  refine ⟨Q, hQI, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi i' hi' hne hR
    have h1 : col i 0 = col i' 0 := by rw [hcolQ i hi, hcolQ i' hi']
    exact hc₀ i i' hne hR h1
  · intro ℓ i hi i' hi' hne hR
    have h1 : col i ℓ.succ = col i' ℓ.succ := by rw [hcolQ i hi, hcolQ i' hi']
    exact hc ℓ (f ℓ i) (f ℓ i') hne hR h1
  · intro ℓ j hj
    have he : ∀ inst : DecidableEq (Fin n),
        @Inter.inter (Finset (Fin n)) (@Finset.instInter (Fin n) inst) Q (F (some ⟨ℓ, j⟩)) =
          Q.filter (fun i => f ℓ i = j) := by
      intro inst; ext i; simp [F]
    have h := hret (some ⟨ℓ, j⟩)
    rw [he] at h
    have h2 := h hj
    simpa [F] using h2
  · intro hQ
    have he : ∀ inst : DecidableEq (Fin n),
        @Inter.inter (Finset (Fin n)) (@Finset.instInter (Fin n) inst) Q (F none) = Q := by
      intro inst; ext i; simp [F]
    have h := hret none
    rw [he] at h
    have h2 := h hQ
    simpa [F] using h2
  · rw [hFsum] at hmass
    have hP' : (∑ i ∈ I, w i) / (K : ℝ) ^ (L + 1) ≤ ∑ i ∈ P, w i := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
