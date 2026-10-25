-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_separated_full_subtree.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_nsp_separated_full_subtree.Arithmetic
import Submission.WZ.Obl.wz_nsp_separated_full_subtree.Covers
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_nsp_separated_full_subtree`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_nsp_separated_full_subtree`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_nsp_separated_full_subtree/`
belong to this obligation.
-/

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nsp_separated_full_subtree

theorem WangZahlLot.wz_nsp_separated_full_subtree : ∀ T, T = (fun (d:ℝ) (p q:LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → ∀ Q, Q = (fun (δ a b:ℝ) (B m:ℕ) (x v:Fin m → LeanEval.Analysis.WangZahlKakeya.Space) => (∀ s:Fin m, ‖v s‖ = 1 ∧ T δ (x s) (v s) ⊆ Metric.ball 0 1) ∧ (∀ W:Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((Set.ncard {s:Fin m | T δ (x s) (v s) ⊆ W}:ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-b)) * MeasureTheory.volume W) ∧ ∃ J:ℕ, 0 < J ∧ J ≤ B ∧ ∃ (r:Fin J → ℝ) (k:Fin J → ℕ) (z w:(j:Fin J) → Fin (k j) → LeanEval.Analysis.WangZahlKakeya.Space) (f:(j:Fin J) → Fin m → Fin (k j)), (∀ j:Fin J, δ ≤ r j ∧ r j ≤ 1 ∧ 0 < k j) ∧ (∀ ρ₀:ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ j:Fin J, ρ₀ ≤ r j ∧ r j ≤ δ ^ (-a) * ρ₀) ∧ (∀ (j:Fin J) (i:Fin (k j)), ‖w j i‖ = 1) ∧ (∀ j:Fin J, Function.Surjective (f j)) ∧ (∀ (j:Fin J) (s:Fin m), T δ (x s) (v s) ⊆ T (r j) (z j (f j s)) (w j (f j s))) ∧ (∀ (j:Fin J) (i:Fin (k j)), δ ^ b * (r j) ^ 2 ≤ (Set.ncard {s:Fin m | f j s = i}:ℝ) * δ ^ 2) ∧ (∀ j j':Fin J, j ≤ j' → r j' ≤ r j ∧ ∃ p:Fin (k j') → Fin (k j), (∀ i':Fin (k j'), T (r j') (z j' i') (w j' i') ⊆ T (r j) (z j (p i')) (w j (p i'))) ∧ (∀ s:Fin m, f j s = p (f j' s)))) → ∀ F, F = (fun (δ K:ℝ) (m:ℕ) (x' v':Fin m → LeanEval.Analysis.WangZahlKakeya.Space) => ∀ ρ₀:ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ:ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ K * ρ₀ ∧ ∃ k:ℕ, 0 < k ∧ ∃ (z w:Fin k → LeanEval.Analysis.WangZahlKakeya.Space), (∀ j:Fin k, ‖w j‖ = 1) ∧ (∀ j j':Fin k, j ≠ j' → MeasureTheory.volume (T ρ (z j) (w j) ∩ T ρ (z j') (w j')) ≤ (1 / 2:ENNReal) * MeasureTheory.volume (T ρ (z j) (w j))) ∧ (∀ i:Fin m, ∃! j:Fin k, T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)) ∧ (∀ j:Fin k, ∃ i:Fin m, T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)) ∧ (∀ j j':Fin k, (((Set.ncard {i:Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)}:ℕ):ℝ)) ≤ K * (((Set.ncard {i:Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j') (w j')}:ℕ):ℝ))) ∧ (∀ j:Fin k, ∀ W:Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((((Set.ncard {i:Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j) (w j) ∧ T δ (x' i) (v' i) ⊆ W}:ℕ):ℝ)) * ρ ^ 2) ≤ ENNReal.ofReal (K * (((Set.ncard {i:Fin m | T δ (x' i) (v' i) ⊆ T ρ (z j) (w j)}:ℕ):ℝ))) * MeasureTheory.volume W)) → ∀ ε:ℝ, 0 < ε → ∀ B:ℕ, 0 < B → ∃ b:ℝ, 0 < b ∧ ∃ δ₀:ℝ, 0 < δ₀ ∧ ∀ δ:ℝ, 0 < δ → δ ≤ δ₀ → ∀ (m:ℕ) (x v:Fin m → LeanEval.Analysis.WangZahlKakeya.Space), 0 < m → Q δ ε b B m x v → ∃ (m':ℕ) (e:Fin m' → Fin m), 0 < m' ∧ Function.Injective e ∧ (∀ s t:Fin m', s ≠ t → MeasureTheory.volume (T δ (x (e s)) (v (e s)) ∩ T δ (x (e t)) (v (e t))) ≤ (1 / 2:ENNReal) * MeasureTheory.volume (T δ (x (e s)) (v (e s)))) ∧ F δ (δ ^ (-ε)) m' (fun s => x (e s)) (fun s => v (e s)) := by
  classical
  rintro T rfl Q rfl F rfl ε hε B hB
  obtain ⟨b, hb, hb1, hbε, q, hq, hqε, d, hd, hd100, hparam⟩ := parameters ε hε B
  refine ⟨b, hb, d, hd, ?_⟩
  intro δ hδ hδd m x v hm hQ
  obtain ⟨hfamily, hcount, J, hJ, hJB, r, k, z, w, f,
    hr, hnet, hw, hsurj, hcontain, hfull, hcoherent⟩ := hQ
  have hδ100 : δ ≤ 1 / 100 := hδd.trans hd100
  have hδ1 : δ < 1 := by linarith
  have hδb : 0 < δ ^ b := Real.rpow_pos_of_pos hδ b
  have hδb1 : δ ^ b ≤ 1 := Real.rpow_le_one hδ.le hδ1.le hb.le
  have hv : ∀ s, ‖v s‖ = 1 := fun s => (hfamily s).1
  obtain ⟨P, hP, hPbound, hbudget⟩ := hparam δ hδ hδd
  obtain ⟨fine, hfine⟩ := layer_coloring hδ hδ1.le
    (Real.rpow_nonneg hδ.le (-b)) hδb hP hPbound x v x v id hv hcount
    (fun _ => Subset.rfl) (by
      intro i
      simpa using mul_le_mul_of_nonneg_right hδb1 (sq_nonneg δ))
  have hlayers : ∀ j : Fin J, ∃ color : Fin (k j) → Fin P,
      ∀ i i', i ≠ i' → Near (r j) (z j i) (w j i) (z j i') (w j i') → color i ≠ color i' := by
    intro j
    exact layer_coloring (hδ.trans_le (hr j).1) (hr j).2.1
      (Real.rpow_nonneg hδ.le (-b)) hδb hP hPbound x v (z j) (w j) (f j)
      (hw j) hcount (hcontain j) (hfull j)
  choose color hcolor using hlayers
  obtain ⟨U, hU, hUfine, hUcolor⟩ := common_colors hP k f fine color
  have hnested : ∀ j j' : Fin J, j ≤ j' → ∀ s t, f j' s = f j' t → f j s = f j t := by
    intro j j' hjj' s t hst
    obtain ⟨_, p, _, hp⟩ := hcoherent j j' hjj'
    rw [hp s, hp t, hst]
  have hball : (volume (ball (0 : Space) 1)).toReal ≤ 16 := by
    rw [EuclideanSpace.volume_ball_fin_three]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith [Real.pi_lt_four]
  have hmcount : (m : ℝ) * δ ^ 2 ≤ δ ^ (-b) * 16 :=
    (WangZahlLot.Obl.wz_direction_density_transfer.global_count
      (Real.rpow_nonneg hδ.le (-b)) hcount (fun s => (hfamily s).2)).trans
      (mul_le_mul_of_nonneg_left hball (Real.rpow_nonneg hδ.le (-b)))
  have hmbins : (m : ℝ) < (δ ^ (-(ε / 4))) ^ q :=
    WangZahlLot.Obl.wz_tower_balanced_refinement.cardinal_lt_power hδ hδ1.le hb1
      (by norm_num) (by linarith) hqε hmcount
  have hR : 1 < δ ^ (-(ε / 4)) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 (show -(ε / 4) < 0 by linarith)
  obtain ⟨bins, hbins⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.exists_size_color
    m q (δ ^ (-(ε / 4))) hq hR hmbins
  obtain ⟨S, hSU, hSmass, hSbal⟩ := regularize_layers hJ hq k f hnested
    (δ ^ (-(ε / 4))) bins hbins U
  have hretain : δ ^ (ε / 4) * m ≤ (S.card : ℝ) :=
    retained_card hδ U S hU hSmass (hbudget J hJB)
  have hSpos : 0 < S.card := by
    have ht : 0 < δ ^ (ε / 4) * (m : ℝ) :=
      mul_pos (Real.rpow_pos_of_pos hδ _) (by exact_mod_cast hm)
    exact_mod_cast ht.trans_le hretain
  have hS : S.Nonempty := Finset.card_pos.mp hSpos
  have hparentsep : ∀ j, ∀ s ∈ S, ∀ t ∈ S, f j s ≠ f j t →
      ¬Near (r j) (z j (f j s)) (w j (f j s)) (z j (f j t)) (w j (f j t)) := by
    intro j s hs t ht hst hn
    exact hcolor j (f j s) (f j t) hst hn (hUcolor j s (hSU hs) t (hSU ht))
  have hSfull : ∀ j, ∀ s ∈ S, δ ^ (3 * ε / 4) * (r j) ^ 2 ≤
      ((S.filter (fun t => f j t = f j s)).card : ℝ) * δ ^ 2 := by
    intro j s hs
    apply fullness_exponents hδ hδ1.le hbε
    simpa only [mul_assoc] using balanced_fullness (hr j).2.2 (Real.rpow_nonneg hδ.le (ε / 4))
      (Real.rpow_nonneg hδ.le (-(ε / 4))) (f j) S (hfull j) hretain (hSbal j) s hs
  let e := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate S
  have he : Function.Injective e := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_injective S
  have hemem : ∀ s, e s ∈ S := WangZahlLot.Obl.wz_separated_cover_refinement.enumerate_mem S
  refine ⟨S.card, e, hSpos, he, ?_, ?_⟩
  · intro s t hst
    apply separated_of_not_near hδ (hv (e s)) (hv (e t))
    intro hn
    exact hfine (e s) (e t) (he.ne hst) hn
      (hUfine (e s) (hSU (hemem s)) (e t) (hSU (hemem t)))
  · intro ρ₀ hρδ hρ1
    obtain ⟨j, hρj, hjρ⟩ := hnet ρ₀ hρδ hρ1
    have hRK : δ ^ (-(ε / 4)) ≤ δ ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (by linarith)
    have hL : δ ^ (-b) ≤ δ ^ (-ε) * δ ^ (3 * ε / 4) := by
      rw [← Real.rpow_add hδ]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (by linarith)
    obtain ⟨k', hk', z', w', hc⟩ := selected_cover hδ (hδ.trans_le (hr j).1)
      (Real.rpow_nonneg hδ.le (-ε)) hRK hL x v (z j) (w j) (f j) hv (hw j)
      hcount (hcontain j) S hS (hparentsep j) (hSbal j) (hSfull j)
    exact ⟨r j, hρj, (hr j).2.1, hjρ, k', hk', z', w', hc⟩
