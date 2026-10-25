-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FactorJ.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorMain
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorAssign

/-!
# Proposition 4.6 for tubes with a balanced assignment (the input format of Proposition 5.2)

From `Fam.factor` and `balanced_assignment`: a sub-collection `U` (`N ≤ 2K #U`) and congruent boxes
`box a b (2R) (z i) (e i)` with an assignment `g` of the tubes of `U` to boxes containing them, whose
fibres are `2K²`-balanced and rich (`m·2Rab ≤ 2K³ #fibre ρ²`), each tube lying in at most `K` boxes,
the boxes Katz–Tao with error `K`, and each fibre Frostman inside its box with error `2K²`.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

noncomputable section

variable {N : ℕ} {R ρ : ℝ} {y w : Fin N → Space}

set_option maxHeartbeats 1000000 in
theorem Fam.factor_assign (hF : Fam R ρ y w) (hR : 1 ≤ R) (hN : 0 < N) :
    ∃ (U : Finset (Fin N)) (m a b : ℝ) (L : ℕ) (z : Fin L → Space)
      (e : Fin L → Space ≃ₗᵢ[ℝ] Space) (g : Fin N → Fin L),
      (N : ℝ) ≤ 2 * Kc R N ρ * U.card ∧ 0 < m ∧ ρ ≤ a ∧ a ≤ b ∧ b ≤ 2 * R ∧
      (∀ W, Convex ℝ W → ENNReal.ofReal (((sub ρ y w U W).card : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal m * volume W) ∧
      (∀ k ∈ U, tube ρ y w k ⊆ box a b (2 * R) (z (g k)) (e (g k)) ∧
        ((Finset.univ.filter fun i => tube ρ y w k ⊆ box a b (2 * R) (z i) (e i)).card : ℝ) ≤
          Kc R N ρ) ∧
      (∀ i i', ((U.filter fun k => g k = i).card : ℝ) ≤
        2 * Kc R N ρ ^ 2 * (U.filter fun k => g k = i').card) ∧
      (∀ i, m * (a * b * (2 * R)) ≤
        2 * Kc R N ρ ^ 3 * (((U.filter fun k => g k = i).card : ℝ) * ρ ^ 2)) ∧
      (∀ V, Convex ℝ V → ENNReal.ofReal
        (((Finset.univ.filter fun i => box a b (2 * R) (z i) (e i) ⊆ V).card : ℝ) *
          (a * b * (2 * R))) ≤ ENNReal.ofReal (Kc R N ρ) * volume V) ∧
      (∀ i V, Convex ℝ V → ENNReal.ofReal
        ((U.filter fun k => g k = i ∧ tube ρ y w k ⊆ box a b (2 * R) (z i) (e i) ∩ V).card) *
          volume (box a b (2 * R) (z i) (e i)) ≤
        ENNReal.ofReal (2 * Kc R N ρ ^ 2 * (U.filter fun k => g k = i).card) *
          volume (box a b (2 * R) (z i) (e i) ∩ V)) := by
  obtain ⟨U₀, m, a, b, L₀, z₀, e₀, h1, hm, ha, hab, hb, hKT, h45, hcov, hboxKT, -⟩ :=
    hF.factor hR hN
  have hρ := hF.pos
  have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
  have hR0 : 0 < R := by linarith
  set K := Kc R N ρ with hKdef
  have hKpos : 0 < K := Kc_pos hR0 N ρ
  have hK1 : 1 ≤ K := by
    have h := hcov
    have hU₀ : U₀.Nonempty := by
      by_contra hU
      rw [Finset.not_nonempty_iff_eq_empty] at hU
      rw [hU, Finset.card_empty, Nat.cast_zero, mul_zero] at h1
      have : (0 : ℝ) < N := by exact_mod_cast hN
      linarith
    obtain ⟨k, hk⟩ := hU₀
    exact le_trans (by exact_mod_cast (h k hk).1) (h k hk).2
  set V₀ := a * b * (2 * R) with hV₀
  have hapos : 0 < a := hρ.trans_le ha
  have hV₀pos : 0 < V₀ := by
    have : 0 < b := hapos.trans_le hab
    positivity
  set Bx : Fin L₀ → Set Space := fun i => box a b (2 * R) (z₀ i) (e₀ i) with hBx
  have hBvol : ∀ i, volume (Bx i) = ENNReal.ofReal V₀ := fun i =>
    box_volume hapos.le (hapos.le.trans hab) (by positivity) _ _
  -- the KT bound in real form for `U₀` and any convex set of finite volume
  have hKTr : ∀ W, Convex ℝ W → ∀ v : ℝ, 0 ≤ v → volume W ≤ ENNReal.ofReal v →
      ((sub ρ y w U₀ W).card : ℝ) * ρ ^ 2 ≤ m * v := by
    intro W hW v hv hWv
    have h : ENNReal.ofReal (((sub ρ y w U₀ W).card : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal m * ENNReal.ofReal v := (hKT W hW).trans (by gcongr)
    rw [← ENNReal.ofReal_mul hm.le] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hm.le hv)).mp h
  set M := m * V₀ / ρ ^ 2 with hMdef
  have hMpos : 0 < M := by positivity
  -- each box holds between `M/K` and `M` tubes of `U₀`
  have hrich : ∀ i, M / K ≤ ((U₀.filter fun k => tube ρ y w k ⊆ Bx i).card : ℝ) ∧
      ((U₀.filter fun k => tube ρ y w k ⊆ Bx i).card : ℝ) ≤ M := by
    intro i
    have hsub_eq : (U₀.filter fun k => tube ρ y w k ⊆ Bx i) = sub ρ y w U₀ (Bx i) := rfl
    rw [hsub_eq]
    constructor
    · have h := h45 i
      rw [hMdef, div_div, div_le_iff₀ (by positivity)]
      calc m * V₀ ≤ K * (((sub ρ y w U₀ (Bx i)).card : ℝ) * ρ ^ 2) := h
        _ = ((sub ρ y w U₀ (Bx i)).card : ℝ) * (ρ ^ 2 * K) := by ring
    · rw [hMdef, le_div_iff₀ hρ2]
      exact hKTr (Bx i) (box_convex _ _ _ _ _) V₀ hV₀pos.le (hBvol i).le
  have hL₀ : 0 < L₀ := by
    have hU₀ : U₀.Nonempty := by
      by_contra hU
      rw [Finset.not_nonempty_iff_eq_empty] at hU
      rw [hU, Finset.card_empty, Nat.cast_zero, mul_zero] at h1
      have : (0 : ℝ) < N := by exact_mod_cast hN
      linarith
    obtain ⟨k, hk⟩ := hU₀
    obtain ⟨i, -⟩ := Finset.card_pos.mp (hcov k hk).1
    exact Fin.pos i
  obtain ⟨U, G, g₀, hUU₀, hUcard, hassign, hfib⟩ :=
    balanced_assignment hL₀ U₀ (fun k i => tube ρ y w k ⊆ Bx i) hK1 hMpos
      (fun k hk => hcov k hk) hrich
  -- reindex the kept boxes by `Fin G.card`
  set idx : Fin G.card → Fin L₀ := fun j => (G.equivFin.symm j).1 with hidx
  have hidxG : ∀ j, idx j ∈ G := fun j => (G.equivFin.symm j).2
  let g : Fin N → Fin G.card := fun k =>
    if hk : g₀ k ∈ G then G.equivFin ⟨g₀ k, hk⟩ else ⟨0, Finset.card_pos.mpr (by
      obtain ⟨k₀, hk₀⟩ : U.Nonempty := by
        by_contra hU
        rw [Finset.not_nonempty_iff_eq_empty] at hU
        rw [hU, Finset.card_empty, Nat.cast_zero, mul_zero] at hUcard
        have : (0 : ℝ) < N := by exact_mod_cast hN
        have hU₀pos : (0 : ℝ) < U₀.card := by
          by_contra h0; push Not at h0
          have : (U₀.card : ℝ) = 0 := le_antisymm h0 (Nat.cast_nonneg _)
          rw [this, mul_zero] at h1; linarith
        linarith
      exact ⟨g₀ k₀, (hassign k₀ hk₀).2⟩)⟩
  have hg_idx : ∀ k ∈ U, idx (g k) = g₀ k := by
    intro k hk
    have hkG := (hassign k hk).2
    simp only [g, dif_pos hkG, hidx, Equiv.symm_apply_apply]
  have hfib_eq : ∀ j, (U.filter fun k => g k = j) = (U.filter fun k => g₀ k = idx j) := by
    intro j
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hkU, hkj⟩; exact ⟨hkU, by rw [← hg_idx k hkU, hkj]⟩
    · rintro ⟨hkU, hkj⟩
      refine ⟨hkU, ?_⟩
      apply (G.equivFin.symm).injective
      apply Subtype.ext
      change idx (g k) = idx j
      rw [hg_idx k hkU, hkj]
  have hfib' : ∀ j, M / (2 * K ^ 2) ≤ ((U.filter fun k => g k = j).card : ℝ) ∧
      ((U.filter fun k => g k = j).card : ℝ) ≤ M := by
    intro j
    rw [hfib_eq j]
    exact hfib (idx j) (hidxG j)
  refine ⟨U, m, a, b, G.card, fun j => z₀ (idx j), fun j => e₀ (idx j), g, ?_, hm, ha, hab, hb,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `N ≤ 2 K #U`
    calc (N : ℝ) ≤ K * U₀.card := h1
      _ ≤ K * (2 * U.card) := by gcongr
      _ = 2 * K * U.card := by ring
  · intro W hW
    refine le_trans ?_ (hKT W hW)
    apply ENNReal.ofReal_le_ofReal
    gcongr
    exact sub_mono hUU₀ subset_rfl
  · intro k hk
    refine ⟨?_, ?_⟩
    · show tube ρ y w k ⊆ Bx (idx (g k))
      rw [hg_idx k hk]
      exact (hassign k hk).1
    · refine le_trans ?_ (hcov k (hUU₀ hk)).2
      have := card_filter_reindex G (fun i => tube ρ y w k ⊆ Bx i)
      simp only [hBx] at this
      rw [show (Finset.univ.filter fun j : Fin G.card =>
          tube ρ y w k ⊆ box a b (2 * R) (z₀ (idx j)) (e₀ (idx j))) =
          (Finset.univ.filter fun j : Fin G.card =>
          tube ρ y w k ⊆ box a b (2 * R) (z₀ (G.equivFin.symm j).1) (e₀ (G.equivFin.symm j).1))
        from rfl, this]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ G))
  · intro i i'
    obtain ⟨hlo, -⟩ := hfib' i'
    obtain ⟨-, hhi⟩ := hfib' i
    have hK2 : 0 < 2 * K ^ 2 := by positivity
    have hcancel : 2 * K ^ 2 * (M / (2 * K ^ 2)) = M := by
      rw [mul_comm]; exact div_mul_cancel₀ M hK2.ne'
    calc ((U.filter fun k => g k = i).card : ℝ) ≤ M := hhi
      _ = 2 * K ^ 2 * (M / (2 * K ^ 2)) := hcancel.symm
      _ ≤ 2 * K ^ 2 * (U.filter fun k => g k = i').card := by gcongr
  · intro i
    obtain ⟨hlo, -⟩ := hfib' i
    have hK3 : 2 * K ^ 2 ≤ 2 * K ^ 3 := by
      have : K ^ 2 ≤ K ^ 3 := pow_le_pow_right₀ hK1 (by norm_num)
      linarith
    have hMρ : m * V₀ = M * ρ ^ 2 := by rw [hMdef]; exact (div_mul_cancel₀ _ hρ2.ne').symm
    have hK2 : 0 < 2 * K ^ 2 := by positivity
    have hcancel : 2 * K ^ 2 * (M / (2 * K ^ 2)) = M := by
      rw [mul_comm]; exact div_mul_cancel₀ M hK2.ne'
    calc m * V₀ = M * ρ ^ 2 := hMρ
      _ = 2 * K ^ 2 * (M / (2 * K ^ 2)) * ρ ^ 2 := by rw [hcancel]
      _ ≤ 2 * K ^ 2 * ((U.filter fun k => g k = i).card : ℝ) * ρ ^ 2 := by gcongr
      _ ≤ 2 * K ^ 3 * ((U.filter fun k => g k = i).card : ℝ) * ρ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK3 (Nat.cast_nonneg _)) hρ2.le
      _ = 2 * K ^ 3 * (((U.filter fun k => g k = i).card : ℝ) * ρ ^ 2) := by ring
  · intro V hV
    refine le_trans ?_ (hboxKT V hV)
    apply ENNReal.ofReal_le_ofReal
    gcongr
    have := card_filter_reindex G (fun i => Bx i ⊆ V)
    simp only [hBx] at this
    rw [show (Finset.univ.filter fun j : Fin G.card =>
        box a b (2 * R) (z₀ (idx j)) (e₀ (idx j)) ⊆ V) =
        (Finset.univ.filter fun j : Fin G.card =>
        box a b (2 * R) (z₀ (G.equivFin.symm j).1) (e₀ (G.equivFin.symm j).1) ⊆ V)
      from rfl, this]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ G))
  · -- each fibre is Frostman inside its box
    intro i V hV
    have hconv : Convex ℝ (Bx (idx i) ∩ V) := (box_convex _ _ _ _ _).inter hV
    obtain ⟨hlo, -⟩ := hfib' i
    have hcount : ((U.filter fun k => g k = i ∧
        tube ρ y w k ⊆ box a b (2 * R) (z₀ (idx i)) (e₀ (idx i)) ∩ V).card : ℝ) ≤
        (sub ρ y w U₀ (Bx (idx i) ∩ V)).card := by
      exact_mod_cast Finset.card_le_card fun k hk => by
        obtain ⟨hkU, -, hkV⟩ := Finset.mem_filter.mp hk
        exact mem_sub.mpr ⟨hUU₀ hkU, hkV⟩
    by_cases htop : volume (Bx (idx i) ∩ V) = ⊤
    · have : volume (Bx (idx i) ∩ V) ≤ ENNReal.ofReal V₀ :=
        (measure_mono inter_subset_left).trans (hBvol _).le
      exact absurd (top_le_iff.mp (htop ▸ this)) ENNReal.ofReal_ne_top
    set v := (volume (Bx (idx i) ∩ V)).toReal with hv
    have hKTv := hKTr (Bx (idx i) ∩ V) hconv v ENNReal.toReal_nonneg
      (ENNReal.le_ofReal_iff_toReal_le htop ENNReal.toReal_nonneg |>.mpr le_rfl)
    -- `#fibre_V · V₀ ≤ (m v / ρ²) V₀ = M v ≤ 2K² #fibre · v`
    have hreal : ((U.filter fun k => g k = i ∧
        tube ρ y w k ⊆ box a b (2 * R) (z₀ (idx i)) (e₀ (idx i)) ∩ V).card : ℝ) * V₀ ≤
        2 * K ^ 2 * ((U.filter fun k => g k = i).card : ℝ) * v := by
      have hK2 : 0 < 2 * K ^ 2 := by positivity
      have h2 : ((sub ρ y w U₀ (Bx (idx i) ∩ V)).card : ℝ) * V₀ ≤ M * v := by
        rw [hMdef]
        rw [div_mul_eq_mul_div, le_div_iff₀ hρ2]
        nlinarith [hKTv]
      have h3 : M * v ≤ 2 * K ^ 2 * ((U.filter fun k => g k = i).card : ℝ) * v := by
        have : M ≤ 2 * K ^ 2 * ((U.filter fun k => g k = i).card : ℝ) := by
          rw [div_le_iff₀ hK2] at hlo; linarith
        gcongr
      calc _ ≤ ((sub ρ y w U₀ (Bx (idx i) ∩ V)).card : ℝ) * V₀ := by gcongr
        _ ≤ M * v := h2
        _ ≤ _ := h3
    show ENNReal.ofReal _ * volume (Bx (idx i)) ≤ _ * volume (Bx (idx i) ∩ V)
    rw [hBvol, ← ENNReal.ofReal_toReal htop, ← hv, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
