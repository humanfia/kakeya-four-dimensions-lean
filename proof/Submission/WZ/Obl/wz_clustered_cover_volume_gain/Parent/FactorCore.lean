-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.FactorCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorKT
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorPrune

/-!
# Steps 4–5 of WZ Proposition 4.6: incidence graph, pruning, verification

Abstract core. We are given congruent convex sets `Bx j` (`j ∈ Jc`) of common volume `V₀`, and
pairwise disjoint families `R j` of tubes of `U₀` lying in `Bx j` with
`θ · m · V₀ ≤ #R_j ρ²`, where `m ≥ KT U₀`. Then the tubes of `U₀` lying in some `Bx j` form, after
discarding those in more than `2/θ` boxes and pruning the incidence graph (Lemma 4.7), a family
`U'` and boxes `J'` with the conclusions (i)–(iv) of Proposition 4.6.
-/

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

noncomputable section

variable {N : ℕ} {R ρ : ℝ} {y w : Fin N → Space}

theorem Fam.factor_core (hF : Fam R ρ y w) {U₀ : Finset (Fin N)} {m θ V₀ : ℝ}
    (hm : KT ρ y w U₀ ≤ m) (hm0 : 0 < m) (hθ : 0 < θ) (hV₀ : 0 < V₀)
    {J : ℕ} {Jc : Finset (Fin J)} (hJc : Jc.Nonempty) {Bx : Fin J → Set Space}
    {R : Fin J → Finset (Fin N)}
    (hBconv : ∀ j, Convex ℝ (Bx j)) (hBvol : ∀ j ∈ Jc, volume (Bx j) = ENNReal.ofReal V₀)
    (hR : ∀ j ∈ Jc, R j ⊆ sub ρ y w U₀ (Bx j))
    (hRlarge : ∀ j ∈ Jc, θ * m * V₀ ≤ (R j).card * ρ ^ 2)
    (hRdisj : ∀ i ∈ Jc, ∀ j ∈ Jc, i ≠ j → Disjoint (R i) (R j)) :
    ∃ U' ⊆ U₀, ∃ J' ⊆ Jc,
      (∑ j ∈ Jc, ((R j).card : ℝ)) ≤ 8 / θ * U'.card ∧
      (∀ j ∈ J', m * V₀ ≤ 8 / θ ^ 2 * (((sub ρ y w U' (Bx j)).card : ℝ) * ρ ^ 2)) ∧
      (∀ k ∈ U', 1 ≤ (J'.filter fun j => tube ρ y w k ⊆ Bx j).card ∧
        ((J'.filter fun j => tube ρ y w k ⊆ Bx j).card : ℝ) ≤ 2 / θ) ∧
      (∀ V, Convex ℝ V → volume V ≠ ⊤ →
        ((J'.filter fun j => Bx j ⊆ V).card : ℝ) * V₀ ≤ 16 / θ ^ 3 * (volume V).toReal) ∧
      (∀ j ∈ J', ∀ V, Convex ℝ V → volume V ≠ ⊤ →
        ((sub ρ y w U' (Bx j ∩ V)).card : ℝ) * V₀ ≤
          8 / θ ^ 2 * (sub ρ y w U' (Bx j)).card * (volume V).toReal) := by
  set E : Fin N → Fin J → Prop := fun k j => tube ρ y w k ⊆ Bx j with hE
  have hρ2 : 0 < ρ ^ 2 := pow_pos hF.pos 2
  have hcount : ∀ U ⊆ U₀, ∀ V, Convex ℝ V → volume V ≠ ⊤ →
      ((sub ρ y w U V).card : ℝ) * ρ ^ 2 ≤ m * (volume V).toReal := by
    intro U hU V hV hVt
    rcases hF.count_le U hV with h | h
    · exact h.trans (by gcongr; exact (KT_mono hU).trans hm)
    · exact absurd h hVt
  have hBfin : ∀ j ∈ Jc, volume (Bx j) ≠ ⊤ := fun j hj => by
    rw [hBvol j hj]; exact ENNReal.ofReal_ne_top
  have hboxcount : ∀ U ⊆ U₀, ∀ j ∈ Jc, ((sub ρ y w U (Bx j)).card : ℝ) * ρ ^ 2 ≤ m * V₀ := by
    intro U hU j hj
    have := hcount U hU (Bx j) (hBconv j) (hBfin j hj)
    rwa [hBvol j hj, ENNReal.toReal_ofReal hV₀.le] at this
  have hdegR_sub : ∀ U : Finset (Fin N), ∀ j, degR E j U = ((sub ρ y w U (Bx j)).card : ℝ) := by
    intro U j
    unfold degR sub
    rfl
  -- the tubes lying in some box
  set U₂ := U₀.filter fun k => ∃ j ∈ Jc, E k j with hU₂
  have hU₂sub : U₂ ⊆ U₀ := Finset.filter_subset _ _
  have hRU₂ : ∀ j ∈ Jc, R j ⊆ U₂ := fun j hj k hk => by
    have := mem_sub.mp (hR j hj hk)
    exact Finset.mem_filter.mpr ⟨this.1, j, hj, this.2⟩
  have hRsum : (∑ j ∈ Jc, ((R j).card : ℝ)) ≤ U₂.card := by
    have h1 : (Jc.biUnion R).card = ∑ j ∈ Jc, (R j).card :=
      Finset.card_biUnion (fun i hi j hj hij => hRdisj i hi j hj hij)
    have h2 : Jc.biUnion R ⊆ U₂ := Finset.biUnion_subset.mpr hRU₂
    have := Finset.card_le_card h2
    rw [h1] at this
    exact_mod_cast this
  have hdegR_low : ∀ j ∈ Jc, θ * m * V₀ ≤ degR E j U₂ * ρ ^ 2 := by
    intro j hj
    refine (hRlarge j hj).trans ?_
    gcongr
    rw [hdegR_sub]
    exact_mod_cast Finset.card_le_card fun k hk =>
      mem_sub.mpr ⟨hRU₂ j hj hk, (mem_sub.mp (hR j hj hk)).2⟩
  have hdegR_up : ∀ U ⊆ U₀, ∀ j ∈ Jc, degR E j U * ρ ^ 2 ≤ m * V₀ := by
    intro U hU j hj
    rw [hdegR_sub]
    exact hboxcount U hU j hj
  have hdegR_R : ∀ j ∈ Jc, θ * degR E j U₂ ≤ (R j).card := by
    intro j hj
    have h1 := hdegR_up U₂ hU₂sub j hj
    have h2 := hRlarge j hj
    have h3 : θ * degR E j U₂ * ρ ^ 2 ≤ (R j).card * ρ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right h3 hρ2
  have he₂ : θ * edges E U₂ Jc ≤ U₂.card := by
    rw [edges_eq_sum_degR, Finset.mul_sum]
    exact (Finset.sum_le_sum hdegR_R).trans hRsum
  have hJc_card : (Jc.card : ℝ) * (θ ^ 2 * m * V₀) ≤ U₂.card * ρ ^ 2 := by
    have h1 : (Jc.card : ℝ) * (θ * m * V₀) ≤ edges E U₂ Jc * ρ ^ 2 := by
      rw [edges_eq_sum_degR, Finset.sum_mul, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum hdegR_low
    calc (Jc.card : ℝ) * (θ ^ 2 * m * V₀) = θ * ((Jc.card : ℝ) * (θ * m * V₀)) := by ring
      _ ≤ θ * (edges E U₂ Jc * ρ ^ 2) := by gcongr
      _ = (θ * edges E U₂ Jc) * ρ ^ 2 := by ring
      _ ≤ U₂.card * ρ ^ 2 := by gcongr
  -- discard the tubes in too many boxes
  set U₃ := U₂.filter fun k => degL E k Jc ≤ 2 / θ with hU₃
  have hU₃sub : U₃ ⊆ U₂ := Finset.filter_subset _ _
  have hdegL_pos : ∀ k ∈ U₂, 1 ≤ degL E k Jc := by
    intro k hk
    obtain ⟨j, hj, hEkj⟩ := (Finset.mem_filter.mp hk).2
    unfold degL
    exact_mod_cast Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hEkj⟩⟩
  have hU₃card : (U₂.card : ℝ) ≤ 2 * U₃.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := U₂) (fun k => degL E k Jc ≤ 2 / θ)
    have hbad : ((U₂.filter fun k => ¬ degL E k Jc ≤ 2 / θ).card : ℝ) * (2 / θ) ≤
        edges E U₂ Jc := by
      unfold edges
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      calc ∑ _k ∈ U₂.filter (fun k => ¬ degL E k Jc ≤ 2 / θ), 2 / θ
          ≤ ∑ k ∈ U₂.filter (fun k => ¬ degL E k Jc ≤ 2 / θ),
              ((Jc.filter (E k)).card : ℝ) := by
            apply Finset.sum_le_sum
            intro k hk
            exact le_of_lt (not_le.mp (Finset.mem_filter.mp hk).2)
        _ ≤ ∑ k ∈ U₂, ((Jc.filter (E k)).card : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => Nat.cast_nonneg _)
    have h2 : ((U₂.filter fun k => ¬ degL E k Jc ≤ 2 / θ).card : ℝ) * 2 ≤ U₂.card := by
      have := mul_le_mul_of_nonneg_left hbad hθ.le
      rw [show θ * (((U₂.filter fun k => ¬ degL E k Jc ≤ 2 / θ).card : ℝ) * (2 / θ)) =
        ((U₂.filter fun k => ¬ degL E k Jc ≤ 2 / θ).card : ℝ) * 2 by field_simp] at this
      linarith
    have h3 : (U₃.card : ℝ) + (U₂.filter fun k => ¬ degL E k Jc ≤ 2 / θ).card = U₂.card := by
      exact_mod_cast hsplit
    linarith
  have he₃ : (U₃.card : ℝ) ≤ edges E U₃ Jc := by
    unfold edges
    calc (U₃.card : ℝ) = ∑ _k ∈ U₃, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun k hk => hdegL_pos k (hU₃sub hk)
  -- nonemptiness
  obtain ⟨j₀, hj₀⟩ := hJc
  have hR₀ : 0 < ((R j₀).card : ℝ) := by
    have := hRlarge j₀ hj₀
    have hpos : 0 < θ * m * V₀ := by positivity
    by_contra h
    push Not at h
    nlinarith
  have hU₂pos : (0 : ℝ) < U₂.card := lt_of_lt_of_le hR₀ (by
    exact_mod_cast Finset.card_le_card (hRU₂ j₀ hj₀))
  have hU₃pos : (0 : ℝ) < U₃.card := by linarith
  have hJcpos : (0 : ℝ) < Jc.card := by exact_mod_cast Finset.card_pos.mpr ⟨j₀, hj₀⟩
  -- pruning
  set e₃ := edges E U₃ Jc with he₃def
  have he₃pos : 0 < e₃ := lt_of_lt_of_le hU₃pos he₃
  obtain ⟨U', hU'U₃, J', hJ'Jc, hdegL', hdegR', hedges'⟩ :=
    prune (E := E) (tA := e₃ / (4 * U₃.card)) (tB := e₃ / (4 * Jc.card)) (by positivity)
      (by positivity) U₃ Jc
  have hedgesU' : e₃ / 2 ≤ edges E U' J' := by
    have h1 : e₃ / (4 * U₃.card) * U₃.card = e₃ / 4 := by field_simp
    have h2 : e₃ / (4 * Jc.card) * Jc.card = e₃ / 4 := by field_simp
    linarith
  have hU'U₀ : U' ⊆ U₀ := hU'U₃.trans (hU₃sub.trans hU₂sub)
  have hdegL_U' : ∀ k ∈ U', degL E k J' ≤ 2 / θ := fun k hk =>
    (degL_mono hJ'Jc).trans (Finset.mem_filter.mp (hU'U₃ hk)).2
  have htB : θ ^ 2 * m * V₀ / (8 * ρ ^ 2) ≤ e₃ / (4 * Jc.card) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc θ ^ 2 * m * V₀ * (4 * Jc.card) = 4 * (Jc.card * (θ ^ 2 * m * V₀)) := by ring
      _ ≤ 4 * (U₂.card * ρ ^ 2) := by gcongr
      _ ≤ 4 * (2 * U₃.card * ρ ^ 2) := by gcongr
      _ ≤ 4 * (2 * e₃ * ρ ^ 2) := by gcongr
      _ = e₃ * (8 * ρ ^ 2) := by ring
  have h45 : ∀ j ∈ J', m * V₀ ≤ 8 / θ ^ 2 * (((sub ρ y w U' (Bx j)).card : ℝ) * ρ ^ 2) := by
    intro j hj
    have hj' := hdegR' j hj
    rw [hdegR_sub] at hj'
    have h3 := htB.trans hj'
    rw [div_le_iff₀ (by positivity)] at h3
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc m * V₀ * θ ^ 2 = θ ^ 2 * m * V₀ := by ring
      _ ≤ ((sub ρ y w U' (Bx j)).card : ℝ) * (8 * ρ ^ 2) := h3
      _ = 8 * (((sub ρ y w U' (Bx j)).card : ℝ) * ρ ^ 2) := by ring
  refine ⟨U', hU'U₀, J', hJ'Jc, ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) many tubes survive
    have h1 : edges E U' J' ≤ 2 / θ * U'.card := by
      unfold edges
      rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum hdegL_U'
    have h2 : 8 / θ * U'.card = 4 * (2 / θ * U'.card) := by ring
    rw [h2]
    linarith
  · -- (4.5): each box contains many tubes of `U'`
    exact h45
  · -- every surviving tube lies in at least one and at most `2/θ` boxes
    intro k hk
    have hlow := hdegL' k hk
    have h1 : 0 < e₃ / (4 * U₃.card) := by positivity
    have hpos : 0 < (J'.filter (E k)).card := by
      have : (0 : ℝ) < (J'.filter (E k)).card := lt_of_lt_of_le h1 hlow
      exact_mod_cast this
    exact ⟨hpos, hdegL_U' k hk⟩
  · -- (iii) the boxes obey the Katz–Tao convex bound
    intro V hV hVt
    set J'V := J'.filter fun j => Bx j ⊆ V with hJ'V
    have hJ'VJ' : J'V ⊆ J' := Finset.filter_subset _ _
    have hlow : (J'V.card : ℝ) * (θ ^ 2 * m * V₀ / (8 * ρ ^ 2)) ≤ edges E U' J'V := by
      rw [edges_eq_sum_degR, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun j hj => htB.trans (hdegR' j (hJ'VJ' hj))
    have hup : edges E U' J'V ≤ 2 / θ * (sub ρ y w U' V).card := by
      unfold edges
      calc ∑ k ∈ U', ((J'V.filter (E k)).card : ℝ)
          ≤ ∑ k ∈ U', (if k ∈ sub ρ y w U' V then 2 / θ else 0) := by
            apply Finset.sum_le_sum
            intro k hk
            split_ifs with hkV
            · exact (degL_mono (E := E) hJ'VJ').trans (hdegL_U' k hk)
            · have : J'V.filter (E k) = ∅ := by
                rw [Finset.filter_eq_empty_iff]
                intro j hj hEkj
                exact hkV (mem_sub.mpr ⟨hk, hEkj.trans (Finset.mem_filter.mp hj).2⟩)
              rw [this, Finset.card_empty, Nat.cast_zero]
        _ = 2 / θ * (sub ρ y w U' V).card := by
            rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (sub_subset U' V),
              Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hcV := hcount U' hU'U₀ V hV hVt
    have hkey : (J'V.card : ℝ) * (θ ^ 2 * m * V₀ / (8 * ρ ^ 2)) ≤
        2 / θ * (m * (volume V).toReal / ρ ^ 2) := by
      refine (hlow.trans hup).trans ?_
      gcongr
      rw [le_div_iff₀ hρ2]
      exact hcV
    have hθ3 : 0 < θ ^ 3 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ3]
    have hgoal : (J'V.card : ℝ) * V₀ * θ ^ 3 * (m / (8 * ρ ^ 2)) ≤
        16 * (volume V).toReal * (m / (8 * ρ ^ 2)) := by
      have e1 : (J'V.card : ℝ) * V₀ * θ ^ 3 * (m / (8 * ρ ^ 2)) =
          θ * ((J'V.card : ℝ) * (θ ^ 2 * m * V₀ / (8 * ρ ^ 2))) := by ring
      have e2 : 16 * (volume V).toReal * (m / (8 * ρ ^ 2)) =
          θ * (2 / θ * (m * (volume V).toReal / ρ ^ 2)) := by field_simp; ring
      rw [e1, e2]
      gcongr
    exact le_of_mul_le_mul_right hgoal (by positivity)
  · -- (iv) the tubes in each box are Frostman (convex) inside it
    intro j hj V hV hVt
    have hjc : j ∈ Jc := hJ'Jc hj
    have h45j := h45 j hj
    have hsubV : ((sub ρ y w U' (Bx j ∩ V)).card : ℝ) ≤ (sub ρ y w U' V).card := by
      exact_mod_cast Finset.card_le_card (sub_mono subset_rfl Set.inter_subset_right)
    have hcV := hcount U' hU'U₀ V hV hVt
    have hvol0 : 0 ≤ (volume V).toReal := ENNReal.toReal_nonneg
    have key : ((sub ρ y w U' (Bx j ∩ V)).card : ℝ) * V₀ * ρ ^ 2 ≤
        8 / θ ^ 2 * (sub ρ y w U' (Bx j)).card * (volume V).toReal * ρ ^ 2 := by
      calc ((sub ρ y w U' (Bx j ∩ V)).card : ℝ) * V₀ * ρ ^ 2
          ≤ (sub ρ y w U' V).card * ρ ^ 2 * V₀ := by
            rw [mul_right_comm]; gcongr
        _ ≤ m * (volume V).toReal * V₀ := by gcongr
        _ = (volume V).toReal * (m * V₀) := by ring
        _ ≤ (volume V).toReal * (8 / θ ^ 2 * (((sub ρ y w U' (Bx j)).card : ℝ) * ρ ^ 2)) := by
            gcongr
        _ = 8 / θ ^ 2 * (sub ρ y w U' (Bx j)).card * (volume V).toReal * ρ ^ 2 := by ring
    exact le_of_mul_le_mul_right key hρ2

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor
