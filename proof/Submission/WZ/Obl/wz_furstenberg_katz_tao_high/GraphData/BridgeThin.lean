-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.BridgeThin.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/BridgeThin.lean (82de8bd).
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.Bridge
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.Thinning

/-!
# The bridge with thinning after endpoint selection

`Bridge.lean` needs lines `9 δ / q`-separated, which the chart of a coarse tube does not give
(its separation is a fixed fraction of the incidence tolerance).  Here lines only need to be
`σ`-separated in the sup metric of their parameters, for any `σ > 0`.  After x0603's endpoint
selection, the common family is thinned greedily so that its anchor codes are `δ`-separated,
keeping a `1/D` share of the (line, selected column) incidences, `D = ⌈(18 δ/(q σ) + 2)²⌉`; the
selected columns are then restricted to those still meeting a `d / (16 D)` share of the thinned
family.  The column-spread hypothesis only involves the original density `d`.

`tube_model_of_dense_columns_thin` produces the inputs of `tube_model_false` with the constant
`tubeKD K₀ q b β d D = K₀ (9/q)^(1+b) 8^β 64 D / d³`; `dense_columns_thin_false` composes it with
`tube_model_false` (accepted o223).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The constant of the thinned tube model. -/
noncomputable def tubeKD (K₀ q b β d D : ℝ) : ℝ :=
  K₀ * (9 / q) ^ (1 + b) * 8 ^ β * 64 * D / d ^ 3

theorem tubeKD_bounds {K₀ q b β d D : ℝ} (hK₀ : 1 ≤ K₀) (hq : 0 < q) (hq1 : q ≤ 1) (hb : 0 < b)
    (hβ : 0 ≤ β) (hd : 0 < d) (hd1 : d ≤ 1) (hD : 1 ≤ D) :
    K₀ * (9 / q) ^ (1 + b) * (64 * D / d ^ 3) ≤ tubeKD K₀ q b β d D ∧
    K₀ * (64 * D / d ^ 3) ≤ tubeKD K₀ q b β d D ∧
    K₀ * 8 ^ β * (64 * D / d ^ 2) ≤ tubeKD K₀ q b β d D ∧
    16 * D / d ≤ tubeKD K₀ q b β d D ∧ 1 ≤ tubeKD K₀ q b β d D := by
  have h9q : 1 ≤ 9 / q := by rw [le_div_iff₀ hq]; linarith
  have hA : 1 ≤ (9 / q) ^ (1 + b) := Real.one_le_rpow h9q (by linarith)
  have hB : 1 ≤ (8 : ℝ) ^ β := Real.one_le_rpow (by norm_num) hβ
  have hd3 : 0 < d ^ 3 := by positivity
  have hd2 : 0 < d ^ 2 := by positivity
  have hd32 : d ^ 3 ≤ d ^ 2 := by nlinarith
  have hd21 : d ^ 2 ≤ d := by nlinarith
  have hT : tubeKD K₀ q b β d D = K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 * D / d ^ 3) := by
    unfold tubeKD; ring
  have hX : 0 ≤ 64 * D / d ^ 3 := by positivity
  have hAB : 1 ≤ (9 / q) ^ (1 + b) * 8 ^ β := one_le_mul_of_one_le_of_one_le hA hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hT]
    have e : K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 * D / d ^ 3) =
        (K₀ * (9 / q) ^ (1 + b) * (64 * D / d ^ 3)) * 8 ^ β := by ring
    rw [e]; exact le_mul_of_one_le_right (by positivity) hB
  · rw [hT]
    have e : K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 * D / d ^ 3) =
        (K₀ * (64 * D / d ^ 3)) * ((9 / q) ^ (1 + b) * 8 ^ β) := by ring
    rw [e]; exact le_mul_of_one_le_right (by positivity) hAB
  · rw [hT]
    have h1 : 64 * D / d ^ 2 ≤ 64 * D / d ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) hd3 hd32
    have h2 : K₀ * 8 ^ β * (64 * D / d ^ 2) ≤ K₀ * 8 ^ β * (64 * D / d ^ 3) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e : K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 * D / d ^ 3) =
        (K₀ * 8 ^ β * (64 * D / d ^ 3)) * (9 / q) ^ (1 + b) := by ring
    rw [e]
    exact h2.trans (le_mul_of_one_le_right (by positivity) hA)
  · rw [hT]
    have h1 : 16 * D / d ≤ 64 * D / d ^ 3 := by
      rw [div_le_div_iff₀ hd hd3]; nlinarith
    have hKAB : 1 ≤ K₀ * ((9 / q) ^ (1 + b) * 8 ^ β) := one_le_mul_of_one_le_of_one_le hK₀ hAB
    have e : K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 * D / d ^ 3) =
        (64 * D / d ^ 3) * (K₀ * ((9 / q) ^ (1 + b) * 8 ^ β)) := by ring
    rw [e]
    exact h1.trans (le_mul_of_one_le_right hX hKAB)
  · rw [hT]
    have h1 : 1 ≤ 64 * D / d ^ 3 := by
      rw [le_div_iff₀ hd3]; nlinarith
    have hKAB : 1 ≤ K₀ * ((9 / q) ^ (1 + b) * 8 ^ β) := one_le_mul_of_one_le_of_one_le hK₀ hAB
    have e : K₀ * (9 / q) ^ (1 + b) * 8 ^ β * (64 * D / d ^ 3) =
        (64 * D / d ^ 3) * (K₀ * ((9 / q) ^ (1 + b) * 8 ^ β)) := by ring
    rw [e]
    exact h1.trans (le_mul_of_one_le_right hX hKAB)

/-- Columns meeting a large share of a family: if `∑_{x ∈ S} f x ≥ c #S M` with `f ≤ M` and
`M > 0`, then at least `(c/2) #S` columns have `f x ≥ (c/2) M`. -/
theorem many_heavy {α : Type*} (S : Finset α) (f : α → ℝ) {c M : ℝ} (hM : 0 < M)
    (hf : ∀ x ∈ S, f x ≤ M) (hsum : c * S.card * M ≤ ∑ x ∈ S, f x) :
    c / 2 * S.card ≤ ((S.filter (fun x => c / 2 * M ≤ f x)).card : ℝ) := by
  classical
  by_cases hc : c ≤ 0
  · have : c / 2 * (S.card : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (Nat.cast_nonneg _)
    exact this.trans (Nat.cast_nonneg _)
  push Not at hc
  set H := S.filter (fun x => c / 2 * M ≤ f x) with hH
  set N := S.filter (fun x => ¬ (c / 2 * M ≤ f x)) with hN
  have hsplit : ∑ x ∈ S, f x = ∑ x ∈ H, f x + ∑ x ∈ N, f x :=
    (Finset.sum_filter_add_sum_filter_not S _ f).symm
  have h1 : ∑ x ∈ H, f x ≤ H.card * M := by
    calc ∑ x ∈ H, f x ≤ ∑ _x ∈ H, M :=
          Finset.sum_le_sum (fun x hx => hf x (Finset.mem_filter.mp hx).1)
      _ = H.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcM : 0 ≤ c / 2 * M := by positivity
  have h2 : ∑ x ∈ N, f x ≤ S.card * (c / 2 * M) := by
    calc ∑ x ∈ N, f x ≤ ∑ _x ∈ N, c / 2 * M :=
          Finset.sum_le_sum (fun x hx => le_of_lt (not_le.mp (Finset.mem_filter.mp hx).2))
      _ = N.card * (c / 2 * M) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ S.card * (c / 2 * M) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) hcM
  have h3 : c / 2 * S.card * M ≤ H.card * M := by
    have : c * S.card * M ≤ H.card * M + S.card * (c / 2 * M) := by linarith
    linarith
  exact le_of_mul_le_mul_right h3 hM

/-- Double counting of (line, column) incidences. -/
theorem sum_meets_swap (Yc : ℝ → Finset ℝ) (δ : ℝ) (G : Finset (ℝ × ℝ)) (S : Finset ℝ) :
    ∑ l ∈ G, ((S.filter (fun x => Meets Yc δ x l)).card : ℝ) =
      ∑ x ∈ S, ((G.filter (fun l => Meets Yc δ x l)).card : ℝ) := by
  classical
  simp only [Finset.card_filter, Nat.cast_sum]
  rw [Finset.sum_comm]

/-- The sup-ball degree bound transported through anchor codes. -/
theorem code_degree_le {δ σ q x₀ x₁ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hgap : q ≤ |x₁ - x₀|) (hx₀ : |x₀| ≤ 4) (L G : Finset (ℝ × ℝ)) (hGL : G ⊆ L)
    (hLsep : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → σ ≤ dist l l') (l : ℝ × ℝ) :
    ((G.filter (fun l' => dist (anchorCode x₀ x₁ l) (anchorCode x₀ x₁ l') < δ)).card : ℝ) ≤
      (18 * δ / (q * σ) + 2) ^ 2 := by
  classical
  have hsub : G.filter (fun l' => dist (anchorCode x₀ x₁ l) (anchorCode x₀ x₁ l') < δ) ⊆
      L.filter (fun l' => dist l' l ≤ 9 * δ / q) := by
    intro l' hl'
    obtain ⟨hl'G, hlt⟩ := Finset.mem_filter.mp hl'
    refine Finset.mem_filter.mpr ⟨hGL hl'G, ?_⟩
    have hu : |lineHeight l' x₀ - lineHeight l x₀| ≤ δ := by
      have : |lineHeight l' x₀ - lineHeight l x₀| ≤
          dist (anchorCode x₀ x₁ l) (anchorCode x₀ x₁ l') := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        simp only [anchorCode]
        rw [abs_sub_comm]
        exact le_max_left _ _
      linarith
    have hv : |lineHeight l' x₁ - lineHeight l x₁| ≤ δ := by
      have : |lineHeight l' x₁ - lineHeight l x₁| ≤
          dist (anchorCode x₀ x₁ l) (anchorCode x₀ x₁ l') := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        simp only [anchorCode]
        rw [abs_sub_comm (lineHeight l x₁)]
        exact le_max_right _ _
      linarith
    obtain ⟨h1, h2⟩ := anchorCode_close hq hq1 hgap hx₀ hu hv
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le h1 h2
  have hρ : 0 ≤ 9 * δ / q := by positivity
  have hpack := card_sup_ball_le hσ hρ L hLsep l
  have e : 2 * (9 * δ / q) / σ + 2 = 18 * δ / (q * σ) + 2 := by field_simp; ring
  rw [e] at hpack
  exact (by exact_mod_cast Finset.card_le_card hsub : ((G.filter _).card : ℝ) ≤ _).trans hpack

/-- **The thinned bridge.**  Lines need only be `σ`-separated (sup metric on parameters). -/
theorem tube_model_of_dense_columns_thin {δ σ q d F K₀ b β : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hq : 0 < q) (hq1 : q ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hK₀ : 1 ≤ K₀) (hb : 0 < b) (hβ : 0 ≤ β)
    (L : Finset (ℝ × ℝ)) (I : Finset ℝ) (Yc : ℝ → Finset ℝ)
    (hLne : L.Nonempty) (hIne : I.Nonempty) (hIb : ∀ x ∈ I, |x| ≤ 4)
    (hLb : ∀ l ∈ L, ∀ x ∈ I, |lineHeight l x| ≤ 7 / 2)
    (hLsep : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → σ ≤ dist l l')
    (hYc : ∀ x ∈ I, ((Yc x).card : ℝ) ≤ F)
    (hdens : d * (I.card : ℝ) * L.card ≤
      (((I ×ˢ L).filter (fun p => Meets Yc δ p.1 p.2)).card : ℝ))
    (hspread : ∀ x ∈ I, ((I.filter (fun x' => |x - x'| < q)).card : ℝ) ≤ d ^ 2 / 16 * I.card)
    (hIfr : ∀ z ρ : ℝ, δ ≤ ρ → ((I.filter (fun x => |x - z| ≤ ρ)).card : ℝ) ≤ K₀ * ρ ^ β * I.card)
    (hLfr : ∀ c a ρ : ℝ, δ ≤ ρ →
      ((L.filter (fun l => |l.1 - c| ≤ ρ ∧ |l.2 - a| ≤ ρ)).card : ℝ) ≤ K₀ * ρ ^ (1 + b) * L.card)
    (hquad : F ^ 2 ≤ K₀ * L.card) :
    ∃ (W : Finset (ℝ × ℝ)) (Y0 Y1 X : Finset ℝ) (Wx : ℝ → Finset (ℝ × ℝ)) (Yx : ℝ → Finset ℝ),
      W.Nonempty ∧ (∀ w ∈ W, |w.1| ≤ 7 / 2 ∧ |w.2| ≤ 7 / 2) ∧
      (∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → δ ≤ dist w w') ∧
      (Y0.card : ℝ) ≤ F ∧ (Y1.card : ℝ) ≤ F ∧
      (∀ w ∈ W, ∃ y ∈ Y0, |w.1 - y| ≤ δ) ∧ (∀ w ∈ W, ∃ y ∈ Y1, |w.2 - y| ≤ δ) ∧
      (∀ x y ρ : ℝ, δ ≤ ρ →
        ((W.filter (fun w => |w.1 - x| ≤ ρ ∧ |w.2 - y| ≤ ρ)).card : ℝ) ≤
          tubeKD K₀ q b β d (⌈(18 * δ / (q * σ) + 2) ^ 2⌉₊ : ℝ) * ρ ^ (1 + b) * W.card) ∧
      F ^ 2 ≤ tubeKD K₀ q b β d (⌈(18 * δ / (q * σ) + 2) ^ 2⌉₊ : ℝ) * W.card ∧
      X.Nonempty ∧ (∀ τ ∈ X, |τ| ≤ 8 / q) ∧
      (∀ x ρ : ℝ, δ ≤ ρ →
        ((X.filter (fun τ => dist τ x ≤ ρ)).card : ℝ) ≤
          tubeKD K₀ q b β d (⌈(18 * δ / (q * σ) + 2) ^ 2⌉₊ : ℝ) * ρ ^ β * X.card) ∧
      (∀ τ ∈ X, Wx τ ⊆ W) ∧
      (∀ τ ∈ X, (W.card : ℝ) ≤
        tubeKD K₀ q b β d (⌈(18 * δ / (q * σ) + 2) ^ 2⌉₊ : ℝ) * (Wx τ).card) ∧
      (∀ τ ∈ X, ((Yx τ).card : ℝ) ≤ F) ∧
      (∀ τ ∈ X, ∀ w ∈ Wx τ, ∃ y ∈ Yx τ, |hgt w τ - y| ≤ δ) := by
  classical
  set Dn : ℕ := ⌈(18 * δ / (q * σ) + 2) ^ 2⌉₊ with hDn
  set D : ℝ := (Dn : ℝ) with hD
  have hD1 : 1 ≤ D := by
    have h2 : (1 : ℝ) ≤ (18 * δ / (q * σ) + 2) ^ 2 := by
      have : (2 : ℝ) ≤ 18 * δ / (q * σ) + 2 := by
        have : 0 ≤ 18 * δ / (q * σ) := by positivity
        linarith
      nlinarith
    exact h2.trans (Nat.le_ceil _)
  have hDpos : 0 < D := by linarith
  obtain ⟨hK1, hK2, hK3, hK4, hK5⟩ := tubeKD_bounds (β := β) hK₀ hq hq1 hb hβ hd hd1 hD1
  set Kt := tubeKD K₀ q b β d D with hKt
  -- endpoint selection
  obtain ⟨x₀, hx₀, x₁, hx₁, G, hGL, S, hSI, hnb, hGR, hGcard, hScard, hS⟩ :=
    dense_endpoint_finset I L hIne hLne (fun x l => Meets Yc δ x l) (fun x x' => |x - x'| < q)
      hd hd1 hdens (fun x hx => hspread x hx)
  push Not at hnb
  have hgap : q ≤ |x₁ - x₀| := by rw [abs_sub_comm]; exact hnb
  have hne : x₀ ≠ x₁ := by
    intro h; rw [h, sub_self, abs_zero] at hgap; linarith
  have hx₀b : |x₀| ≤ 4 := hIb x₀ hx₀
  have hne' : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hxx : ∀ x, x₀ + anchorParam x₀ x₁ x * (x₁ - x₀) = x := by
    intro x; simp only [anchorParam]; field_simp; ring
  -- greedy thinning of the codes
  set R : ℝ × ℝ → ℝ × ℝ → Prop :=
    fun l l' => dist (anchorCode x₀ x₁ l) (anchorCode x₀ x₁ l') < δ with hR
  set w : ℝ × ℝ → ℝ := fun l => ((S.filter (fun x => Meets Yc δ x l)).card : ℝ) with hw
  have hdeg : ∀ l ∈ G, (G.filter (R l)).card ≤ Dn := by
    intro l _
    have h := code_degree_le hδ hσ hq hq1 hgap hx₀b L G hGL hLsep l
    have h2 : ((G.filter (R l)).card : ℝ) ≤ Dn := h.trans (Nat.le_ceil _)
    exact_mod_cast h2
  obtain ⟨G₂, hG₂G, hG₂ind, hG₂w⟩ := greedy_thin R (fun l => by simp [hR, hδ])
    (fun l l' h => by simpa [hR, dist_comm] using h) Dn w (fun _ => Nat.cast_nonneg _) G hdeg
  -- incidence counts
  have hGpos : (0 : ℝ) < G.card := by
    have hLpos : (0 : ℝ) < L.card := by exact_mod_cast hLne.card_pos
    have : 0 < d ^ 2 / 8 * (L.card : ℝ) := by positivity
    linarith
  have hIpos : (0 : ℝ) < I.card := by exact_mod_cast hIne.card_pos
  have hSpos : (0 : ℝ) < S.card := by
    have : 0 < d / 4 * (I.card : ℝ) := by positivity
    linarith
  have hsumG : d / 8 * (G.card : ℝ) * S.card ≤ ∑ l ∈ G, w l := by
    rw [hw, sum_meets_swap]
    calc d / 8 * (G.card : ℝ) * S.card = ∑ _x ∈ S, d / 8 * (G.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ x ∈ S, ((G.filter (fun l => Meets Yc δ x l)).card : ℝ) :=
          Finset.sum_le_sum (fun x hx => (hS x hx).2.2)
  have hsumG₂ : d / (8 * D) * (G.card : ℝ) * S.card ≤ ∑ l ∈ G₂, w l := by
    have h := hsumG.trans hG₂w
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 8)] at h
    nlinarith
  have hwS : ∀ l, w l ≤ S.card := fun l => by
    simp only [hw]; exact_mod_cast Finset.card_filter_le _ _
  have hG₂pos : (0 : ℝ) < G₂.card := by
    have h1 : 0 < d / (8 * D) * (G.card : ℝ) * S.card := by positivity
    have h2 : ∑ l ∈ G₂, w l ≤ G₂.card * S.card := by
      calc ∑ l ∈ G₂, w l ≤ ∑ _l ∈ G₂, (S.card : ℝ) := Finset.sum_le_sum (fun l _ => hwS l)
        _ = G₂.card * S.card := by rw [Finset.sum_const, nsmul_eq_mul]
    by_contra h0
    push Not at h0
    have : (G₂.card : ℝ) = 0 := le_antisymm h0 (Nat.cast_nonneg _)
    rw [this, zero_mul] at h2
    linarith
  have hG₂ne : G₂.Nonempty := Finset.card_pos.mp (by exact_mod_cast hG₂pos)
  have hG₂big : d / (8 * D) * (G.card : ℝ) ≤ G₂.card := by
    have h2 : ∑ l ∈ G₂, w l ≤ G₂.card * S.card := by
      calc ∑ l ∈ G₂, w l ≤ ∑ _l ∈ G₂, (S.card : ℝ) := Finset.sum_le_sum (fun l _ => hwS l)
        _ = G₂.card * S.card := by rw [Finset.sum_const, nsmul_eq_mul]
    have := hsumG₂.trans h2
    exact le_of_mul_le_mul_right this hSpos
  -- heavy columns for the thinned family
  have hsum2 : d / (8 * D) * (S.card : ℝ) * G₂.card ≤
      ∑ x ∈ S, ((G₂.filter (fun l => Meets Yc δ x l)).card : ℝ) := by
    rw [← sum_meets_swap]
    have hGG : d / (8 * D) * (S.card : ℝ) * G₂.card ≤ d / (8 * D) * (G.card : ℝ) * S.card := by
      have hc : 0 ≤ d / (8 * D) := by positivity
      have hGG' : (G₂.card : ℝ) ≤ G.card := by exact_mod_cast Finset.card_le_card hG₂G
      have hcS : 0 ≤ d / (8 * D) * (S.card : ℝ) := mul_nonneg hc (Nat.cast_nonneg _)
      calc d / (8 * D) * (S.card : ℝ) * G₂.card ≤ d / (8 * D) * (S.card : ℝ) * G.card :=
            mul_le_mul_of_nonneg_left hGG' hcS
        _ = d / (8 * D) * (G.card : ℝ) * S.card := by ring
    exact hGG.trans hsumG₂
  have hheavy := many_heavy S (fun x => ((G₂.filter (fun l => Meets Yc δ x l)).card : ℝ))
    (c := d / (8 * D)) hG₂pos (fun x _ => by exact_mod_cast Finset.card_filter_le _ _) hsum2
  set S₂ := S.filter (fun x => d / (8 * D) / 2 * (G₂.card : ℝ) ≤
    ((G₂.filter (fun l => Meets Yc δ x l)).card : ℝ)) with hS₂
  have hS₂pos : (0 : ℝ) < S₂.card := by
    have : 0 < d / (8 * D) / 2 * (S.card : ℝ) := by positivity
    linarith
  have hS₂ne : S₂.Nonempty := Finset.card_pos.mp (by exact_mod_cast hS₂pos)
  have hS₂I : S₂ ⊆ I := fun x hx => hSI (Finset.mem_filter.mp hx).1
  -- injectivity of the code on the thinned family
  have hinj : Set.InjOn (anchorCode x₀ x₁) (↑G₂ : Set (ℝ × ℝ)) := by
    intro l hl l' hl' heq
    by_contra hll'
    have := hG₂ind l hl l' hl' hll'
    apply this
    simp only [hR, heq, dist_self, hδ]
  set W := G₂.image (anchorCode x₀ x₁) with hWdef
  have hWcard : W.card = G₂.card := Finset.card_image_of_injOn hinj
  -- size comparisons
  have hLW : (L.card : ℝ) ≤ 64 * D / d ^ 3 * W.card := by
    rw [hWcard]
    have h1 : d ^ 2 / 8 * (L.card : ℝ) ≤ G.card := hGcard
    have h2 : d / (8 * D) * (G.card : ℝ) ≤ G₂.card := hG₂big
    have h3 : d / (8 * D) * (d ^ 2 / 8 * (L.card : ℝ)) ≤ G₂.card :=
      le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
    have e : d / (8 * D) * (d ^ 2 / 8 * (L.card : ℝ)) = d ^ 3 / (64 * D) * L.card := by
      field_simp; ring
    rw [e] at h3
    have h4 := le_div_mul_of_mul_le (by positivity : (0 : ℝ) < d ^ 3 / (64 * D)) h3
    have e2 : 1 / (d ^ 3 / (64 * D)) = 64 * D / d ^ 3 := by field_simp
    rwa [e2] at h4
  have hIX : (I.card : ℝ) ≤ 64 * D / d ^ 2 * S₂.card := by
    have h1 : d / 4 * (I.card : ℝ) ≤ S.card := hScard
    have h2 : d / (8 * D) / 2 * (S.card : ℝ) ≤ S₂.card := hheavy
    have h3 : d / (8 * D) / 2 * (d / 4 * (I.card : ℝ)) ≤ S₂.card :=
      le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
    have e : d / (8 * D) / 2 * (d / 4 * (I.card : ℝ)) = d ^ 2 / (64 * D) * I.card := by
      field_simp; ring
    rw [e] at h3
    have h4 := le_div_mul_of_mul_le (by positivity : (0 : ℝ) < d ^ 2 / (64 * D)) h3
    have e2 : 1 / (d ^ 2 / (64 * D)) = 64 * D / d ^ 2 := by field_simp
    rwa [e2] at h4
  refine ⟨W, Yc x₀, Yc x₁, S₂.image (anchorParam x₀ x₁),
    fun τ => (G₂.filter (fun l => Meets Yc δ (x₀ + τ * (x₁ - x₀)) l)).image (anchorCode x₀ x₁),
    fun τ => Yc (x₀ + τ * (x₁ - x₀)), hG₂ne.image _, ?_, ?_, hYc x₀ hx₀, hYc x₁ hx₁, ?_, ?_,
    ?_, ?_, hS₂ne.image _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w' hw'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw'
    exact ⟨hLb l (hGL (hG₂G hl)) x₀ hx₀, hLb l (hGL (hG₂G hl)) x₁ hx₁⟩
  · intro w₁ hw₁ w₂ hw₂ hww
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw₁
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hw₂
    have hll' : l ≠ l' := fun h => hww (by rw [h])
    have := hG₂ind l hl l' hl' hll'
    simp only [hR, not_lt] at this
    exact this
  · intro w' hw'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw'
    exact (hGR l (hG₂G hl)).1
  · intro w' hw'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw'
    exact (hGR l (hG₂G hl)).2
  · -- square counts
    intro x y ρ hρ
    set c₀ := (y - x) / (x₁ - x₀) with hc₀
    set a₀ := x - c₀ * x₀ with ha₀
    have hsub : W.filter (fun w' => |w'.1 - x| ≤ ρ ∧ |w'.2 - y| ≤ ρ) ⊆
        (L.filter (fun l => |l.1 - c₀| ≤ 9 * ρ / q ∧ |l.2 - a₀| ≤ 9 * ρ / q)).image
          (anchorCode x₀ x₁) := by
      intro w' hw'
      obtain ⟨hwW, hw1, hw2⟩ := by simpa using hw'
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hwW
      refine Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨hGL (hG₂G hl), ?_⟩, rfl⟩
      have hx1' : lineHeight (c₀, a₀) x₀ = x := by
        simp only [lineHeight, ha₀]; ring
      have hy1' : lineHeight (c₀, a₀) x₁ = y := by
        simp only [lineHeight, ha₀, hc₀]; field_simp; ring
      have hu : |lineHeight l x₀ - lineHeight (c₀, a₀) x₀| ≤ ρ := by
        rw [hx1']; simpa [anchorCode] using hw1
      have hv : |lineHeight l x₁ - lineHeight (c₀, a₀) x₁| ≤ ρ := by
        rw [hy1']; simpa [anchorCode] using hw2
      exact anchorCode_close hq hq1 hgap hx₀b hu hv
    have hρpos : 0 < ρ := lt_of_lt_of_le hδ hρ
    have hρ' : δ ≤ 9 * ρ / q := hρ.trans (le_nine_mul_div hρpos.le hq hq1)
    have hcount := hLfr c₀ a₀ (9 * ρ / q) hρ'
    have e1 : (9 * ρ / q) ^ (1 + b) = (9 / q) ^ (1 + b) * ρ ^ (1 + b) := by
      rw [show 9 * ρ / q = (9 / q) * ρ by ring, Real.mul_rpow (by positivity) hρpos.le]
    calc ((W.filter (fun w' => |w'.1 - x| ≤ ρ ∧ |w'.2 - y| ≤ ρ)).card : ℝ)
        ≤ (((L.filter (fun l => |l.1 - c₀| ≤ 9 * ρ / q ∧ |l.2 - a₀| ≤ 9 * ρ / q)).image
            (anchorCode x₀ x₁)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((L.filter (fun l => |l.1 - c₀| ≤ 9 * ρ / q ∧ |l.2 - a₀| ≤ 9 * ρ / q)).card : ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ ≤ K₀ * (9 * ρ / q) ^ (1 + b) * L.card := hcount
      _ = K₀ * (9 / q) ^ (1 + b) * ρ ^ (1 + b) * L.card := by rw [e1]; ring
      _ ≤ K₀ * (9 / q) ^ (1 + b) * ρ ^ (1 + b) * (64 * D / d ^ 3 * W.card) :=
          mul_le_mul_of_nonneg_left hLW (by positivity)
      _ = (K₀ * (9 / q) ^ (1 + b) * (64 * D / d ^ 3)) * ρ ^ (1 + b) * W.card := by ring
      _ ≤ Kt * ρ ^ (1 + b) * W.card := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right hK1 (by positivity)
  · calc F ^ 2 ≤ K₀ * L.card := hquad
      _ ≤ K₀ * (64 * D / d ^ 3 * W.card) := mul_le_mul_of_nonneg_left hLW (by linarith)
      _ = (K₀ * (64 * D / d ^ 3)) * W.card := by ring
      _ ≤ Kt * W.card := mul_le_mul_of_nonneg_right hK2 (Nat.cast_nonneg _)
  · intro τ hτ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hτ
    exact anchorParam_abs_le hq (hIb x (hS₂I hx)) hx₀b hgap
  · -- column Frostman
    intro z ρ hρ
    have hρpos : 0 < ρ := lt_of_lt_of_le hδ hρ
    set z' := x₀ + z * (x₁ - x₀) with hz'
    have hgap8 : |x₁ - x₀| ≤ 8 := by
      calc |x₁ - x₀| ≤ |x₁| + |x₀| := abs_sub _ _
        _ ≤ 8 := by linarith [hIb x₁ hx₁]
    have hsub : (S₂.image (anchorParam x₀ x₁)).filter (fun τ => dist τ z ≤ ρ) ⊆
        ((I.filter (fun x => |x - z'| ≤ 8 * ρ))).image (anchorParam x₀ x₁) := by
      intro τ hτ
      obtain ⟨hτS, hτz⟩ := Finset.mem_filter.mp hτ
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hτS
      refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hS₂I hx, ?_⟩, rfl⟩
      have hxz : x - z' = (anchorParam x₀ x₁ x - z) * (x₁ - x₀) := by
        simp only [anchorParam, hz']; field_simp; ring
      rw [hxz, abs_mul]
      rw [Real.dist_eq] at hτz
      calc |anchorParam x₀ x₁ x - z| * |x₁ - x₀| ≤ ρ * 8 :=
            mul_le_mul hτz hgap8 (abs_nonneg _) hρpos.le
        _ = 8 * ρ := by ring
    have hcount := hIfr z' (8 * ρ) (by linarith)
    have hXcard : ((S₂.image (anchorParam x₀ x₁)).card : ℝ) = S₂.card := by
      rw [Finset.card_image_of_injective _ (anchorParam_injective hne)]
    have e8 : (8 * ρ) ^ β = 8 ^ β * ρ ^ β := Real.mul_rpow (by norm_num) hρpos.le
    rw [hXcard]
    calc (((S₂.image (anchorParam x₀ x₁)).filter (fun τ => dist τ z ≤ ρ)).card : ℝ)
        ≤ (((I.filter (fun x => |x - z'| ≤ 8 * ρ)).image (anchorParam x₀ x₁)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((I.filter (fun x => |x - z'| ≤ 8 * ρ)).card : ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ ≤ K₀ * (8 * ρ) ^ β * I.card := hcount
      _ = K₀ * 8 ^ β * ρ ^ β * I.card := by rw [e8]; ring
      _ ≤ K₀ * 8 ^ β * ρ ^ β * (64 * D / d ^ 2 * S₂.card) :=
          mul_le_mul_of_nonneg_left hIX (by positivity)
      _ = (K₀ * 8 ^ β * (64 * D / d ^ 2)) * ρ ^ β * S₂.card := by ring
      _ ≤ Kt * ρ ^ β * S₂.card := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right hK3 (by positivity)
  · intro τ _ w' hw'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw'
    exact Finset.mem_image.mpr ⟨l, (Finset.mem_filter.mp hl).1, rfl⟩
  · intro τ hτ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hτ
    dsimp only
    rw [hxx]
    have hdeg2 := (Finset.mem_filter.mp hx).2
    have hcardimg : (((G₂.filter (fun l => Meets Yc δ x l)).image (anchorCode x₀ x₁)).card : ℝ) =
        ((G₂.filter (fun l => Meets Yc δ x l)).card : ℝ) := by
      rw [Finset.card_image_of_injOn (hinj.mono (fun l hl => (Finset.mem_filter.mp hl).1))]
    rw [hcardimg, hWcard]
    have hG8 : (G₂.card : ℝ) ≤ 16 * D / d * ((G₂.filter (fun l => Meets Yc δ x l)).card : ℝ) := by
      have h := le_div_mul_of_mul_le (by positivity : (0 : ℝ) < d / (8 * D) / 2) hdeg2
      have e : 1 / (d / (8 * D) / 2) = 16 * D / d := by field_simp; ring
      rwa [e] at h
    calc (G₂.card : ℝ) ≤ 16 * D / d * ((G₂.filter (fun l => Meets Yc δ x l)).card : ℝ) := hG8
      _ ≤ Kt * ((G₂.filter (fun l => Meets Yc δ x l)).card : ℝ) :=
          mul_le_mul_of_nonneg_right hK4 (Nat.cast_nonneg _)
  · intro τ hτ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hτ
    dsimp only
    rw [hxx]
    exact hYc x (hS₂I hx)
  · intro τ hτ w' hw'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hτ
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw'
    have hl' := (Finset.mem_filter.mp hl).2
    dsimp only
    rw [hxx] at hl' ⊢
    obtain ⟨y, hy, hly⟩ := hl'
    refine ⟨y, hy, ?_⟩
    rw [hgt_anchorCode hne]
    exact hly

/-- **Case A in tube coordinates, with thinning.**  For positive `e, b, β` there are `ζ, δ₀` such
that `σ`-separated column-dense tube data at a scale `δ ≤ δ₀` with `F ≤ δ^(-(1-e))`,
`4 ≤ δ^(-ζ/2)` and `4 Kt (2 (1 + 8/q)²)^β 2^(1+b) ≤ δ^(-ζ)`, where
`Kt = tubeKD K₀ q b β d ⌈(18 δ/(q σ) + 2)²⌉`, cannot exist. -/
theorem dense_columns_thin_false {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ ζ δ₀ : ℝ, 0 < ζ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ ∀ (δ σ q d F K₀ : ℝ),
      0 < δ → δ ≤ δ₀ → 0 < σ → 0 < q → q ≤ 1 → 0 < d → d ≤ 1 → 1 ≤ K₀ → 1 ≤ F →
      F ≤ δ ^ (-(1 - e)) →
      (4 * tubeKD K₀ q b β d (⌈(18 * δ / (q * σ) + 2) ^ 2⌉₊ : ℝ) * (2 * (1 + 8 / q) ^ 2) ^ β) *
          2 ^ (1 + b) ≤ δ ^ (-ζ) →
      4 ≤ δ ^ (-(ζ / 2)) →
      ∀ (L : Finset (ℝ × ℝ)) (I : Finset ℝ) (Yc : ℝ → Finset ℝ),
      L.Nonempty → I.Nonempty → (∀ x ∈ I, |x| ≤ 4) →
      (∀ l ∈ L, ∀ x ∈ I, |lineHeight l x| ≤ 7 / 2) →
      (∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → σ ≤ dist l l') →
      (∀ x ∈ I, ((Yc x).card : ℝ) ≤ F) →
      d * (I.card : ℝ) * L.card ≤
        (((I ×ˢ L).filter (fun p : ℝ × (ℝ × ℝ) => Meets Yc δ p.1 p.2)).card : ℝ) →
      (∀ x ∈ I, ((I.filter (fun x' => |x - x'| < q)).card : ℝ) ≤ d ^ 2 / 16 * I.card) →
      (∀ z ρ : ℝ, δ ≤ ρ → ((I.filter (fun x => |x - z| ≤ ρ)).card : ℝ) ≤ K₀ * ρ ^ β * I.card) →
      (∀ c a ρ : ℝ, δ ≤ ρ →
        ((L.filter (fun l => |l.1 - c| ≤ ρ ∧ |l.2 - a| ≤ ρ)).card : ℝ) ≤
          K₀ * ρ ^ (1 + b) * L.card) →
      F ^ 2 ≤ K₀ * L.card → False := by
  obtain ⟨ζ, δ₀, hζ, hδ₀, hδ₀2, hfalse⟩ := tube_model_false he hb hβ
  refine ⟨ζ, δ₀, hζ, hδ₀, hδ₀2, ?_⟩
  intro δ σ q d F K₀ hδ hδδ₀ hσ hq hq1 hd hd1 hK₀ hF hFe hloss h4 L I Yc hLne hIne hIb hLb hLsep
    hYc hdens hspread hIfr hLfr hquad
  obtain ⟨W, Y0, Y1, X, Wx, Yx, hWne, hWb, hWsep, hY0, hY1, hW0, hW1, hsq, hWbig, hXne, hXB,
    hXfr, hWx, hWxbig, hYx, hcovx⟩ :=
    tube_model_of_dense_columns_thin hδ hσ hq hq1 hd hd1 hK₀ hb hβ.le L I Yc hLne hIne hIb hLb
      hLsep hYc hdens hspread hIfr hLfr hquad
  have hD1 : (1 : ℝ) ≤ (⌈(18 * δ / (q * σ) + 2) ^ 2⌉₊ : ℝ) := by
    have h2 : (1 : ℝ) ≤ (18 * δ / (q * σ) + 2) ^ 2 := by
      have : (2 : ℝ) ≤ 18 * δ / (q * σ) + 2 := by
        have : 0 ≤ 18 * δ / (q * σ) := by positivity
        linarith
      nlinarith
    exact h2.trans (Nat.le_ceil _)
  obtain ⟨_, _, _, _, hKt⟩ := tubeKD_bounds (β := β) hK₀ hq hq1 hb hβ.le hd hd1 hD1
  have hB : 1 ≤ 8 / q := by rw [le_div_iff₀ hq]; linarith
  exact hfalse δ F _ (8 / q) hδ hδδ₀ hB hKt hF hFe hloss h4 W hWne hWb hWsep
    Y0 Y1 hY0 hY1 hW0 hW1 hsq hWbig X hXne hXB hXfr Wx hWx hWxbig Yx hYx hcovx

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
