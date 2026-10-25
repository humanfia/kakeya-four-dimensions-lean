-- Adapted from this LOT tree, o206, session x0709, commit f7d6ac58,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Front.lean.
-- Adapted from this obligation, session x0713, commit 64983e61,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Front.lean.
-- The preparation namespace TE is identified here with Construction.

import Submission.Obl.k4_homogeneous_native_pair_preparation.KnownSample
import Submission.Obl.k4_homogeneous_native_pair_preparation.ScaleClass
import Submission.Obl.k4_matching_homogeneous_records.Dyadic

/-!
# The front end of the per-sample step

From one old known sample (`KnownSample`, tolerance `ε`) we

* split the old time exponent as `T + s` with `N^e ≤ 2^s ≤ 2 N^e` and
  `2^T ≤ N^((h - e) + ε)` (`exists_coarsened_horizon`);
* restrict to the heaviest dyadic scale class of the chart matrices (x0472's
  `Construction.exists_heavy_class` and `Construction.scaleClass`), losing the number `ncls` of classes in
  the coverage, and reindex the class charts and the lists;

and record the result as a `ClassSample` (`exists_classSample`).  `ClassSample.toPrepData`
builds x0472's `Construction.PrepData` from it and `ClassSample.hyp` proves `Construction.PrepData.Hyp`.
The true floors and the class coverage stay available as fields of the `ClassSample`.
-/

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Filter
open scoped ENNReal

/-! ### Time coarsening -/

-- Adapted from LOT tree o-074, obligation o114 (`k4_terminal_representative_atlas`),
-- session branch x0680 at commit bdf7e715, file
-- Submission/Obl/k4_terminal_representative_atlas/Preparation/TimeCoarsening.lean
-- (`dyadic_gain_le`, `exists_coarsened_horizon`); it uses the accepted o055
-- `dyadicHeight`.

/-- The rounded-up gain fits in an old dyadic time exponent whenever the corresponding
real power fits. -/
theorem dyadic_gain_le {N e : ℝ} {T₀ : ℕ} (hN : 1 ≤ N)
    (hgain : N ^ e ≤ (2 : ℝ) ^ T₀) :
    Submission.Obl.k4_matching_homogeneous_records.dyadicHeight N e ≤ T₀ := by
  unfold Submission.Obl.k4_matching_homogeneous_records.dyadicHeight
  apply Nat.ceil_le.mpr
  calc Real.logb 2 (N ^ e) ≤ Real.logb 2 ((2 : ℝ) ^ T₀) :=
      Real.logb_le_logb_of_le (by norm_num)
        (Real.rpow_pos_of_pos (by linarith) _) hgain
    _ = T₀ := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- Choose the coarse exponent and the exact integer gain together. -/
theorem exists_coarsened_horizon {N e h τ : ℝ} {T₀ : ℕ} (hN : 1 ≤ N)
    (he : 0 ≤ e) (hgap : e ≤ h - τ)
    (hlow : N ^ (h - τ) ≤ (2 : ℝ) ^ T₀)
    (hupp : (2 : ℝ) ^ T₀ ≤ N ^ (h + τ)) :
    ∃ T s : ℕ, T₀ = T + s ∧
      N ^ e ≤ (2 : ℝ) ^ s ∧ (2 : ℝ) ^ s ≤ 2 * N ^ e ∧
      (2 : ℝ) ^ T₀ / (2 * N ^ e) ≤ (2 : ℝ) ^ T ∧
      (2 : ℝ) ^ T ≤ N ^ ((h - e) + τ) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNe : 0 < N ^ e := Real.rpow_pos_of_pos hN0 _
  let s := Submission.Obl.k4_matching_homogeneous_records.dyadicHeight N e
  have hs : s ≤ T₀ := dyadic_gain_le hN
    ((Real.rpow_le_rpow_of_exponent_le hN hgap).trans hlow)
  let T := T₀ - s
  have hT : T₀ = T + s := (Nat.sub_add_cancel hs).symm
  obtain ⟨hsl, hsu⟩ := Submission.Obl.k4_matching_homogeneous_records.dyadicHeight_bounds hN he
  have hfactor : (2 : ℝ) ^ T₀ = (2 : ℝ) ^ T * (2 : ℝ) ^ s := by rw [hT, pow_add]
  refine ⟨T, s, hT, hsl, hsu, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity : 0 < 2 * N ^ e), hfactor]
    exact mul_le_mul_of_nonneg_left hsu (by positivity)
  · have hdiv : (2 : ℝ) ^ T ≤ (2 : ℝ) ^ T₀ / N ^ e := by
      rw [le_div_iff₀ hNe, hfactor]
      exact mul_le_mul_of_nonneg_left hsl (by positivity)
    calc (2 : ℝ) ^ T ≤ (2 : ℝ) ^ T₀ / N ^ e := hdiv
      _ ≤ N ^ (h + τ) / N ^ e := div_le_div_of_nonneg_right hupp hNe.le
      _ = N ^ ((h - e) + τ) := by
        rw [← Real.rpow_sub hN0]
        congr 1
        ring

/-! ### Weakening the extra clause of `chart` -/

theorem chart_of_ex {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex ex' : Prop}
    (h : chart Nk M D κ T j r Bv Ev c u Q R A F ex) (hex : ex → ex') :
    chart Nk M D κ T j r Bv Ev c u Q R A F ex' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hex h12⟩

theorem chart_ex {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : chart Nk M D κ T j r Bv Ev c u Q R A F ex) : ex := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12⟩ := h
  exact h12

theorem chart_det {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : chart Nk M D κ T j r Bv Ev c u Q R A F ex) : Q.det ≠ 0 := h.1

theorem chart_frame {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : chart Nk M D κ T j r Bv Ev c u Q R A F ex) :
    (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ Nk ^ M := h.2.2.1

/-! ### One scale class of an old known sample -/

/-- An old known sample restricted to one dyadic scale class of its chart matrices, with its
old time exponent split as `T + s` (`2^s` about `N^e`).  The fields `hchart`, `hdisj`,
`hlst`, `hlstfmt` are those of `known` for the class charts and the restricted lists; the
coverage `hcov` loses the number `ncls` of classes. -/
structure ClassSample (Nk : ℝ) (Wk : ℕ) (ωk : Fin Wk → ℝ)
    (νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))) (Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (Bk : Fin Wk → ℝ) (f : ℝ → ℝ) (L h : ℝ) (M D : ℕ) (ε e : ℝ) where
  κ : ℝ
  κ_one : 1 ≤ κ
  κ_le : κ ≤ Nk ^ ε
  T : ℕ
  s : ℕ
  C : ℕ
  γ : Fin C → Fin Wk
  j : Fin C → Fin (2 ^ (T + s))
  c : Fin C → EuclideanSpace ℝ (Fin 2)
  u : Fin C → EuclideanSpace ℝ (Fin 2)
  Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ
  R : Fin C → MvPolynomial (Fin 4) ℝ
  A : Fin C → Set (ℕ × (Fin 6 → ℝ))
  F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  lst : Fin Wk → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)
  R₁ : ℝ
  R₂ : ℝ
  ncls : ℕ
  hs₁ : Nk ^ e ≤ (2 : ℝ) ^ s
  hs₂ : (2 : ℝ) ^ s ≤ 2 * Nk ^ e
  hT : (2 : ℝ) ^ T ≤ Nk ^ ((h - e) + ε)
  hT₁ : Nk ^ (h - ε) ≤ (2 : ℝ) ^ (T + s)
  hT₂ : (2 : ℝ) ^ (T + s) ≤ Nk ^ (h + ε)
  hC : (C : ℝ) ≤ Nk ^ M
  hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')
  hchart : ∀ b, chart Nk M D κ (T + s) ((j b : ℕ) : ℝ) L (Bk (γ b)) (Ek (γ b)) (c b) (u b)
    (Q b) (R b) (A b) (F b)
    (ENNReal.ofReal (Nk ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ (T + s) * κ)) ≤
        ((νk (γ b)).prod MeasureTheory.volume) (F b) ∧
      ∀ p ∈ F b, b ∈ lst (γ b) (obs (Bk (γ b)) (δ Nk L) p))
  hcov : ENNReal.ofReal κ⁻¹ ≤
    (ncls : ℝ≥0∞) * ∑ b, ENNReal.ofReal (ωk (γ b)) * ((νk (γ b)).prod MeasureTheory.volume) (F b)
  hncls : (ncls : ℝ) ≤ (2 * (3 * (M : ℝ) + 1) * Real.logb 2 Nk + 2) ^ 2
  hlst : ∀ γ₀ o, ((lst γ₀ o).card : ℝ) ≤ κ
  hlstfmt : ∀ γ₀ b, MeasurableSet {p | b ∈ lst γ₀ (obs (Bk γ₀) (δ Nk L) p)} ∧
    ∀ i, fmt 7 (Nk ^ M) D {r : Fin 7 → ℝ |
      b ∈ lst γ₀ (obs (Bk γ₀) (δ Nk L) ((i, fun z : Fin 6 => r z.castSucc), r 6))}
  r₁lo : ∀ b, R₁ ≤ Construction.r₁ (Q b)
  r₁hi : ∀ b, Construction.r₁ (Q b) < 2 * R₁
  r₂lo : ∀ b, R₂ ≤ Construction.r₂ (Q b)
  r₂hi : ∀ b, Construction.r₂ (Q b) < 2 * R₂
  R₁pos : 0 < R₁
  R₂pos : 0 < R₂
  R21 : R₂ ≤ R₁

/-- The chart matrices of an old known sample lie in the dyadic class grid of exponent
`3 M + 1`. -/
theorem scaleClass_mem_classGrid {Nk : ℝ} {M : ℕ} (hN : 2 ≤ Nk)
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (hX : (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ Nk ^ M) :
    Construction.scaleClass Q ∈ Construction.magnitudeGrid Nk (3 * (M : ℝ) + 1) ×ˢ
      Construction.magnitudeGrid Nk (3 * (M : ℝ) + 1) := by
  have hN1 : (1 : ℝ) ≤ Nk := by linarith
  have hX1 : (1 : ℝ) ≤ Nk ^ M := one_le_pow₀ hN1
  refine Construction.scaleClass_mem_grid hQ hX1 (by linarith) hX ?_
  have hcast : Nk ^ (3 * (M : ℝ) + 1) = Nk ^ (3 * M + 1) := by
    rw [← Real.rpow_natCast]
    norm_num
  have hpow : (Nk ^ M) ^ 3 = Nk ^ (3 * M) := by rw [← pow_mul, mul_comm]
  rw [hcast, hpow, pow_succ]
  have : 0 ≤ Nk ^ (3 * M) := by positivity
  nlinarith

/-- **The front end**: an old known sample yields a class sample. -/
theorem exists_classSample {Nk : ℝ} {Wk : ℕ} {ωk : Fin Wk → ℝ}
    {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))} {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Bk : Fin Wk → ℝ} {f : ℝ → ℝ} {L h : ℝ} {M D : ℕ} {ε : ℝ}
    (S : KnownSample Nk Wk ωk νk Ek Bk f L h M D ε) (hN : 2 ≤ Nk) {e : ℝ} (he : 0 ≤ e)
    (hgap : e ≤ h - ε) :
    Nonempty (ClassSample Nk Wk ωk νk Ek Bk f L h M D ε e) := by
  classical
  obtain ⟨κ, κ_one, κ_le, T₀, C', γ, j, c, u, Q, R, A, F, lst, hT₁, hT₂, hC, hdisj, hchart,
    hcov, hlst, hlstfmt⟩ := S
  have hN1 : (1 : ℝ) ≤ Nk := by linarith
  obtain ⟨T, s, rfl, hs₁, hs₂, -, hT⟩ := exists_coarsened_horizon hN1 he hgap hT₁ hT₂
  -- the class grid
  set G := Construction.magnitudeGrid Nk (3 * (M : ℝ) + 1) ×ˢ Construction.magnitudeGrid Nk (3 * (M : ℝ) + 1)
    with hGdef
  have hcls : ∀ b, Construction.scaleClass (Q b) ∈ G := fun b =>
    scaleClass_mem_classGrid hN (chart_det (hchart b)) (chart_frame (hchart b))
  set w : Fin C' → ℝ≥0∞ := fun b =>
    ENNReal.ofReal (ωk (γ b)) * ((νk (γ b)).prod MeasureTheory.volume) (F b) with hw
  have hκpos : (0 : ℝ) < κ⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one κ_one)
  have hcov0 : (0 : ℝ≥0∞) < ∑ b, w b := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hκpos) hcov
  have hC'pos : 0 < C' := by
    rcases Nat.eq_zero_or_pos C' with h0 | h0
    · subst h0; simp at hcov0
    · exact h0
  have hGne : G.Nonempty := ⟨_, hcls ⟨0, hC'pos⟩⟩
  obtain ⟨⟨i₁, i₂⟩, -, hheavy⟩ := Construction.exists_heavy_class w (fun b => Construction.scaleClass (Q b)) G hcls hGne
  -- the class charts
  let cls := {b : Fin C' // Construction.scaleClass (Q b) = (i₁, i₂)}
  let eqv : cls ≃ Fin (Fintype.card cls) := Fintype.equivFin cls
  let ι : Fin (Fintype.card cls) → Fin C' := fun i => (eqv.symm i).1
  have hιinj : Function.Injective ι := by
    intro a b hab
    exact eqv.symm.injective (Subtype.ext hab)
  have hιcls : ∀ i, Construction.scaleClass (Q (ι i)) = (i₁, i₂) := fun i => (eqv.symm i).2
  have hsum : ∑ b ∈ Finset.univ.filter (fun b => Construction.scaleClass (Q b) = (i₁, i₂)), w b =
      ∑ i, w (ι i) := by
    rw [Finset.sum_subtype (Finset.univ.filter (fun b => Construction.scaleClass (Q b) = (i₁, i₂)))
      (p := fun b => Construction.scaleClass (Q b) = (i₁, i₂)) (fun b => by simp)]
    exact (Equiv.sum_comp eqv.symm (fun b : cls => w b.1)).symm
  have hcovc : ENNReal.ofReal κ⁻¹ ≤ (G.card : ℝ≥0∞) * ∑ i, w (ι i) := by
    rw [← hsum]; exact hcov.trans hheavy
  have hCpos : 0 < Fintype.card cls := by
    rcases Nat.eq_zero_or_pos (Fintype.card cls) with h0 | h0
    · exfalso
      have hz : ∑ i : Fin (Fintype.card cls), w (ι i) = 0 := by
        rw [Finset.sum_eq_zero]
        intro i _
        exact absurd i.2 (by omega)
      rw [hz, mul_zero] at hcovc
      exact absurd (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hκpos) hcovc) (lt_irrefl 0)
    · exact h0
  -- the restricted lists
  let lst' : Fin Wk → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin (Fintype.card cls)) :=
    fun γ₀ o => Finset.univ.filter (fun i => ι i ∈ lst γ₀ o)
  have hmem : ∀ γ₀ o i, i ∈ lst' γ₀ o ↔ ι i ∈ lst γ₀ o := by
    intro γ₀ o i; simp [lst']
  have hbounds : ∀ i, (2 : ℝ) ^ i₁ ≤ Construction.r₁ (Q (ι i)) ∧ Construction.r₁ (Q (ι i)) < 2 * (2 : ℝ) ^ i₁ ∧
      (2 : ℝ) ^ i₂ ≤ Construction.r₂ (Q (ι i)) ∧ Construction.r₂ (Q (ι i)) < 2 * (2 : ℝ) ^ i₂ := fun i =>
    Construction.scaleClass_bounds (chart_det (hchart (ι i))) (hιcls i)
  have hGcard : (G.card : ℝ) ≤ (2 * (3 * (M : ℝ) + 1) * Real.logb 2 Nk + 2) ^ 2 := by
    rw [hGdef, Finset.card_product, Nat.cast_mul, ← sq]
    have hb := Construction.magnitudeGrid_card_bound (N := Nk) (a := 3 * (M : ℝ) + 1) hN1 (by positivity)
    have h0 : (0 : ℝ) ≤ ((Construction.magnitudeGrid Nk (3 * (M : ℝ) + 1)).card : ℝ) := Nat.cast_nonneg _
    have hlog : 0 ≤ Real.logb 2 Nk := Real.logb_nonneg (by norm_num) hN1
    gcongr
  refine ⟨{
    κ := κ, κ_one := κ_one, κ_le := κ_le, T := T, s := s, C := Fintype.card cls,
    γ := fun i => γ (ι i), j := fun i => j (ι i), c := fun i => c (ι i), u := fun i => u (ι i),
    Q := fun i => Q (ι i), R := fun i => R (ι i), A := fun i => A (ι i), F := fun i => F (ι i),
    lst := lst', R₁ := (2 : ℝ) ^ i₁, R₂ := (2 : ℝ) ^ i₂, ncls := G.card,
    hs₁ := hs₁, hs₂ := hs₂, hT := hT, hT₁ := hT₁, hT₂ := hT₂,
    hC := ?_, hdisj := ?_, hchart := ?_, hcov := hcovc, hncls := hGcard, hlst := ?_,
    hlstfmt := ?_, r₁lo := fun i => (hbounds i).1, r₁hi := fun i => (hbounds i).2.1,
    r₂lo := fun i => (hbounds i).2.2.1, r₂hi := fun i => (hbounds i).2.2.2,
    R₁pos := by positivity, R₂pos := by positivity,
    R21 := Construction.class_R₂_le_R₁ (chart_det (hchart (ι ⟨0, hCpos⟩))) (hιcls ⟨0, hCpos⟩) }⟩
  · calc ((Fintype.card cls : ℕ) : ℝ) ≤ (C' : ℝ) := by
          exact_mod_cast (Fintype.card_subtype_le _).trans (Fintype.card_fin C').le
      _ ≤ Nk ^ M := hC
  · intro b b' hbb' hγ hj
    exact hdisj (ι b) (ι b') (fun h => hbb' (hιinj h)) hγ hj
  · intro i
    exact chart_of_ex (hchart (ι i)) (fun ⟨hfl, hkn⟩ => ⟨hfl, fun p hp => (hmem _ _ _).mpr (hkn p hp)⟩)
  · intro γ₀ o
    refine le_trans ?_ (hlst γ₀ o)
    exact_mod_cast Finset.card_le_card_of_injOn ι (fun i hi => (hmem _ _ _).mp hi)
      (fun a _ b _ hab => hιinj hab)
  · intro γ₀ i
    have hset : {p : (ℕ × (Fin 6 → ℝ)) × ℝ | i ∈ lst' γ₀ (obs (Bk γ₀) (δ Nk L) p)} =
        {p | ι i ∈ lst γ₀ (obs (Bk γ₀) (δ Nk L) p)} := by
      ext p; exact hmem _ _ _
    have hset' : ∀ i' : ℕ, {r : Fin 7 → ℝ |
        i ∈ lst' γ₀ (obs (Bk γ₀) (δ Nk L) ((i', fun z : Fin 6 => r z.castSucc), r 6))} =
        {r : Fin 7 → ℝ |
          ι i ∈ lst γ₀ (obs (Bk γ₀) (δ Nk L) ((i', fun z : Fin 6 => r z.castSucc), r 6))} := by
      intro i'; ext r; exact hmem _ _ _
    refine ⟨?_, fun i' => ?_⟩
    · rw [hset]; exact (hlstfmt γ₀ (ι i)).1
    · rw [hset' i']; exact (hlstfmt γ₀ (ι i)).2 i'

end Submission.Obl.k4_homogeneous_native_pair_preparation
