import Mathlib

-- Adapted from this LOT tree, o063, session x0216, commit bff5370,
-- Submission/Obl/k4_affine_skew_row_fit/Selection.lean.

/-!
# Finite selection of directions and points (paper Lemma 7.7, "two projections")

A weighted bipartite incidence structure between points `P ∈ Pts` and direction bins `d ∈ D`
with weights `m P d`.  From heavy edges, high-degree points and separated triples of incident
directions we select two directions `d₁, d₂` and many third directions `d₃`, each with many
common neighbours.  Everything is stated with explicit constants.
-/

open Finset

namespace Submission.Obl.k4_row_incidence_graph_construction

/-- Real indicator of a decidable proposition. -/
noncomputable def ind (p : Prop) [Decidable p] : ℝ := if p then 1 else 0

theorem ind_nonneg (p : Prop) [Decidable p] : 0 ≤ ind p := by
  unfold ind; split_ifs <;> norm_num

theorem ind_le_one (p : Prop) [Decidable p] : ind p ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem sum_ind_eq_card {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    ∑ i ∈ s, ind (p i) = ((s.filter p).card : ℝ) := by
  unfold ind
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul, mul_one, add_zero]

/-- `[A ∧ B] ≥ [A] - [¬ B]`. -/
theorem ind_and_ge (A B : Prop) [Decidable A] [Decidable B] :
    ind A - ind (¬ B) ≤ ind (A ∧ B) := by
  unfold ind
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

/-- Pigeonhole for sums: some term is at least the average. -/
theorem exists_ge_avg {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ) (hs : s.Nonempty)
    (h : c ≤ ∑ i ∈ s, f i) : ∃ i ∈ s, c / s.card ≤ f i := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ i ∈ s, f i < ∑ _i ∈ s, c / s.card := Finset.sum_lt_sum_of_nonempty hs hcon
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [mul_div_cancel₀ _ hcard.ne'] at hlt
  linarith

/-- If the terms are bounded by `B` and their sum is at least `c`, then the terms at least
`t` contribute at least `c - |s| t`, and there are at least `(c - |s| t) / B` of them. -/
theorem card_large_ge {ι : Type*} (s : Finset ι) (f : ι → ℝ) (t B c : ℝ)
    (hB : 0 < B) (ht : 0 ≤ t) (hfB : ∀ i ∈ s, f i ≤ B) (hc : c ≤ ∑ i ∈ s, f i) :
    (c - s.card * t) / B ≤ ((s.filter (fun i => t ≤ f i)).card : ℝ) := by
  rw [div_le_iff₀ hB]
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => t ≤ f i) f
  have h1 : ∑ i ∈ s.filter (fun i => t ≤ f i), f i ≤
      ((s.filter (fun i => t ≤ f i)).card : ℝ) * B := by
    calc ∑ i ∈ s.filter (fun i => t ≤ f i), f i
        ≤ ∑ _i ∈ s.filter (fun i => t ≤ f i), B :=
          Finset.sum_le_sum (fun i hi => hfB i (Finset.mem_filter.mp hi).1)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ i ∈ s.filter (fun i => ¬ t ≤ f i), f i ≤ (s.card : ℝ) * t := by
    calc ∑ i ∈ s.filter (fun i => ¬ t ≤ f i), f i
        ≤ ∑ _i ∈ s.filter (fun i => ¬ t ≤ f i), t :=
          Finset.sum_le_sum (fun i hi => le_of_lt (not_le.mp (Finset.mem_filter.mp hi).2))
      _ = ((s.filter (fun i => ¬ t ≤ f i)).card : ℝ) * t := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s.card : ℝ) * t := mul_le_mul_of_nonneg_right
              (by exact_mod_cast Finset.card_filter_le _ _) ht
  linarith


theorem ind_and (A B : Prop) [Decidable A] [Decidable B] : ind (A ∧ B) = ind A * ind B := by
  unfold ind
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

/-- Separated triples among the incident directions of one point. -/
theorem triple_lower {D : Finset ℤ} (A : ℤ → Prop) [DecidablePred A]
    (sep : ℤ → ℤ → Prop) [∀ d, DecidablePred (sep d)] {g nρ : ℝ}
    (hsep : ∀ d₀ ∈ D, ((D.filter (fun d => ¬ sep d₀ d)).card : ℝ) ≤ nρ)
    (hn0 : 0 ≤ nρ) (hg : 4 * nρ ≤ g) (hdeg : g ≤ ((D.filter A).card : ℝ)) :
    g ^ 3 / 4 ≤ ∑ d₁ ∈ D, ∑ d₂ ∈ D, ∑ d₃ ∈ D,
      ind (A d₁ ∧ A d₂ ∧ A d₃ ∧ sep d₁ d₂ ∧ sep d₁ d₃ ∧ sep d₂ d₃) := by
  set deg : ℝ := ((D.filter A).card : ℝ) with hdeg_def
  have hdeg_sum : ∑ d ∈ D, ind (A d) = deg := sum_ind_eq_card D A
  -- innermost sum
  have hin : ∀ d₁ ∈ D, ∀ d₂ ∈ D,
      deg - 2 * nρ ≤ ∑ d₃ ∈ D, ind (A d₃ ∧ sep d₁ d₃ ∧ sep d₂ d₃) := by
    intro d₁ hd₁ d₂ hd₂
    have h1 : ∑ d₃ ∈ D, ind (¬ sep d₁ d₃) ≤ nρ := by
      rw [sum_ind_eq_card]; exact hsep d₁ hd₁
    have h2 : ∑ d₃ ∈ D, ind (¬ sep d₂ d₃) ≤ nρ := by
      rw [sum_ind_eq_card]; exact hsep d₂ hd₂
    have hpt : ∀ d₃ ∈ D, ind (A d₃) - ind (¬ sep d₁ d₃) - ind (¬ sep d₂ d₃) ≤
        ind (A d₃ ∧ sep d₁ d₃ ∧ sep d₂ d₃) := by
      intro d₃ _
      unfold ind
      by_cases a : A d₃ <;> by_cases b : sep d₁ d₃ <;> by_cases c : sep d₂ d₃ <;>
        simp [a, b, c]
    have := Finset.sum_le_sum hpt
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hdeg_sum] at this
    linarith
  -- middle sum
  have hmid : ∀ d₁ ∈ D, (deg - nρ) * (deg - 2 * nρ) ≤
      ∑ d₂ ∈ D, ind (A d₂ ∧ sep d₁ d₂) * ∑ d₃ ∈ D, ind (A d₃ ∧ sep d₁ d₃ ∧ sep d₂ d₃) := by
    intro d₁ hd₁
    have h1 : ∑ d₂ ∈ D, ind (¬ sep d₁ d₂) ≤ nρ := by
      rw [sum_ind_eq_card]; exact hsep d₁ hd₁
    have hpos : 0 ≤ deg - 2 * nρ := by linarith
    calc (deg - nρ) * (deg - 2 * nρ)
        ≤ (∑ d₂ ∈ D, ind (A d₂ ∧ sep d₁ d₂)) * (deg - 2 * nρ) := by
          apply mul_le_mul_of_nonneg_right _ hpos
          have hpt : ∀ d₂ ∈ D, ind (A d₂) - ind (¬ sep d₁ d₂) ≤ ind (A d₂ ∧ sep d₁ d₂) :=
            fun d₂ _ => ind_and_ge _ _
          have := Finset.sum_le_sum hpt
          rw [Finset.sum_sub_distrib, hdeg_sum] at this
          linarith
      _ = ∑ d₂ ∈ D, ind (A d₂ ∧ sep d₁ d₂) * (deg - 2 * nρ) := by rw [Finset.sum_mul]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro d₂ hd₂
          exact mul_le_mul_of_nonneg_left (hin d₁ hd₁ d₂ hd₂) (ind_nonneg _)
  -- assemble
  have hexp : ∀ d₁ d₂ d₃ : ℤ,
      ind (A d₁ ∧ A d₂ ∧ A d₃ ∧ sep d₁ d₂ ∧ sep d₁ d₃ ∧ sep d₂ d₃) =
        ind (A d₁) * (ind (A d₂ ∧ sep d₁ d₂) * ind (A d₃ ∧ sep d₁ d₃ ∧ sep d₂ d₃)) := by
    intro d₁ d₂ d₃
    unfold ind
    by_cases a1 : A d₁ <;> by_cases a2 : A d₂ <;> by_cases a3 : A d₃ <;>
      by_cases s12 : sep d₁ d₂ <;> by_cases s13 : sep d₁ d₃ <;> by_cases s23 : sep d₂ d₃ <;>
      simp [a1, a2, a3, s12, s13, s23]
  simp_rw [hexp, ← Finset.mul_sum]
  have hpos2 : 0 ≤ (deg - nρ) * (deg - 2 * nρ) := by
    apply mul_nonneg <;> linarith
  calc g ^ 3 / 4 ≤ deg * ((deg - nρ) * (deg - 2 * nρ)) := by
        have hg0 : 0 ≤ g := by linarith
        have e1 : 3 * deg / 4 ≤ deg - nρ := by linarith
        have e2 : deg / 2 ≤ deg - 2 * nρ := by linarith
        have hd0 : 0 ≤ deg := by linarith
        calc g ^ 3 / 4 ≤ deg * ((3 * deg / 4) * (deg / 2)) := by
              have : g ^ 3 ≤ deg ^ 3 := pow_le_pow_left₀ hg0 hdeg 3
              have e3 : deg * ((3 * deg / 4) * (deg / 2)) = 3 / 8 * deg ^ 3 := by ring
              have : 0 ≤ g ^ 3 := pow_nonneg hg0 3
              linarith
          _ ≤ deg * ((deg - nρ) * (deg - 2 * nρ)) := by
              apply mul_le_mul_of_nonneg_left _ hd0
              apply mul_le_mul e1 e2 (by positivity) (by linarith)
    _ = ∑ d₁ ∈ D, ind (A d₁) * ((deg - nρ) * (deg - 2 * nρ)) := by
        rw [← Finset.sum_mul, hdeg_sum]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro d₁ hd₁
        exact mul_le_mul_of_nonneg_left (hmid d₁ hd₁) (ind_nonneg _)


/-- A row sum is at most `U` times the number of heavy terms plus the light threshold mass. -/
theorem row_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (θ U : ℝ) (hθ : 0 ≤ θ)
    (hfU : ∀ i ∈ s, f i ≤ U) :
    ∑ i ∈ s, f i ≤ U * ((s.filter (fun i => θ ≤ f i)).card : ℝ) + s.card * θ := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => θ ≤ f i) f]
  apply add_le_add
  · calc ∑ i ∈ s.filter (fun i => θ ≤ f i), f i
        ≤ ∑ _i ∈ s.filter (fun i => θ ≤ f i), U :=
          Finset.sum_le_sum (fun i hi => hfU i (Finset.mem_filter.mp hi).1)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · calc ∑ i ∈ s.filter (fun i => ¬ θ ≤ f i), f i
        ≤ ∑ _i ∈ s.filter (fun i => ¬ θ ≤ f i), θ :=
          Finset.sum_le_sum (fun i hi => le_of_lt (not_le.mp (Finset.mem_filter.mp hi).2))
      _ = ((s.filter (fun i => ¬ θ ≤ f i)).card : ℝ) * θ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s.card : ℝ) * θ := mul_le_mul_of_nonneg_right
              (by exact_mod_cast Finset.card_filter_le _ _) hθ

/-- The heavy terms of a nonnegative row carry at least `θ` times their number. -/
theorem heavy_sum_ge {ι : Type*} (s : Finset ι) (f : ι → ℝ) (θ : ℝ) (hf0 : ∀ i, 0 ≤ f i) :
    ((s.filter (fun i => θ ≤ f i)).card : ℝ) * θ ≤ ∑ i ∈ s, f i := by
  calc ((s.filter (fun i => θ ≤ f i)).card : ℝ) * θ
      = ∑ _i ∈ s.filter (fun i => θ ≤ f i), θ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s.filter (fun i => θ ≤ f i), f i :=
        Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i ∈ s, f i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => hf0 i)

/-- Selection of two directions, many third directions and their common neighbours
(heavy edges, high-degree points, separated triples, two pigeonholes). -/
theorem select_directions {Pt : Type*} (Pts : Finset Pt) (D : Finset ℤ) (m : Pt → ℤ → ℝ)
    (sep : ℤ → ℤ → Prop) [∀ d, DecidablePred (sep d)]
    {c U Npts nρ : ℝ}
    (hm0 : ∀ P d, 0 ≤ m P d)
    (hmU : ∀ P ∈ Pts, ∀ d ∈ D, m P d ≤ U)
    (hc : 0 < c) (hU : 0 < U)
    (htot : c ≤ ∑ P ∈ Pts, ∑ d ∈ D, m P d)
    (hNpts : (Pts.card : ℝ) ≤ Npts)
    (hsep : ∀ d₀ ∈ D, ((D.filter (fun d => ¬ sep d₀ d)).card : ℝ) ≤ nρ)
    (hn0 : 0 ≤ nρ)
    (hnρ : 4 * nρ ≤ c / (4 * U * Npts)) :
    ∃ d₁ ∈ D, ∃ d₂ ∈ D, sep d₁ d₂ ∧ ∃ D₃ ⊆ D,
      (∀ d₃ ∈ D₃, sep d₁ d₃ ∧ sep d₂ d₃) ∧
      (c / (4 * U * Npts)) ^ 3 / (8 * (D.card : ℝ) ^ 2) ≤ (D₃.card : ℝ) ∧
      ∀ d₃ ∈ D₃, c * (c / (4 * U * Npts)) ^ 3 / (32 * U * (D.card : ℝ) ^ 4) ≤
        ((Pts.filter (fun P => c / (2 * Npts * D.card) ≤ m P d₁ ∧
            c / (2 * Npts * D.card) ≤ m P d₂ ∧ c / (2 * Npts * D.card) ≤ m P d₃ ∧
            (c / (4 * U * Npts)) * (c / (2 * Npts * D.card)) ≤ ∑ d ∈ D, m P d)).card : ℝ) := by
  classical
  -- nonemptiness
  have hPtsne : Pts.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at htot
    linarith
  have hDne : D.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp only [hne, Finset.sum_empty, Finset.sum_const_zero] at htot
    linarith
  have hMpos : (0 : ℝ) < D.card := by exact_mod_cast hDne.card_pos
  have hNpos : 0 < Npts := lt_of_lt_of_le (by exact_mod_cast hPtsne.card_pos) hNpts
  set M : ℝ := (D.card : ℝ) with hM
  set θ : ℝ := c / (2 * Npts * M) with hθ
  set g : ℝ := c / (4 * U * Npts) with hg
  have hθ0 : 0 ≤ θ := by positivity
  have hg0 : 0 ≤ g := by positivity
  let A : Pt → ℤ → Prop := fun P d => θ ≤ m P d
  let deg : Pt → ℝ := fun P => ((D.filter (A P)).card : ℝ)
  have hdegM : ∀ P, deg P ≤ M := fun P => by
    simp only [deg, hM]; exact_mod_cast Finset.card_filter_le _ _
  -- heavy edges
  have hheavy : c / (2 * U) ≤ ∑ P ∈ Pts, deg P := by
    have hrow : ∀ P ∈ Pts, ∑ d ∈ D, m P d ≤ U * deg P + M * θ := fun P hP =>
      row_sum_le D (m P) θ U hθ0 (hmU P hP)
    have h1 : ∑ P ∈ Pts, ∑ d ∈ D, m P d ≤ U * ∑ P ∈ Pts, deg P + (Pts.card : ℝ) * (M * θ) := by
      calc ∑ P ∈ Pts, ∑ d ∈ D, m P d ≤ ∑ P ∈ Pts, (U * deg P + M * θ) := Finset.sum_le_sum hrow
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have h2 : (Pts.card : ℝ) * (M * θ) ≤ c / 2 := by
      calc (Pts.card : ℝ) * (M * θ) ≤ Npts * (M * θ) :=
            mul_le_mul_of_nonneg_right hNpts (by positivity)
        _ = c / 2 := by rw [hθ]; field_simp
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- high degree points
  let HD : Finset Pt := Pts.filter (fun P => g ≤ deg P)
  have hHDsum : c / (4 * U) ≤ ∑ P ∈ HD, deg P := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Pts (fun P => g ≤ deg P) deg
    have hlow : ∑ P ∈ Pts.filter (fun P => ¬ g ≤ deg P), deg P ≤ Npts * g := by
      calc ∑ P ∈ Pts.filter (fun P => ¬ g ≤ deg P), deg P
          ≤ ∑ _P ∈ Pts.filter (fun P => ¬ g ≤ deg P), g :=
            Finset.sum_le_sum (fun P hP => le_of_lt (not_le.mp (Finset.mem_filter.mp hP).2))
        _ = ((Pts.filter (fun P => ¬ g ≤ deg P)).card : ℝ) * g := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Npts * g := mul_le_mul_of_nonneg_right
            ((by exact_mod_cast Finset.card_filter_le _ _ : ((Pts.filter (fun P => ¬ g ≤ deg P)).card : ℝ) ≤ Pts.card).trans hNpts) hg0
    have hNg : Npts * g = c / (4 * U) := by rw [hg]; field_simp
    have : c / (2 * U) = c / (4 * U) + c / (4 * U) := by field_simp; ring
    linarith
  have hHDcard : c / (4 * U * M) ≤ (HD.card : ℝ) := by
    have : ∑ P ∈ HD, deg P ≤ (HD.card : ℝ) * M := by
      calc ∑ P ∈ HD, deg P ≤ ∑ _P ∈ HD, M := Finset.sum_le_sum (fun P _ => hdegM P)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [div_le_iff₀ (by positivity)]
    have h4 : c / (4 * U) * M ≤ (HD.card : ℝ) * M * M := by
      have := mul_le_mul_of_nonneg_right (hHDsum.trans this) hMpos.le
      linarith
    calc c = c / (4 * U) * (4 * U) := by field_simp
      _ ≤ (HD.card : ℝ) * M * (4 * U) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact hHDsum.trans this
      _ = _ := by ring
  have hHDpos : (0 : ℝ) < HD.card := lt_of_lt_of_le (by positivity) hHDcard
  -- separated triples
  let good : Pt → ℤ → ℤ → ℤ → Prop := fun P d₁ d₂ d₃ =>
    A P d₁ ∧ A P d₂ ∧ A P d₃ ∧ sep d₁ d₂ ∧ sep d₁ d₃ ∧ sep d₂ d₃
  have htrip : ∀ P ∈ HD, g ^ 3 / 4 ≤ ∑ d₁ ∈ D, ∑ d₂ ∈ D, ∑ d₃ ∈ D, ind (good P d₁ d₂ d₃) := by
    intro P hP
    exact triple_lower (A P) sep hsep hn0 hnρ (Finset.mem_filter.mp hP).2
  have htot4 : (HD.card : ℝ) * (g ^ 3 / 4) ≤
      ∑ x ∈ D ×ˢ D, ∑ d₃ ∈ D, ∑ P ∈ HD, ind (good P x.1 x.2 d₃) := by
    calc (HD.card : ℝ) * (g ^ 3 / 4) = ∑ _P ∈ HD, g ^ 3 / 4 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ P ∈ HD, ∑ d₁ ∈ D, ∑ d₂ ∈ D, ∑ d₃ ∈ D, ind (good P d₁ d₂ d₃) :=
          Finset.sum_le_sum htrip
      _ = ∑ d₁ ∈ D, ∑ d₂ ∈ D, ∑ d₃ ∈ D, ∑ P ∈ HD, ind (good P d₁ d₂ d₃) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro d₁ _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro d₂ _
          rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_product]
  have hDDne : (D ×ˢ D).Nonempty := hDne.product hDne
  obtain ⟨⟨d₁, d₂⟩, hx, hxbig⟩ := exists_ge_avg (D ×ˢ D) _ _ hDDne htot4
  rw [Finset.card_product] at hxbig
  obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
  simp only at hx1 hx2 hxbig
  let n : ℤ → ℝ := fun d₃ => ∑ P ∈ HD, ind (good P d₁ d₂ d₃)
  have hn_le : ∀ d₃, n d₃ ≤ HD.card := by
    intro d₃
    calc n d₃ ≤ ∑ _P ∈ HD, (1 : ℝ) := Finset.sum_le_sum (fun P _ => ind_le_one _)
      _ = HD.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hn_card : ∀ d₃, n d₃ = ((HD.filter (fun P => good P d₁ d₂ d₃)).card : ℝ) :=
    fun d₃ => sum_ind_eq_card _ _
  have hn_pos_good : ∀ d₃, 0 < n d₃ → ∃ P ∈ HD, good P d₁ d₂ d₃ := by
    intro d₃ hpos
    rw [hn_card] at hpos
    have : (HD.filter (fun P => good P d₁ d₂ d₃)).Nonempty := by
      rw [← Finset.card_pos]; exact_mod_cast hpos
    obtain ⟨P, hP⟩ := this
    exact ⟨P, (Finset.mem_filter.mp hP).1, (Finset.mem_filter.mp hP).2⟩
  have hsum_n : (HD.card : ℝ) * g ^ 3 / (4 * M ^ 2) ≤ ∑ d₃ ∈ D, n d₃ := by
    have : (HD.card : ℝ) * (g ^ 3 / 4) / ((D.card * D.card : ℕ) : ℝ) =
        (HD.card : ℝ) * g ^ 3 / (4 * M ^ 2) := by
      rw [hM]; push_cast; ring
    rw [← this]; exact hxbig
  set t : ℝ := (HD.card : ℝ) * g ^ 3 / (8 * M ^ 3) with ht
  let D₃ := D.filter (fun d₃ => t ≤ n d₃)
  have hD₃card : g ^ 3 / (8 * M ^ 2) ≤ (D₃.card : ℝ) := by
    have := card_large_ge D n t (HD.card : ℝ) ((HD.card : ℝ) * g ^ 3 / (4 * M ^ 2)) hHDpos
      (by positivity) (fun d₃ _ => hn_le d₃) hsum_n
    have e : ((HD.card : ℝ) * g ^ 3 / (4 * M ^ 2) - (D.card : ℝ) * t) / (HD.card : ℝ) =
        g ^ 3 / (8 * M ^ 2) := by
      rw [ht, ← hM]; field_simp; ring
    rw [e] at this
    exact this
  refine ⟨d₁, hx1, d₂, hx2, ?_, D₃, Finset.filter_subset _ _, ?_, hD₃card, ?_⟩
  · -- some third direction carries mass, so `d₁, d₂` are separated
    have hpos : 0 < ∑ d₃ ∈ D, n d₃ := lt_of_lt_of_le (by positivity) hsum_n
    obtain ⟨d₃, hd₃⟩ : ∃ d₃, 0 < n d₃ := by
      by_contra hall
      push_neg at hall
      have : ∑ d₃ ∈ D, n d₃ ≤ 0 := Finset.sum_nonpos (fun d₃ _ => hall d₃)
      linarith
    obtain ⟨P, _, hP⟩ := hn_pos_good d₃ hd₃
    exact hP.2.2.2.1
  · intro d₃ hd₃
    have ht0 : 0 < t := by positivity
    have : 0 < n d₃ := lt_of_lt_of_le ht0 (Finset.mem_filter.mp hd₃).2
    obtain ⟨P, _, hP⟩ := hn_pos_good d₃ this
    exact ⟨hP.2.2.2.2.1, hP.2.2.2.2.2⟩
  · intro d₃ hd₃
    have hnt : t ≤ n d₃ := (Finset.mem_filter.mp hd₃).2
    have hsub : HD.filter (fun P => good P d₁ d₂ d₃) ⊆
        Pts.filter (fun P => θ ≤ m P d₁ ∧ θ ≤ m P d₂ ∧ θ ≤ m P d₃ ∧
          g * θ ≤ ∑ d ∈ D, m P d) := by
      intro P hP
      obtain ⟨hPHD, hgood⟩ := Finset.mem_filter.mp hP
      obtain ⟨hPPts, hPdeg⟩ := Finset.mem_filter.mp hPHD
      refine Finset.mem_filter.mpr ⟨hPPts, hgood.1, hgood.2.1, hgood.2.2.1, ?_⟩
      calc g * θ ≤ deg P * θ := mul_le_mul_of_nonneg_right hPdeg hθ0
        _ ≤ ∑ d ∈ D, m P d := heavy_sum_ge D (m P) θ (hm0 P)
    have hcard_le := Finset.card_le_card hsub
    calc c * g ^ 3 / (32 * U * M ^ 4) = (c / (4 * U * M)) * g ^ 3 / (8 * M ^ 3) := by
          field_simp; ring
      _ ≤ (HD.card : ℝ) * g ^ 3 / (8 * M ^ 3) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hHDcard (by positivity)
      _ = t := rfl
      _ ≤ n d₃ := hnt
      _ = _ := hn_card d₃
      _ ≤ _ := by exact_mod_cast hcard_le

end Submission.Obl.k4_row_incidence_graph_construction
