import Mathlib

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# Covering numbers for the planar input

Covers by finitely many closed balls, in the `Fin m`-indexed form used by
`WangZahlLot.wz_ad_projection_dichotomy`:

* `CoveredBy S ρ m`: `S` lies in the union of `m` closed `ρ`-balls;
* `coveredBy_of_finset`: a finite set of centres gives such a cover;
* `card_le_of_coveredBy`: lower bound for covers of a set containing many points, at most
  `B` of which lie in any closed `ρ`-ball;
* `graph_coveredBy`: the part of the graph `{(u, ψ u) : u ∈ T}` of a function with
  `|ψ u - ψ u'| ≤ K (|u - u'| + s₀)` inside a ball of radius `r` is covered by
  `(4K+5)(4r/ρ+1)` closed `ρ`-balls, for `s₀ ≤ ρ ≤ r` (the planar regularity condition).
-/

open Metric

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

/-- The Euclidean plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- `S` lies in the union of `m` closed balls of radius `ρ`. -/
def CoveredBy {X : Type*} [PseudoMetricSpace X] (S : Set X) (ρ : ℝ) (m : ℕ) : Prop :=
  ∃ cc : Fin m → X, S ⊆ ⋃ j, closedBall (cc j) ρ

theorem coveredBy_of_finset {X : Type*} [PseudoMetricSpace X] {S : Set X} {ρ : ℝ}
    (C : Finset X) (h : S ⊆ ⋃ c ∈ C, closedBall c ρ) : CoveredBy S ρ C.card := by
  classical
  refine ⟨fun j => (C.equivFin.symm j : X), ?_⟩
  intro x hx
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (h hx)
  exact Set.mem_iUnion.2 ⟨C.equivFin ⟨c, hc⟩, by simpa using hxc⟩

theorem CoveredBy.mono {X : Type*} [PseudoMetricSpace X] {S S' : Set X} {ρ : ℝ} {m : ℕ}
    (h : CoveredBy S ρ m) (hS : S' ⊆ S) : CoveredBy S' ρ m := by
  obtain ⟨cc, hcc⟩ := h
  exact ⟨cc, hS.trans hcc⟩

open Classical in
/-- If `P ⊆ S` is finite and every closed `ρ`-ball contains at most `B` points of `P`,
then every cover of `S` by `m` closed `ρ`-balls has `card P ≤ m * B`. -/
theorem card_le_of_coveredBy {X : Type*} [PseudoMetricSpace X] {S : Set X} {ρ : ℝ} {m B : ℕ}
    (P : Finset X) (hPS : ∀ x ∈ P, x ∈ S)
    (hB : ∀ c : X, (P.filter (fun x => x ∈ closedBall c ρ)).card ≤ B)
    (cc : Fin m → X) (hcov : S ⊆ ⋃ j, closedBall (cc j) ρ) : P.card ≤ m * B := by
  classical
  have hsub : P ⊆ Finset.univ.biUnion (fun j : Fin m => P.filter (fun x => x ∈ closedBall (cc j) ρ)) := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov (hPS x hx))
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_filter.2 ⟨hx, hj⟩⟩
  calc P.card ≤ (Finset.univ.biUnion (fun j : Fin m => P.filter (fun x => x ∈ closedBall (cc j) ρ))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j : Fin m, (P.filter (fun x => x ∈ closedBall (cc j) ρ)).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin m, B := Finset.sum_le_sum (fun j _ => hB (cc j))
    _ = m * B := by simp

theorem dist_E2 (x y : E2) : dist x y = Real.sqrt ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
  rw [EuclideanSpace.dist_eq]; simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem abs_sub_le_dist_E2_zero (x y : E2) : |x 0 - y 0| ≤ dist x y := by
  rw [dist_E2]
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (x 1 - y 1)])

theorem abs_sub_le_dist_E2_one (x y : E2) : |x 1 - y 1| ≤ dist x y := by
  rw [dist_E2]
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (x 0 - y 0)])

theorem dist_E2_le_of {x y : E2} {a b ρ : ℝ} (ha : |x 0 - y 0| ≤ a) (hb : |x 1 - y 1| ≤ b)
    (h : a ^ 2 + b ^ 2 ≤ ρ ^ 2) (hρ : 0 ≤ ρ) : dist x y ≤ ρ := by
  rw [dist_E2]
  have h1 : (x 0 - y 0) ^ 2 ≤ a ^ 2 := by
    have := abs_nonneg (x 0 - y 0); rw [← sq_abs]; exact pow_le_pow_left₀ this ha 2
  have h2 : (x 1 - y 1) ^ 2 ≤ b ^ 2 := by
    have := abs_nonneg (x 1 - y 1); rw [← sq_abs]; exact pow_le_pow_left₀ this hb 2
  rw [Real.sqrt_le_left hρ]
  linarith

/-- The point `(u, w)` of the plane. -/
def pt (u w : ℝ) : E2 := !₂[u, w]

@[simp] theorem pt_zero (u w : ℝ) : pt u w 0 = u := by simp [pt]
@[simp] theorem pt_one (u w : ℝ) : pt u w 1 = w := by simp [pt]

/-- Regularity of a slack-Lipschitz graph: inside a ball of radius `r` it is covered by
`(4K+5)(4r/ρ+1)` closed `ρ`-balls once `s₀ ≤ ρ ≤ r`. -/
theorem graph_coveredBy {T : Set ℝ} {ψ : ℝ → ℝ} {K s₀ : ℝ} (hK : 0 ≤ K)
    (hψ : ∀ u ∈ T, ∀ u' ∈ T, |ψ u - ψ u'| ≤ K * (|u - u'| + s₀))
    {ρ r : ℝ} (hρ : 0 < ρ) (hs₀ : s₀ ≤ ρ) (hρr : ρ ≤ r) (x : E2) :
    ∃ m : ℕ, CoveredBy ({a : E2 | ∃ u ∈ T, a = pt u (ψ u)} ∩ ball x r) ρ m ∧
      (m : ℝ) ≤ (4 * K + 5) * (4 * r / ρ + 1) := by
  classical
  -- time cells of length ρ/2 starting at x 0 - r
  set h : ℝ := ρ / 2 with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  set M : ℕ := ⌈4 * r / ρ⌉₊ with hM
  set J : ℕ := ⌈2 * K⌉₊ + 1 with hJ
  let cell : ℝ → ℕ := fun u => ⌊(u - (x 0 - r)) / h⌋₊
  -- a chosen time of `T` in each occupied cell
  let rep : ℕ → ℝ := fun i => if hi : ∃ u ∈ T, cell u = i ∧ x 0 - r < u then hi.choose else 0
  let center : ℕ × ℤ → E2 := fun ij =>
    pt (x 0 - r + ((ij.1 : ℝ) + 1 / 2) * h) (ψ (rep ij.1) + (ij.2 : ℝ) * ρ)
  let C : Finset E2 := ((Finset.range M) ×ˢ (Finset.Icc (-(J : ℤ)) J)).image center
  refine ⟨C.card, coveredBy_of_finset C ?_, ?_⟩
  · rintro a ⟨⟨u, huT, rfl⟩, hball⟩
    have hdist : dist (pt u (ψ u)) x < r := hball
    have hu0 : |u - x 0| < r := by
      have := abs_sub_le_dist_E2_zero (pt u (ψ u)) x
      simp only [pt_zero] at this; linarith
    have hlo : x 0 - r < u := by linarith [(abs_lt.1 hu0).1]
    have hhi : u < x 0 + r := by linarith [(abs_lt.1 hu0).2]
    set i := cell u with hi
    have hpos : 0 ≤ (u - (x 0 - r)) / h := div_nonneg (by linarith) hh0.le
    have hfl := Nat.floor_le hpos
    have hfl2 := Nat.lt_floor_add_one ((u - (x 0 - r)) / h)
    have hiM : i < M := by
      have : (u - (x 0 - r)) / h < 4 * r / ρ := by
        rw [div_lt_div_iff₀ hh0 hρ, hh]; nlinarith
      have h2 : ((i : ℕ) : ℝ) < (M : ℝ) := by
        calc ((i : ℕ) : ℝ) ≤ (u - (x 0 - r)) / h := hfl
          _ < 4 * r / ρ := this
          _ ≤ (M : ℝ) := Nat.le_ceil _
      exact_mod_cast h2
    have hex : ∃ u' ∈ T, cell u' = i ∧ x 0 - r < u' := ⟨u, huT, rfl, hlo⟩
    have hrep : rep i = hex.choose := by simp only [rep]; exact dif_pos hex
    obtain ⟨hrT, hrcell, hrlo⟩ := hex.choose_spec
    set v := hex.choose with hv
    -- both `u` and `v` lie in time cell `i`
    have hvpos : 0 ≤ (v - (x 0 - r)) / h := div_nonneg (by linarith) hh0.le
    have hvfl := Nat.floor_le hvpos
    have hvfl2 := Nat.lt_floor_add_one ((v - (x 0 - r)) / h)
    have hcv : (cell v : ℝ) = (i : ℝ) := by rw [hrcell]
    have huv : |u - v| ≤ h := by
      have e1 : (i : ℝ) * h ≤ u - (x 0 - r) := by
        have := hfl; rw [le_div_iff₀ hh0] at this; exact this
      have e2 : u - (x 0 - r) < ((i : ℝ) + 1) * h := by
        have := hfl2; rw [div_lt_iff₀ hh0] at this; exact this
      have e3 : (i : ℝ) * h ≤ v - (x 0 - r) := by
        have := hvfl; rw [le_div_iff₀ hh0] at this; simp only [cell] at hcv; rw [hcv] at this; exact this
      have e4 : v - (x 0 - r) < ((i : ℝ) + 1) * h := by
        have := hvfl2; rw [div_lt_iff₀ hh0] at this; simp only [cell] at hcv; rw [hcv] at this; exact this
      rw [abs_le]; constructor <;> nlinarith
    have hψuv : |ψ u - ψ v| ≤ K * (h + ρ) := by
      calc |ψ u - ψ v| ≤ K * (|u - v| + s₀) := hψ u huT v hrT
        _ ≤ K * (h + ρ) := by apply mul_le_mul_of_nonneg_left _ hK; linarith
    -- vertical index
    set jr : ℤ := round ((ψ u - ψ v) / ρ) with hjr
    have hjr_err : |(ψ u - ψ v) / ρ - (jr : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have hjr_bound : |(jr : ℝ)| ≤ J := by
      have hq : |(ψ u - ψ v) / ρ| ≤ 3 / 2 * K := by
        rw [abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
        calc |ψ u - ψ v| ≤ K * (h + ρ) := hψuv
          _ = 3 / 2 * K * ρ := by rw [hh]; ring
      have hJ' : (2 * K : ℝ) + 1 ≤ (J : ℝ) := by
        simp only [hJ]; push_cast; linarith [Nat.le_ceil (2 * K)]
      have := abs_sub_abs_le_abs_sub ((jr : ℝ)) ((ψ u - ψ v) / ρ)
      rw [abs_sub_comm] at hjr_err
      linarith [abs_nonneg ((ψ u - ψ v) / ρ)]
    have hjmem : jr ∈ Finset.Icc (-(J : ℤ)) J := by
      rw [Finset.mem_Icc]
      have := abs_le.1 hjr_bound
      constructor <;> [exact_mod_cast (by linarith [this.1] : (-(J : ℝ)) ≤ jr);
        exact_mod_cast this.2]
    refine Set.mem_iUnion₂.2 ⟨center (i, jr), Finset.mem_image.2
      ⟨(i, jr), Finset.mem_product.2 ⟨Finset.mem_range.2 hiM, hjmem⟩, rfl⟩, ?_⟩
    rw [mem_closedBall]
    apply dist_E2_le_of (a := h / 2) (b := ρ / 2) _ _ _ hρ.le
    · simp only [center, pt_zero]
      have e1 : (i : ℝ) * h ≤ u - (x 0 - r) := by
        have := hfl; rw [le_div_iff₀ hh0] at this; exact this
      have e2 : u - (x 0 - r) < ((i : ℝ) + 1) * h := by
        have := hfl2; rw [div_lt_iff₀ hh0] at this; exact this
      rw [abs_le]; constructor <;> nlinarith
    · simp only [center, pt_one]
      rw [hrep]
      have : ψ u - (ψ v + (jr : ℝ) * ρ) = ρ * ((ψ u - ψ v) / ρ - jr) := by
        field_simp; ring
      rw [this, abs_mul, abs_of_pos hρ]
      nlinarith
    · rw [hh]; nlinarith
  · -- counting the centres
    have hC : (C.card : ℝ) ≤ (M : ℝ) * (2 * J + 1) := by
      have h1 : C.card ≤ ((Finset.range M) ×ˢ (Finset.Icc (-(J : ℤ)) J)).card := Finset.card_image_le
      rw [Finset.card_product, Finset.card_range, Int.card_Icc] at h1
      have h2 : ((J : ℤ) + 1 - -(J : ℤ)).toNat = 2 * J + 1 := by omega
      rw [h2] at h1
      exact_mod_cast h1
    have hM' : (M : ℝ) ≤ 4 * r / ρ + 1 := (Nat.ceil_lt_add_one (by
      apply div_nonneg <;> linarith)).le
    have hJ' : (2 * (J : ℝ) + 1) ≤ 4 * K + 5 := by
      have : (J : ℝ) ≤ 2 * K + 2 := by
        simp only [hJ]; push_cast
        linarith [Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * K by linarith)]
      linarith
    calc (C.card : ℝ) ≤ (M : ℝ) * (2 * J + 1) := hC
      _ ≤ (4 * r / ρ + 1) * (4 * K + 5) := by
        have hr0 : 0 ≤ 4 * r / ρ + 1 := by
          have : 0 ≤ 4 * r / ρ := by apply div_nonneg <;> linarith
          linarith
        exact mul_le_mul hM' hJ' (by positivity) hr0
      _ = (4 * K + 5) * (4 * r / ρ + 1) := by ring

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
