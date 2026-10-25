-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse

open MeasureTheory Set Metric
open scoped ENNReal

abbrev Space := EuclideanSpace ℝ (Fin 3)

def tube (δ : ℝ) (x v : Space) : Set Space :=
  thickening δ (segment ℝ x (x + v))

def dilatedTube (ρ : ℝ) (z w : Space) : Set Space :=
  thickening (10 * ρ) (segment ℝ (z - (9 / 2 : ℝ) • w) (z + (11 / 2 : ℝ) • w))

def Family (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1) ∧
    (∀ i, tube δ (x i) (v i) ⊆ ball 0 1) ∧
    (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ℝ≥0∞) * volume (tube δ (x i) (v i))) ∧
    (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ tube δ (x i) (v i)) ∧
    ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i)

def Separated (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ r : ℝ, δ ≤ r → r ≤ 1 → ∃ ρ : ℝ,
    r ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-η) * r ∧
    ∃ k : ℕ, 0 < k ∧ ∃ z w : Fin k → Space,
      (∀ j, ‖w j‖ = 1) ∧
      (∀ j j', j ≠ j' → volume (tube ρ (z j) (w j) ∩ tube ρ (z j') (w j')) ≤
        (1 / 2 : ℝ≥0∞) * volume (tube ρ (z j) (w j))) ∧
      (∀ i, ∃! j, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)) ∧
      (∀ j, ∃ i, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)) ∧
      (∀ j j', ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ) ≤
        δ ^ (-η) * ({i | tube δ (x i) (v i) ⊆ tube ρ (z j') (w j')}.ncard : ℝ)) ∧
      (∀ j, ∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ∧
          tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η) *
          ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ)) * volume W) ∧
      (∀ i j j', tube δ (x i) (v i) ⊆ dilatedTube ρ (z j) (w j) →
        tube δ (x i) (v i) ⊆ dilatedTube ρ (z j') (w j') → j = j')

def Examples (s : ℝ) : Prop :=
  ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
    0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y ∧ Separated η δ n x v ∧
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ s)

def Covering (d α C : ℝ) (B : Set ℝ) : Prop :=
  ∀ r R a : ℝ, d ≤ r → r ≤ R → ∃ (m : ℕ) (c : Fin m → ℝ),
    B ∩ Icc a (a + R) ⊆ (⋃ j, closedBall (c j) r) ∧ (m : ℝ) ≤ C * (R / r) ^ α

def projectedSlice (f : ℝ → ℝ) (E : Set Space) (z : ℝ) : Set ℝ :=
  {u | (u, z) ∈ (fun p : Space => (p 0 + f (p 2) * p 1, p 2)) '' E}

def Grains (σ : ℝ) : Prop :=
  ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
    0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y ∧ Separated η δ n x v ∧ (∀ i, IsCompact (Y i)) ∧
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) ∧
      ∃ (f : ℝ → ℝ) (P : Space → Space),
        LipschitzWith 1 f ∧
        (∀ z : ℝ, z ∈ Icc (-1) 1 → Covering δ (1 - σ) (δ ^ (-η))
          (projectedSlice f (⋃ i, Y i) z)) ∧
        LipschitzWith 1 P ∧ (∀ p, p ∈ (⋃ i, Y i) → ‖P p‖ = 1) ∧
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (P p)| ≤ δ) ∧
        (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ (⋃ i, Y i) →
          Covering ρ (1 - σ) (δ ^ (-η))
            ((fun q : Space => inner ℝ (P p) q) '' ((⋃ i, Y i) ∩ ball p (Real.sqrt ρ))))

theorem Family.union_subset_ball {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : Family η δ n x v Y) :
    (⋃ i, Y i) ⊆ ball 0 1 :=
  iUnion_subset fun i => (h.2.2.2.2.2.1 i).trans (h.2.2.1 i)

theorem Family.volume_union_ne_top {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : Family η δ n x v Y) : volume (⋃ i, Y i) ≠ ∞ :=
  ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono h.union_subset_ball)

theorem Family.mono_error {η ε δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : Family η δ n x v Y)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηε : η ≤ ε) : Family ε δ n x v Y := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_⟩
  apply le_trans (ENNReal.ofReal_le_ofReal _) h.2.2.2.2.2.2
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηε)
      (Nat.cast_nonneg _)) (sq_nonneg _)

theorem Separated.mono_error {η ε δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : Separated η δ n x v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηε : η ≤ ε) :
    Separated ε δ n x v := by
  have hp : δ ^ (-η) ≤ δ ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηε)
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, hw, hd, hc, ho, hb, hf, hs⟩ := h r hδr hr1
  refine ⟨ρ, hrρ, hρ1, hρr.trans ?_, k, hk, z, w, hw, hd, hc, ho, ?_, ?_, hs⟩
  · exact mul_le_mul_of_nonneg_right hp (hδ.le.trans hδr)
  · intro j j'
    exact (hb j j').trans (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))
  · intro j W hW
    apply (hf j W hW).trans
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))) le_rfl

theorem Examples.mono {s t : ℝ} (h : Examples s) (hts : t ≤ s) : Examples t := by
  intro η d0 hη hd0
  obtain ⟨δ, hδ, hδ0, hδmax, n, x, v, Y, hH, hS, hV⟩ := h η d0 hη hd0
  refine ⟨δ, hδ, hδ0, hδmax, n, x, v, Y, hH, hS, hV.trans ?_⟩
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) hts)

/-- Failure of arbitrarily small examples is a uniform strict volume lower bound. -/
theorem not_examples_iff (s : ℝ) : ¬Examples s ↔
    ∃ η d0 : ℝ, 0 < η ∧ 0 < d0 ∧ ∀ δ : ℝ,
      0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Family η δ n x v Y → Separated η δ n x v →
          ENNReal.ofReal (δ ^ s) < volume (⋃ i, Y i) := by
  classical
  constructor
  · intro h
    have hex : ∃ η d0 : ℝ, 0 < η ∧ 0 < d0 ∧
        ¬∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
          ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
            Family η δ n x v Y ∧ Separated η δ n x v ∧
              volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ s) := by
      by_contra hn
      apply h
      intro η d0 hη hd0
      by_contra he
      exact hn ⟨η, d0, hη, hd0, he⟩
    obtain ⟨η, d0, hη, hd0, hn⟩ := hex
    refine ⟨η, d0, hη, hd0, ?_⟩
    intro δ hδ hδ0 hδmax n x v Y hH hS
    apply lt_of_not_ge
    intro hV
    exact hn ⟨δ, hδ, hδ0, hδmax, n, x, v, Y, hH, hS, hV⟩
  · rintro ⟨η, d0, hη, hd0, hn⟩ h
    obtain ⟨δ, hδ, hδ0, hδmax, n, x, v, Y, hH, hS, hV⟩ := h η d0 hη hd0
    exact (hn δ hδ hδ0 hδmax n x v Y hH hS).not_ge hV

theorem Covering.mono {d α C : ℝ} {A B : Set ℝ} (h : Covering d α C B)
    (hAB : A ⊆ B) : Covering d α C A := by
  intro r R a hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h r R a hdr hrR
  exact ⟨m, c, (inter_subset_inter_left _ hAB).trans hc, hm⟩

theorem projectedSlice_mono {f : ℝ → ℝ} {E F : Set Space} (hEF : E ⊆ F) (z : ℝ) :
    projectedSlice f E z ⊆ projectedSlice f F z := by
  intro u hu
  exact image_mono hEF hu

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse
