import Submission.Obl.k4_marked_scalar_grid_selection.CountableBands
import Submission.Obl.k4_marked_scalar_grid_selection.TrimmedTables
import Submission.Obl.k4_marked_scalar_grid_selection.RecordWeights
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.CanonicalTransport

namespace Submission.Obl.k4_marked_scalar_grid_selection

open MeasureTheory Set Filter Scalar
open scoped ENNReal

/-- Whole-cell selection, given exact measurable density choices for all the
finite subtables. The choices need no regularity in their depth parameters. -/
theorem selection_of_exact_densities
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Subpower N K) (s m V : ℝ) (hs : 0 < s) (hsm : s < m) (hV : 0 < V)
    (M : ℕ) (H J : ℕ → ℕ)
    (b : (k : ℕ) → Fin (H k) → Fin 5 → ℝ)
    (w : (k : ℕ) → Fin (H k) → ℝ)
    (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool)
    (htables : ∀ k, tables (N k) (K k) m M (H k) (J k) (b k) (w k) (mark k))
    (g : (k : ℕ) → Finset (AtomIndex (H k) (J k)) → ℝ → ObsSpace → ℝ≥0∞)
    (G : (k : ℕ) → Finset (AtomIndex (H k) (J k)) → ℝ → ℝ → JointSpace → ℝ≥0∞)
    (hg : ∀ k T r, 0 ≤ r → r ≤ s → Measurable (g k T r) ∧
      (law (N k ^ (-m)) (H k) (J k) (b k) (w k) (markOf T)).map (obs (N k) r) =
        reference.withDensity (g k T r))
    (hG : ∀ k T r u, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ V →
      Measurable (G k T r u) ∧
        (law (N k ^ (-m)) (H k) (J k) (b k) (w k) (markOf T)).map (aug (N k) r u) =
          jointReference.withDensity (G k T r u)) :
    ∃ L : ℕ → ℝ, Subpower N L ∧ (∀ k, K k ≤ L k) ∧
      ∃ mark' : (k : ℕ) → Fin (H k) → Fin (J k) → Bool,
        (∀ k, tables (N k) (L k) m M (H k) (J k) (b k) (w k) (mark' k)) ∧
        (∀ k j z, mark' k j z = true → mark k j z = true) ∧
        gridData N s V (fun k => law (N k ^ (-m)) (H k) (J k) (b k) (w k) (mark' k)) := by
  classical
  have hm : 0 ≤ m := by linarith
  have hn1 (k : ℕ) : 1 ≤ N k := by linarith [hN k]
  have hn0 (k : ℕ) : 0 < N k := by linarith [hN k]
  have hj (k : ℕ) : 0 < J k := by have := (htables k).1; omega
  have hw (k : ℕ) : ∀ j, 0 ≤ w k j := (htables k).2.2.2.2.2.1
  have hw1 (k : ℕ) : ∑ j, w k j = 1 := (htables k).2.2.2.2.2.2.1
  have hb (k : ℕ) : ∀ j e, |b k j e| ≤ K k := (htables k).2.2.2.2.2.2.2.1
  have hclamp (B : ℝ) (hB : 0 ≤ B) (q : ℚ) : 0 ≤ clamp B q ∧ clamp B q ≤ B :=
    k4_tempered_grid_selection.clamp_mem hB q
  have hc0 : clamp V (0 : ℚ) = 0 := by
    simp only [clamp, Rat.cast_zero, min_eq_right hV.le, max_self]
  let σ (k : ℕ) := N k ^ (-m)
  let aWidth (k : ℕ) (q : ℚ) := N k ^ (-clamp s q)
  let ρ (k : ℕ) (v : ℚ) := N k ^ (-clamp V v)
  have hσ (k : ℕ) : 0 < σ k := Real.rpow_pos_of_pos (hn0 k) _
  have hσ₁ (k : ℕ) : σ k ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (hn1 k) (by linarith)
  have haWidth (k : ℕ) (q : ℚ) : σ k ≤ aWidth k q :=
    Real.rpow_le_rpow_of_exponent_le (hn1 k) (by linarith [(hclamp s hs.le q).2])
  obtain ⟨I, hI, hIlower, hcut⟩ := trimmed_tables N K hN hNt hK m M H J b w mark htables
  let T (k : ℕ) (A : Set (AtomIndex (H k) (J k))) := (I k).filter (fun a => a ∈ A)
  let μ (k : ℕ) := tableMeasure (I k) (cellWeight (J k) (w k))
  let ν (k : ℕ) (A : Set (AtomIndex (H k) (J k))) :=
    law (σ k) (H k) (J k) (b k) (w k) (markOf (T k A))
  let code (k : ℕ) (i : ℚ × ℚ) (a : AtomIndex (H k) (J k)) :=
    atomRecord (σ k) (aWidth k i.1) (max (σ k) (ρ k i.2)) (b k) a.1 a.2
  let W (k : ℕ) (i : ℚ × ℚ) (a : AtomIndex (H k) (J k)) :=
    realNodeMass (I k) (σ k) (ρ k i.2) (w k) (code k i) (code k i a)
  have hWpure (k : ℕ) (q : ℚ) (a : AtomIndex (H k) (J k)) :
      W k (q, 0) a = realNodeMass (I k) (σ k) 1 (w k)
        (fun a => atomRecord (σ k) (aWidth k q) 1 (b k) a.1 a.2)
        (atomRecord (σ k) (aWidth k q) 1 (b k) a.1 a.2) := by
    simp only [W, code, ρ, hc0, neg_zero, Real.rpow_zero, max_eq_right (hσ₁ k)]
  obtain ⟨C, hC⟩ := exists_nat_ge (max (2 * (M : ℝ) + 2 + V) ((M : ℝ) + m))
  have hW : ∀ i, ∀ᶠ k in atTop, ∀ z ∈ (I k : Set _),
      N k ^ (-(C : ℝ)) ≤ W k i z ∧ W k i z ≤ N k ^ (C : ℝ) := by
    intro i
    filter_upwards [hcut] with k hk z hz
    have hbound := realNodeMass_power_bounds (I k) (w k) (hw k) (hw1 k) (code k i)
      (hn1 k) hm (hclamp V hV.le i.2).1 (hclamp V hV.le i.2).2
      (htables k).1 (htables k).2.2.1 z hz (hk z hz)
    constructor
    · exact (Real.rpow_le_rpow_of_exponent_le (hn1 k)
        (by linarith [le_max_left (2 * (M : ℝ) + 2 + V) ((M : ℝ) + m)])).trans hbound.1
    · exact hbound.2.trans (Real.rpow_le_rpow_of_exponent_le (hn1 k)
        ((le_max_right _ _).trans hC))
  let F := ℚ ⊕ (ℚ × ℚ)
  let Y : F → Type := fun j => match j with
    | .inl _ => ObsSpace
    | .inr _ => JointSpace
  let col : F → ℚ × ℚ := fun j => match j with
    | .inl q => (q, 0)
    | .inr i => i
  let Q : (j : F) → ℕ → Incidence → Y j := fun j => match j with
    | .inl q => fun k => obs (N k) (clamp s q)
    | .inr i => fun k => aug (N k) (clamp s i.1) (clamp V i.2)
  let D : (j : F) → (k : ℕ) → Set (AtomIndex (H k) (J k)) → Y j → ℝ≥0∞ :=
    fun j => match j with
    | .inl q => fun k A => g k (T k A) (clamp s q)
    | .inr i => fun k A => G k (T k A) (clamp s i.1) (clamp V i.2)
  have hband : ∀ j, ∀ᶠ k in atTop, ∀ A : Set (AtomIndex (H k) (J k)),
      A ⊆ (I k : Set _) → ∀ l u ε : ℝ, 0 < l → 0 < u → 0 < ε →
      (∀ z ∈ A, l ≤ W k (col j) z ∧ W k (col j) z ≤ u) →
      ν k A {p | D j k A (Q j k p) < ENNReal.ofReal (ε * l) ∨
        ENNReal.ofReal (geometryLoss (K k) * u) < D j k A (Q j k p)} ≤
        ENNReal.ofReal (ε * geometryLoss (K k)) := by
    intro j
    apply Eventually.of_forall
    intro k A hAI l u ε hl hu hε hfit
    cases j with
    | inl q =>
      exact selected_pure_real_band (hj k) (hσ k) (hσ₁ k)
        (htables k).2.2.2.1 (haWidth k q) (hK.1 k) (b k) (hb k) (w k) (hw k) (hw1 k)
        (I k) (T k A) (Finset.filter_subset _ _) hε.le (by
          intro z hz
          simpa only [col, hWpure] using hfit z (Finset.mem_filter.mp hz).2)
        (g k (T k A) (clamp s q))
        (hg k (T k A) _ (hclamp s hs.le q).1 (hclamp s hs.le q).2).1
        (hg k (T k A) _ (hclamp s hs.le q).1 (hclamp s hs.le q).2).2
    | inr i =>
      exact selected_aug_real_band (hj k) (hσ k) (htables k).2.2.2.1
        (haWidth k i.1) (Real.rpow_pos_of_pos (hn0 k) _) (hK.1 k)
        (b k) (hb k) (w k) (hw k) (hw1 k) (I k) (T k A) (Finset.filter_subset _ _) hε.le
        (fun z hz => hfit z (Finset.mem_filter.mp hz).2)
        (G k (T k A) (clamp s i.1) (clamp V i.2))
        (hG k (T k A) _ _ (hclamp s hs.le i.1).1 (hclamp s hs.le i.1).2
          (hclamp V hV.le i.2).1 (hclamp V hV.le i.2).2).1
        (hG k (T k A) _ _ (hclamp s hs.le i.1).1 (hclamp s hs.le i.1).2
          (hclamp V hV.le i.2).1 (hclamp V hV.le i.2).2).2
  have hbase : k4_tempered_grid_selection.Subpower N (fun k => 2 * K k) :=
    k4_tempered_grid_selection.subpower_mul (fun k => hn0 k)
      (subpower_constant hNt (show (1 : ℝ) ≤ 2 by norm_num)) hK
  have hμlower (k : ℕ) : ENNReal.ofReal (2 * K k)⁻¹ ≤ μ k (I k : Set _) := by
    rw [tableMeasure_finset (I k) (I k) Subset.rfl _ (fun a _ =>
      div_nonneg (hw k a.1) (Nat.cast_nonneg _))]
    exact hIlower k
  obtain ⟨L, A, a, hL, hLK, hAI, hAlower, ha, htyp⟩ :=
    countable_record_selection Y col N (fun k => 2 * K k) hN hNt hbase μ
      (fun k => (I k : Set _)) hμlower ν Q D W C hW
      (fun _ k => geometryLoss (K k)) (fun _ => geometryLoss_subpower hN hNt hK) hband
  have hKL (k : ℕ) : K k ≤ L k := by linarith [hLK k, hK.1 k]
  have hmass (k : ℕ) : ENNReal.ofReal (L k)⁻¹ ≤ ν k (A k) univ := by
    rw [law_mass_markOf (hσ k) (hj k) (b k) (w k) (hw k)]
    have h := hAlower k
    rw [tableMeasure_restrict_mass (I k) _ _ (Set.to_countable (A k)).measurableSet
      (fun a _ => div_nonneg (hw k a.1) (Nat.cast_nonneg _))] at h
    exact h
  refine ⟨L, hL, hKL, (fun k => markOf (T k (A k))), ?_, ?_, ?_⟩
  · intro k
    rcases htables k with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, (fun j e => (h8 j e).trans (hKL k)), hmass k⟩
  · intro k
    exact markOf_mono ((Finset.filter_subset _ _).trans (hI k))
  · refine ⟨C, (fun k q v => a k (q, v)),
      (fun k r => g k (T k (A k)) r), (fun k r u => G k (T k (A k)) r u),
      (fun k q v => ha k (q, v)), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro k r hr hrs
      exact hg k _ r hr hrs
    · intro k r u hr hrs hu huV
      exact hG k _ r u hr hrs hu huV
    · intro q τ hτ
      exact htyp (Sum.inl q) τ hτ
    · intro q v τ hτ
      exact htyp (Sum.inr (q, v)) τ hτ

end Submission.Obl.k4_marked_scalar_grid_selection
