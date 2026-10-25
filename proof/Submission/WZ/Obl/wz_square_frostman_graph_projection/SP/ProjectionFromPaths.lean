-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ProjectionFromPaths.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GraphPathCounting
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ThreeSumWindow
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoverCounting

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Many paths between every retained pair transfer a small restricted
projection cover to a small full Cartesian projection cover. -/
theorem projection_cover_of_many_paths (A B : Finset ℝ) (R : A → B → Prop)
    (X : Finset A) (Y : Finset B) {δ c t p₀ : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hct : c ≤ t) (ht1 : t ≤ 1)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y)
    (hpaths : ∀ x ∈ X, ∀ b ∈ Y, p₀ * (A.card : ℝ) * (B.card : ℝ) ≤
      ((graphThreePaths R x b).card : ℝ))
    {m : ℕ} (cc : Fin m → ℝ)
    (hcover : Covers δ ((fun q : A × B => (q.1 : ℝ) + t * (q.2 : ℝ)) ''
      (↑(Finset.univ.filter (fun q : A × B => R q.1 q.2)) : Set (A × B))) cc) :
    ∃ (n : ℕ) (centers : Fin n → ℝ), Covers δ
      (↑((X ×ˢ Y).image (fun q : A × B => (q.1 : ℝ) + t * (q.2 : ℝ))) : Set ℝ) centers ∧
      c * p₀ * (A.card : ℝ) * (B.card : ℝ) * (n : ℝ) ≤ 288 * (m : ℝ) ^ 3 := by
  classical
  let S := (X ×ˢ Y).image (fun q : A × B => (q.1 : ℝ) + t * (q.2 : ℝ))
  obtain ⟨n, centers, hcS, hcsep, hScov⟩ := exists_separated_cover S.finite_toSet.totallyBounded hδ
  let V := Finset.univ.image centers
  have hVS : V ⊆ S := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact hcS i
  have hVsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → δ ≤ dist x y := by
    intro x hx y hy hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact (hcsep i j (fun hij => hne (hij ▸ rfl))).le
  have hcinj : Function.Injective centers := by
    intro i j hij
    by_contra hne
    have hh := hcsep i j hne
    rw [hij, dist_self] at hh
    linarith
  have hVc : V.card = n := by
    rw [Finset.card_image_iff.mpr (fun i _ j _ hij => hcinj hij)]
    simp
  have hchoice (v : V) : ∃ x ∈ X, ∃ b ∈ Y, (x : ℝ) + t * (b : ℝ) = (v : ℝ) := by
    obtain ⟨q, hq, hval⟩ := Finset.mem_image.mp (hVS v.2)
    exact ⟨q.1, (Finset.mem_product.mp hq).1, q.2, (Finset.mem_product.mp hq).2, hval⟩
  choose a ha b hb hrep using hchoice
  let P := Finset.univ.filter (fun q : V × A × B =>
    R (a q.1) q.2.2 ∧ R q.2.1 q.2.2 ∧ R q.2.1 (b q.1))
  have hPcard : (n : ℝ) * (p₀ * (A.card : ℝ) * (B.card : ℝ)) ≤ (P.card : ℝ) := by
    have hident : (P.card : ℝ) = ∑ v : V, ((graphThreePaths R (a v) (b v)).card : ℝ) := by
      simpa only [P, graphThreePaths, Finset.card_eq_sum_ones, Finset.sum_filter,
        Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
        product_filter_card_eq_sum (fun (v : V) (q : A × B) => R (a v) q.2 ∧ R q.1 q.2 ∧ R q.1 (b v))
    rw [hident]
    calc
      (n : ℝ) * (p₀ * (A.card : ℝ) * (B.card : ℝ)) =
          ∑ _v : V, p₀ * (A.card : ℝ) * (B.card : ℝ) := by simp [hVc]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hpaths (a v) (ha v) (b v) (hb v))
  let f (q : V × A × B) : ℝ × ℝ × ℝ :=
    ((a q.1 : ℝ) + t * (q.2.2 : ℝ), (q.2.1 : ℝ) + t * (q.2.2 : ℝ),
      (q.2.1 : ℝ) + t * (b q.1 : ℝ))
  let cc₃ (j : Fin (m * (m * m))) : ℝ × ℝ × ℝ :=
    (cc (finProdFinEquiv.symm j).1,
      cc (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1,
      cc (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2)
  have hcov : Covers δ (f '' (↑P : Set (V × A × B))) cc₃ := by
    apply (hcover.prod (hcover.prod hcover)).mono_set
    rintro z ⟨q, hq, rfl⟩
    have hr := (Finset.mem_filter.mp hq).2
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨(a q.1, q.2.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.1⟩, rfl⟩
    · exact ⟨(q.2.1, q.2.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.2.1⟩, rfl⟩
    · exact ⟨(q.2.1, b q.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.2.2⟩, rfl⟩
  have hbound (j : Fin (m * (m * m))) :
      ((P.filter (fun q => dist (f q) (cc₃ j) ≤ δ)).card : ℝ) ≤ 288 / c := by
    let W := Finset.univ.filter (fun q : V × A × B =>
      dist ((a q.1 : ℝ) + t * (q.2.2 : ℝ)) (cc₃ j).1 ≤ δ ∧
      dist ((q.2.1 : ℝ) + t * (q.2.2 : ℝ)) (cc₃ j).2.1 ≤ δ ∧
      dist ((q.2.1 : ℝ) + t * (b q.1 : ℝ)) (cc₃ j).2.2 ≤ δ)
    have hsub : P.filter (fun q => dist (f q) (cc₃ j) ≤ δ) ⊆ W := by
      intro q hq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [f, Prod.dist_eq, max_le_iff] using (Finset.mem_filter.mp hq).2
    have hw := three_sum_window_card V A B (fun v => (a v : ℝ)) (fun v => (b v : ℝ))
      hδ hc hct ht1 hVsep hAsep hBsep hrep
      (z₁ := (cc₃ j).1) (z₂ := (cc₃ j).2.1) (z₃ := (cc₃ j).2.2)
    have hw' : (W.card : ℝ) ≤ 288 / c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hw)
    exact (show ((P.filter (fun q => dist (f q) (cc₃ j) ≤ δ)).card : ℝ) ≤ (W.card : ℝ) by
      exact_mod_cast Finset.card_le_card hsub).trans hw'
  have hcount := WangZahlLot.Obl.wz_separated_projection_dichotomy.card_le_cover_mul_fiber_bound P f hcov hbound
  have hscaled := mul_le_mul_of_nonneg_left hcount hc.le
  have hid : c * (((m * (m * m) : ℕ) : ℝ) * (288 / c)) = 288 * (m : ℝ) ^ 3 := by
    push_cast
    field_simp <;> ring
  rw [hid] at hscaled
  refine ⟨n, centers, hScov, ?_⟩
  have hh := (mul_le_mul_of_nonneg_left hPcard hc.le).trans hscaled
  convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
