-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.SetThinTubes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.SetCountBridges
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.FiniteThin

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

attribute [local instance] Classical.propDecidable

/-- Thin tubes written as a large relation between ambient finite sets. -/
def SetThinTubes (δ σ K c : ℝ) (X Y : Set Plane) : Prop :=
  ∃ R : Set (Plane × Plane), R ⊆ X ×ˢ Y ∧
    (1 - c) * (X.ncard : ℝ) * (Y.ncard : ℝ) ≤ (R.ncard : ℝ) ∧
    ∀ x ∈ X, ∀ u : Plane, ‖u‖ = 1 → ∀ r : ℝ, δ ≤ r →
      ({y | (x, y) ∈ R ∧ |inner ℝ (y - x) u| < r}.ncard : ℝ) ≤
        K * r ^ σ * (Y.ncard : ℝ)

theorem IndexedThinTubes.to_set {S T : Finset Plane} {δ σ K c : ℝ}
    (h : IndexedThinTubes δ σ K c (fun x : S => (x : Plane)) (fun y : T => (y : Plane))) :
    SetThinTubes δ σ K c (↑S : Set Plane) (↑T : Set Plane) := by
  classical
  obtain ⟨P, hbad, hthin⟩ := h.to_finite
  let A := (S ×ˢ T).filter (fun p => P p.1 p.2)
  let B := (S ×ˢ T).filter (fun p => ¬P p.1 p.2)
  have hadd : (A.card : ℝ) + (B.card : ℝ) = (S.card : ℝ) * (T.card : ℝ) := by
    have hc := Finset.card_filter_add_card_filter_not (s := S ×ˢ T) (p := fun p => P p.1 p.2)
    rw [Finset.card_product] at hc
    exact_mod_cast hc
  have hgood : (1 - c) * (S.card : ℝ) * (T.card : ℝ) ≤ (A.card : ℝ) := by
    change (B.card : ℝ) ≤ c * (S.card : ℝ) * (T.card : ℝ) at hbad
    nlinarith
  refine ⟨(↑A : Set (Plane × Plane)), ?_, ?_, ?_⟩
  · intro p hp
    exact Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  · simpa only [Set.ncard_coe_finset] using hgood
  · intro x hx u hu r hr
    have hs : {y : Plane | (x, y) ∈ (↑A : Set (Plane × Plane)) ∧
        |inner ℝ (y - x) u| < r} = ↑(T.filter (fun y => P x y ∧ |inner ℝ (y - x) u| < r)) := by
      ext y
      simp [A, show x ∈ S from hx, and_assoc]
    rw [hs, Set.ncard_coe_finset, Set.ncard_coe_finset]
    exact hthin x hx u r hu hr

theorem SetThinTubes.to_indexed {S T : Finset Plane} {δ σ K c : ℝ}
    (h : SetThinTubes δ σ K c (↑S : Set Plane) (↑T : Set Plane)) :
    IndexedThinTubes δ σ K c (fun x : S => (x : Plane)) (fun y : T => (y : Plane)) := by
  classical
  obtain ⟨R, hR, hgood, hthin⟩ := h
  let P (x : S) (y : T) : Prop := ((x : Plane), (y : Plane)) ∈ R
  have hcard : (Finset.univ.filter (fun p : S × T => P p.1 p.2)).card = R.ncard := by
    rw [indexed_pair_filter_card S T (fun p => p ∈ R)]
    have hs : (↑((S ×ˢ T).filter (fun p => p ∈ R)) : Set (Plane × Plane)) = R := by
      ext p
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, and_iff_right_iff_imp]
      exact fun hp => hR hp
    rw [← Set.ncard_coe_finset, hs]
  have hadd : ((Finset.univ.filter (fun p : S × T => P p.1 p.2)).card : ℝ) +
      ((Finset.univ.filter (fun p : S × T => ¬P p.1 p.2)).card : ℝ) =
        (Fintype.card S : ℝ) * (Fintype.card T : ℝ) := by
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (S × T))) (p := fun p => P p.1 p.2)
    rw [Finset.card_univ, Fintype.card_prod] at hc
    exact_mod_cast hc
  have hgood' : (1 - c) * (Fintype.card S : ℝ) * (Fintype.card T : ℝ) ≤
      ((Finset.univ.filter (fun p : S × T => P p.1 p.2)).card : ℝ) := by
    simpa only [hcard, Fintype.card_coe, Set.ncard_coe_finset] using hgood
  refine ⟨P, by nlinarith [hgood', hadd], ?_⟩
  intro x u r hu hr
  have hc := hthin x x.property u hu r hr
  have heq : (Finset.univ.filter (fun j : T => P x j ∧ |inner ℝ ((j : Plane) - x) u| < r)).card =
      {y ∈ (↑T : Set Plane) | ((x : Plane), y) ∈ R ∧ |inner ℝ (y - x) u| < r}.ncard := by
    convert indexed_filter_card_eq_ncard T
      (fun y => ((x : Plane), y) ∈ R ∧ |inner ℝ (y - x) u| < r) using 1
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, P]
  rw [heq]
  have hs : {y ∈ (↑T : Set Plane) | ((x : Plane), y) ∈ R ∧ |inner ℝ (y - x) u| < r} =
      {y | ((x : Plane), y) ∈ R ∧ |inner ℝ (y - x) u| < r} := by
    ext y
    exact ⟨fun hy => hy.2, fun hy => ⟨(hR hy.1).2, hy⟩⟩
  rw [hs]
  simpa only [Fintype.card_coe, Set.ncard_coe_finset] using hc

theorem setThinTubes_iff_indexed {S T : Finset Plane} {δ σ K c : ℝ} :
    SetThinTubes δ σ K c (↑S : Set Plane) (↑T : Set Plane) ↔
      IndexedThinTubes δ σ K c (fun x : S => (x : Plane)) (fun y : T => (y : Plane)) :=
  ⟨SetThinTubes.to_indexed, IndexedThinTubes.to_set⟩

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
