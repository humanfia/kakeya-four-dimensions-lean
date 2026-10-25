-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.UnionReduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.DenseContacts
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.MeasureSampling
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.UnionArithmetic
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.CoefficientCount

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open MeasureTheory Set
open scoped ENNReal

/-- The exact restricted rich set reduces to unions formed from small
subfamilies, with a fixed enlargement of the slope threshold. -/
theorem restricted_area_le_of_sample_unions {n : ℕ} (A B : Finset (Fin n))
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {δ κ D μ V : ℝ}
    (hκ : 0 < κ) (hD : 0 < D) (hμ : 0 < μ)
    (hcross : ∀ i ∈ A, ∀ j ∈ B,
      D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2 * D)
    (hbound : ∀ (F G : Finset (Fin n)), F ⊆ A → G ⊆ B →
      F.card ≤ ⌈(A.card : ℝ) / (μ / 2)⌉₊ →
      G.card ≤ ⌈(B.card : ℝ) / (μ / 2)⌉₊ →
      volume (⋃ i ∈ F, ⋃ j ∈ G,
        narrowIntersection δ (9 * κ) (q i) (q j) (g i) (g j)) ≤ ENNReal.ofReal V) :
    volume {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
      ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p ∧
      transverseMultiplicity A B δ κ q g p < ENNReal.ofReal (μ ^ 2 / 100)} ≤
      ENNReal.ofReal (4 * V) := by
  classical
  let E := {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
      ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p ∧
      transverseMultiplicity A B δ κ q g p < ENNReal.ofReal (μ ^ 2 / 100)}
  change volume E ≤ _
  rcases E.eq_empty_or_nonempty with hE | hE
  · rw [hE, measure_empty]
    exact zero_le
  obtain ⟨p₀, hp₀⟩ := hE
  obtain ⟨F₀, G₀, hF₀A, hG₀B, hF₀, hG₀, _⟩ :=
    exists_dense_narrow_biclique A B hκ hD hμ hcross hp₀.1 hp₀.2.1 hp₀.2.2
  have hFA : 0 < A.card := by
    have : 0 < (F₀.card : ℝ) := (by linarith : 0 < μ / 2).trans_le hF₀
    exact (Nat.cast_pos.mp this).trans_le (Finset.card_le_card hF₀A)
  have hGB : 0 < B.card := by
    have : 0 < (G₀.card : ℝ) := (by linarith : 0 < μ / 2).trans_le hG₀
    exact (Nat.cast_pos.mp this).trans_le (Finset.card_le_card hG₀B)
  let : Nonempty {i : Fin n // i ∈ A} :=
    ⟨⟨(Finset.card_pos.mp hFA).choose, (Finset.card_pos.mp hFA).choose_spec⟩⟩
  let : Nonempty {j : Fin n // j ∈ B} :=
    ⟨⟨(Finset.card_pos.mp hGB).choose, (Finset.card_pos.mp hGB).choose_spec⟩⟩
  let R (i : {i : Fin n // i ∈ A}) (j : {j : Fin n // j ∈ B}) :=
    narrowIntersection δ (9 * κ) (q i) (q j) (g i) (g j)
  apply measure_rich_le_of_ceil_sample_unions volume R
    (fun i j => measurableSet_narrowIntersection (hg i) (hg j)) E
    (by linarith : 0 < μ / 2) V
  · intro p hp
    obtain ⟨F, G, hFA, hGB, hF, hG, hFG⟩ :=
      exists_dense_narrow_biclique A B hκ hD hμ hcross hp.1 hp.2.1 hp.2.2
    have hFc : (F.subtype (· ∈ A)).card = F.card := by
      rw [Finset.card_subtype, Finset.filter_eq_self.mpr (fun i hi => hFA hi)]
    have hGc : (G.subtype (· ∈ B)).card = G.card := by
      rw [Finset.card_subtype, Finset.filter_eq_self.mpr (fun i hi => hGB hi)]
    refine ⟨F.subtype (· ∈ A), G.subtype (· ∈ B), ?_, ?_, ?_⟩
    · simpa only [hFc] using hF
    · simpa only [hGc] using hG
    · intro i hi j hj
      exact hFG i (Finset.mem_subtype.mp hi) j (Finset.mem_subtype.mp hj)
  · intro F G hF hG
    let F' := F.map (Function.Embedding.subtype (· ∈ A))
    let G' := G.map (Function.Embedding.subtype (· ∈ B))
    have hFA : F' ⊆ A := fun _ hi => Finset.property_of_mem_map_subtype F hi
    have hGB : G' ⊆ B := fun _ hj => Finset.property_of_mem_map_subtype G hj
    have hb := hbound F' G' hFA hGB
      (by simpa only [F', Finset.card_map, Fintype.card_coe] using hF)
      (by simpa only [G', Finset.card_map, Fintype.card_coe] using hG)
    convert hb using 1
    congr 1
    ext p
    simp [F', G', R]

/-- A hereditary one-rich union-area estimate suffices for the restricted
rich-area estimate. The geometric union bound is an explicit hypothesis:
this theorem only supplies the sampling and coefficient-mass reduction. -/
theorem restricted_area_of_narrow_union {n : ℕ} (A B : Finset (Fin n))
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {δ κ D μ K C τ : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) (hD : 0 < D) (hμ : 0 < μ)
    (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hcross : ∀ i ∈ A, ∀ j ∈ B,
      D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2 * D)
    (hpack : δ * ((A.card : ℝ) + B.card) ≤ 2 * K * D)
    (hslope : κ ≤ μ ^ (-(1 / 2 : ℝ)))
    (hunion : ∀ (F G : Finset (Fin n)), F ⊆ A → G ⊆ B →
      volume (⋃ i ∈ F, ⋃ j ∈ G,
        narrowIntersection δ (9 * κ) (q i) (q j) (g i) (g j)) ≤
        ENNReal.ofReal (C * δ ^ (-τ) * δ *
          (Real.sqrt (δ / D) * ((F.card : ℝ) + G.card) *
              Real.sqrt ((F.card : ℝ) + G.card) + 9 * κ * ((F.card : ℝ) + G.card)))) :
    volume {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
      ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p ∧
      transverseMultiplicity A B δ κ q g p < ENNReal.ofReal (μ ^ 2 / 100)} ≤
      ENNReal.ofReal (576 * C * δ ^ (-τ) * K * δ *
        ((A.card : ℝ) + B.card) * μ ^ (-(3 / 2 : ℝ))) := by
  classical
  let E := {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
      ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p ∧
      transverseMultiplicity A B δ κ q g p < ENNReal.ofReal (μ ^ 2 / 100)}
  change volume E ≤ _
  rcases E.eq_empty_or_nonempty with hE | hE
  · rw [hE, measure_empty]
    exact zero_le
  obtain ⟨p₀, hp₀⟩ := hE
  obtain ⟨F₀, G₀, hF₀A, hG₀B, hF₀, hG₀, _⟩ :=
    exists_dense_narrow_biclique A B hκ hD hμ hcross hp₀.1 hp₀.2.1 hp₀.2.2
  have hμA : μ / 2 ≤ (A.card : ℝ) := hF₀.trans (Nat.cast_le.mpr
    (Finset.card_le_card hF₀A))
  have hμB : μ / 2 ≤ (B.card : ℝ) := hG₀.trans (Nat.cast_le.mpr
    (Finset.card_le_card hG₀B))
  have hceil (m : ℕ) (hm : μ / 2 ≤ (m : ℝ)) :
      (⌈(m : ℝ) / (μ / 2)⌉₊ : ℝ) ≤ 4 * m / μ := by
    have hh := (Nat.ceil_lt_add_one
      (div_nonneg (Nat.cast_nonneg m) (by linarith : 0 ≤ μ / 2))).le
    have h1 := (one_le_div (by linarith : 0 < μ / 2)).mpr hm
    calc
      _ ≤ 2 * ((m : ℝ) / (μ / 2)) := by linarith
      _ = _ := by ring
  let V := 144 * C * δ ^ (-τ) * K * δ *
    ((A.card : ℝ) + B.card) * μ ^ (-(3 / 2 : ℝ))
  have hv : volume E ≤ ENNReal.ofReal (4 * V) := by
    apply restricted_area_le_of_sample_unions A B hg hκ hD hμ hcross
    intro F G hFA hGB hF hG
    have hsample : (F.card : ℝ) + G.card ≤ 4 * ((A.card : ℝ) + B.card) / μ := by
      calc
        _ ≤ 4 * A.card / μ + 4 * B.card / μ :=
          add_le_add ((Nat.cast_le.mpr hF).trans (hceil A.card hμA))
            ((Nat.cast_le.mpr hG).trans (hceil B.card hμB))
        _ = _ := by ring
    have hn := sampled_narrow_union_expression_le hδ hD hK
      (by positivity : 0 ≤ (A.card : ℝ) + B.card) hμ
      (by positivity : 0 ≤ (F.card : ℝ) + G.card) hpack hsample hslope
    have hroot : 0 ≤ Real.sqrt (δ / D) * ((F.card : ℝ) + G.card) *
        Real.sqrt ((F.card : ℝ) + G.card) := by positivity
    have hn' : Real.sqrt (δ / D) * ((F.card : ℝ) + G.card) *
          Real.sqrt ((F.card : ℝ) + G.card) + 9 * κ * ((F.card : ℝ) + G.card) ≤
        144 * K * ((A.card : ℝ) + B.card) * μ ^ (-(3 / 2 : ℝ)) := by
      nlinarith only [hn, hroot]
    apply (hunion F G hFA hGB).trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ (C * δ ^ (-τ) * δ) *
          (144 * K * ((A.card : ℝ) + B.card) * μ ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hn' (by positivity)
      _ = V := by dsimp [V]; ring
  convert hv using 1
  congr 1
  dsimp [V]
  ring

/-- Specialize the sampling reduction to the slope threshold and coefficient
count of the frozen obligation. The one-rich union estimate is still a premise. -/
theorem restricted_area_of_frozen_union_bound {n : ℕ} (A B : Finset (Fin n))
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) {δ D μ K C τ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδD : δ ≤ D)
    (hμ : 0 < μ) (hK : 1 ≤ K) (hC : 0 ≤ C) (hτ : 0 ≤ τ)
    (hdiamA : ∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D / 100)
    (hdiamB : ∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ D / 100)
    (hcross : ∀ i ∈ A, ∀ j ∈ B,
      D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2 * D)
    (hcount : ∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ D →
      (Set.ncard {i : Fin n | i ∈ A ∪ B ∧ q i ∈ Metric.ball q0 r} : ℝ) ≤
        K * (r / δ))
    (hunion : ∀ (F G : Finset (Fin n)), F ⊆ A → G ⊆ B →
      volume (⋃ i ∈ F, ⋃ j ∈ G,
        narrowIntersection δ (9 * (δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ))))
          (q i) (q j) (g i) (g j)) ≤
        ENNReal.ofReal (C * δ ^ (-τ) * δ *
          (Real.sqrt (δ / D) * ((F.card : ℝ) + G.card) *
              Real.sqrt ((F.card : ℝ) + G.card) +
            9 * (δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ))) * ((F.card : ℝ) + G.card)))) :
    volume {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
      ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p ∧
      transverseMultiplicity A B δ (δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ))) q g p <
        ENNReal.ofReal (μ ^ 2 / 100)} ≤
      ENNReal.ofReal (576 * C * δ ^ (-τ) * K ^ (1 : ℝ) * δ *
        ((A.card : ℝ) + B.card) * μ ^ (-(3 / 2 : ℝ))) := by
  have hD : 0 < D := hδ.trans_le hδD
  have hN := total_card_le_of_bipartite_count A B hδ hδD (by linarith : 0 ≤ K)
    hdiamA hdiamB hcount
  have hpack : δ * ((A.card : ℝ) + B.card) ≤ 2 * K * D := by
    have h := mul_le_mul_of_nonneg_left hN hδ.le
    calc
      _ ≤ δ * (2 * K * (D / δ)) := h
      _ = _ := by field_simp
  have hslope : δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ)) ≤ μ ^ (-(1 / 2 : ℝ)) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (Real.rpow_le_one hδ.le hδ1 (by positivity : 0 ≤ 4 * τ))
      (by positivity : 0 ≤ μ ^ (-(1 / 2 : ℝ)))
  simpa only [Real.rpow_one] using restricted_area_of_narrow_union A B hg hδ
    (by positivity : 0 < δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ))) hD hμ hK hC hcross
    hpack hslope hunion

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
