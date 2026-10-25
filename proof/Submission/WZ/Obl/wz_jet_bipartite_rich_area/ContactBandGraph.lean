-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactBandGraph.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactChoices
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGridCrowding
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactPairCount

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set MeasureTheory
open scoped Classical
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- A slope-band strip union produces a finite simple contact graph, retaining
the actual contact times and the quantitative nearby-neighbor bounds. -/
theorem exists_band_contact_graph {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (A B : Finset (Fin n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (i₀ : Fin n) (T : Finset ℤ) {δ lower s ℓ w D l u : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) (hℓ : 0 < ℓ) (hD : 0 < D)
    (href : ∀ i ∈ A, dist (q i) (q i₀) ≤ 2 * D)
    (hcross : ∀ i ∈ A, ∀ j ∈ B, dist (q i) (q j) ≤ 2 * D)
    (hinterval : Icc l u ⊆ Icc (-1 : ℝ) 1)
    (hT : ∀ k ∈ T, w + k * ℓ ∈ Icc (-1 : ℝ) 1)
    (hcover : ∀ x ∈ Icc l u, ∃ k ∈ T, |x - (w + k * ℓ)| ≤ ℓ)
    (hlin : s * ℓ ≤ δ) (hstep : D * ℓ ≤ s) (hmesh : δ ≤ 2 * s * ℓ)
    (hnat : δ * D ≤ s ^ 2) (hband : lower = s / 2 ∨ s ^ 2 ≤ δ * D)
    (hcurv : ∀ i ∈ A, ∀ j ∈ B, ∀ x ∈ Icc l u,
      D / 120 ≤ |deriv (deriv (g i)) x - deriv (deriv (g j)) x|)
    (E : Set (ℝ × ℝ))
    (hE : ∀ p ∈ E, p.2 ∈ Icc l u ∧ ∃ i ∈ A, ∃ j ∈ B,
      |p.1 - g i p.2| ≤ δ ∧ |p.1 - g j p.2| ≤ δ ∧
      lower ≤ |deriv (g i) p.2 - deriv (g j) p.2| ∧
      |deriv (g i) p.2 - deriv (g j) p.2| ≤ s) :
    ∃ (R : {i : Fin n // i ∈ A} → {j : Fin n // j ∈ B} → Prop)
      (t : {i : Fin n // i ∈ A} → {j : Fin n // j ∈ B} → ℝ),
      (∀ a b, R a b → t a b ∈ Icc l u ∧ NearContact (2 * δ) s (g a) (g b) (t a b)) ∧
      (∀ a b, R a b → Fintype.card {b' // R a b' ∧
        |t a b - t a b'| ≤ 10000 * s / D} ≤ contactCrowding δ D s) ∧
      (∀ a b, R a b → Fintype.card {a' // R a' b ∧
        |t a b - t a' b| ≤ 10000 * s / D} ≤ contactCrowding δ D s) ∧
      volume E ≤ ENNReal.ofReal (18000000000 * δ * ℓ *
        ∑ a, (Fintype.card {b // R a b} : ℝ)) := by
  classical
  obtain ⟨S, hS, _, harea⟩ := exists_contactCell_cover hg hjet A B i₀ T hδ hs hℓ hD.le
    href hcross hinterval hT hcover hlin hstep E hE
  obtain ⟨red, blue, tag, htag⟩ := choose_contactCell_witnesses A B hA hB g (g i₀) S
    (fun t ht => (hS t ht).2)
  let gA (a : {i : Fin n // i ∈ A}) := g a
  let gB (b : {j : Fin n // j ∈ B}) := g b
  have hcurv' (a : {i : Fin n // i ∈ A}) (b : {j : Fin n // j ∈ B})
      (x : ℝ) (hx : x ∈ Icc l u) :
      D / 120 ≤ |deriv (deriv (gA a - gB b)) x| := by
    rw [deriv2_sub_of_contDiff_two (hg a) (hg b)]
    exact hcurv a a.2 b b.2 x hx
  have hcellA : ∀ t ∈ S, JetCell (gA (red t)) (g i₀) δ s ℓ w 42 t :=
    fun t ht => (htag t ht).2.2.2.2.1
  have hcellB : ∀ t ∈ S, JetCell (gB (blue t)) (g i₀) δ s ℓ w 42 t :=
    fun t ht => (htag t ht).2.2.2.2.2
  have hnear : ∀ t ∈ S, |tag t - (w + t.1 * ℓ)| ≤ ℓ :=
    fun t ht => (htag t ht).2.1
  have htags : ∀ t ∈ S, tag t ∈ Icc l u ∧
      NearContact (2 * δ) s (gA (red t)) (gB (blue t)) (tag t) :=
    fun t ht => ⟨(htag t ht).1, (htag t ht).2.2.1⟩
  have hfiber : ∀ a b, (S.filter (fun t => red t = a ∧ blue t = b)).card ≤ 30000000 := by
    intro a b
    rcases hband with hb | hb
    · have htags' : ∀ t ∈ S, tag t ∈ Icc l u ∧
          NearContact (2 * δ) s (gA (red t)) (gB (blue t)) (tag t) ∧
          s / 2 ≤ |deriv (gA (red t)) (tag t) - deriv (gB (blue t)) (tag t)| := by
        intro t ht
        exact ⟨(htags t ht).1, (htags t ht).2, hb ▸ (htag t ht).2.2.2.1⟩
      convert cell_pair_count_transverse S red blue tag gA gB (g i₀)
          (fun a => hg a) (fun b => hg b) hδ hs hℓ (by positivity : 0 < D / 120)
          hmesh hcurv' hcellA hnear htags' a b using 1
      congr 1
      ext t
      simp
    · convert cell_pair_count_natural S red blue tag gA gB (g i₀)
          (fun a => hg a) (fun b => hg b) hδ hs hℓ hD hmesh hb hcurv' hcellA hnear htags a b using 1
      congr 1
      ext t
      simp
  let R := cellRelation S red blue
  let time (a : {i : Fin n // i ∈ A}) (b : {j : Fin n // j ∈ B}) :=
    tag (cellRepresentative S red blue a b)
  have hresolution := (contactCrowding_bounds hδ hD hs hℓ.le hnat hmesh hlin).2.1
  refine ⟨R, time, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hr := cellRepresentative_spec S red blue hab
    have ht := htags (cellRepresentative S red blue a b) hr.1
    rw [hr.2.1, hr.2.2] at ht
    exact ht
  · intro a b hab
    exact card_cell_red_neighbors_of_jetCells S red blue tag gA (g i₀) hδ hs hℓ 42
      (contactCrowdingSteps δ D s) hcellA hnear hresolution hab
  · intro a b hab
    exact card_cell_blue_neighbors_of_jetCells S red blue tag gB (g i₀) hδ hs hℓ 42
      (contactCrowdingSteps δ D s) hcellB hnear hresolution hab
  · have hc := card_cells_le_mul_incidence S red blue 30000000 (fun a b => by
      convert hfiber a b using 1
      congr 1
      ext t
      simp)
    have hc' : (S.card : ℝ) ≤ 30000000 * ∑ a, (Fintype.card {b // R a b} : ℝ) := by
      exact_mod_cast hc
    apply harea.trans (ENNReal.ofReal_le_ofReal ?_)
    have hh := mul_le_mul_of_nonneg_left hc' (by positivity : 0 ≤ 600 * δ * ℓ)
    nlinarith only [hh]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
