-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.DenseContacts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.Restricted
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGeometry
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactWindows
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.SlopeWindow
import Submission.WZ.Obl.wz_jet_whitney_rich_reduction.WhitneyCover

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment (strip JetControlled)

/-- A point satisfying the frozen rich and few-transverse-pair conditions
has large incident subfamilies of both colors near one common value and slope.
This is a pointwise extraction; it asserts no global count of such contacts. -/
theorem exists_dense_contacts {n : ℕ} (A B : Finset (Fin n))
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    {δ κ D μ : ℝ} {p : ℝ × ℝ}
    (hκ : 0 ≤ κ) (hD : 0 ≤ D) (hμ : 0 < μ)
    (hupper : ∀ i ∈ A, ∀ j ∈ B, dist (q i) (q j) ≤ 2 * D)
    (hA : ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p)
    (hB : ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p)
    (hT : transverseMultiplicity A B δ κ q g p < ENNReal.ofReal (μ ^ 2 / 100)) :
    ∃ a ∈ A, p ∈ strip δ (g a) ∧
      ∃ A' B' : Finset (Fin n), A' ⊆ A ∧ B' ⊆ B ∧
        μ / 2 ≤ (A'.card : ℝ) ∧ μ / 2 ≤ (B'.card : ℝ) ∧
        ∀ i ∈ A' ∪ B', p ∈ strip δ (g i) ∧
          NearContact (2 * δ) (4 * κ * D) (g i) (g a) p.2 := by
  classical
  let U := A.filter fun i => p ∈ strip δ (g i)
  let V := B.filter fun i => p ∈ strip δ (g i)
  let s : Fin n → ℝ := fun i => deriv (g i) p.2
  let η := 2 * κ * D
  let E := (U ×ˢ V).filter fun ij => η ≤ |s ij.1 - s ij.2|
  have hAc : μ ≤ (U.card : ℝ) := by
    have he := WangZahlLot.Obl.wz_jet_whitney_rich_reduction.multOn_eq_card
      (fun i => strip δ (g i)) A p
    change finiteMultiplicity A δ g p = (U.card : ENNReal) at he
    rw [he] at hA
    exact ENNReal.ofReal_le_natCast.mp hA
  have hBc : μ ≤ (V.card : ℝ) := by
    have he := WangZahlLot.Obl.wz_jet_whitney_rich_reduction.multOn_eq_card
      (fun i => strip δ (g i)) B p
    change finiteMultiplicity B δ g p = (V.card : ENNReal) at he
    rw [he] at hB
    exact ENNReal.ofReal_le_natCast.mp hB
  have hE : E = (A ×ˢ B).filter fun ij =>
      p ∈ strip δ (g ij.1) ∧ p ∈ strip δ (g ij.2) ∧ η ≤ |s ij.1 - s ij.2| := by
    ext ij
    simp only [E, U, V, Finset.mem_filter, Finset.mem_product]
    tauto
  have hcount : (E.card : ENNReal) ≤ transverseMultiplicity A B δ κ q g p := by
    rw [hE, ← Finset.sum_boole]
    unfold transverseMultiplicity
    rw [← Finset.sum_product']
    apply Finset.sum_le_sum
    intro ij hij
    split_ifs with hp
    · obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
      have hs : κ * dist (q ij.1) (q ij.2) ≤ |s ij.1 - s ij.2| := by
        have hh := mul_le_mul_of_nonneg_left (hupper ij.1 hi ij.2 hj) hκ
        dsimp [η] at hp
        linarith [hp.2.2]
      rw [indicator_of_mem (show p ∈ strip δ (g ij.1) ∩ strip δ (g ij.2) ∩
          {p | κ * dist (q ij.1) (q ij.2) ≤
            |deriv (g ij.1) p.2 - deriv (g ij.2) p.2|} from ⟨⟨hp.1, hp.2.1⟩, hs⟩)]
    · exact zero_le
  have hbad : (E.card : ℝ) < μ ^ 2 / 4 := by
    have he : ENNReal.ofReal (E.card : ℝ) < ENNReal.ofReal (μ ^ 2 / 100) := by
      simpa only [ENNReal.ofReal_natCast] using hcount.trans_lt hT
    have hb := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < μ ^ 2 / 100)).mp he
    nlinarith [sq_pos_of_pos hμ]
  obtain ⟨a, ha, hUA, hVB⟩ := exists_bipartite_slope_window U V s s hμ hAc hBc hbad
  let A' := U.filter fun i => |s i - s a| ≤ 2 * η
  let B' := V.filter fun i => |s a - s i| < η
  obtain ⟨haA, hpa⟩ := Finset.mem_filter.mp ha
  refine ⟨a, haA, hpa, A', B', ?_, ?_, hUA, hVB, ?_⟩
  · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  · intro i hi
    have hpi : p ∈ strip δ (g i) := by
      rcases Finset.mem_union.mp hi with hi | hi
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    refine ⟨hpi, ?_, ?_⟩
    · have hv := abs_sub_le (g i p.2) p.1 (g a p.2)
      rw [abs_sub_comm (g i p.2) p.1] at hv
      linarith [hpi.2, hpa.2]
    · rcases Finset.mem_union.mp hi with hi | hi
      · have hs := (Finset.mem_filter.mp hi).2
        dsimp [s, η] at hs
        linarith
      · have hs := (Finset.mem_filter.mp hi).2
        dsimp [s, η] at hs
        rw [abs_sub_comm] at hs
        have hκD := mul_nonneg hκ hD
        linarith

/-- The two extracted subfamilies form a complete bipartite family of narrow
overlaps after a constant enlargement of the slope threshold. -/
theorem exists_dense_narrow_biclique {n : ℕ} (A B : Finset (Fin n))
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    {δ κ D μ : ℝ} {p : ℝ × ℝ}
    (hκ : 0 < κ) (hD : 0 < D) (hμ : 0 < μ)
    (hcross : ∀ i ∈ A, ∀ j ∈ B,
      D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2 * D)
    (hA : ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p)
    (hB : ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p)
    (hT : transverseMultiplicity A B δ κ q g p < ENNReal.ofReal (μ ^ 2 / 100)) :
    ∃ A' B' : Finset (Fin n), A' ⊆ A ∧ B' ⊆ B ∧
      μ / 2 ≤ (A'.card : ℝ) ∧ μ / 2 ≤ (B'.card : ℝ) ∧
      ∀ i ∈ A', ∀ j ∈ B',
        p ∈ narrowIntersection δ (9 * κ) (q i) (q j) (g i) (g j) := by
  classical
  obtain ⟨a, _, _, A', B', hAs, hBs, hAc, hBc, hcontact⟩ :=
    exists_dense_contacts A B hκ.le hD.le hμ
      (fun i hi j hj => (hcross i hi j hj).2) hA hB hT
  refine ⟨A', B', hAs, hBs, hAc, hBc, ?_⟩
  intro i hi j hj
  obtain ⟨hpi, hci⟩ := hcontact i (Finset.mem_union_left _ hi)
  obtain ⟨hpj, hcj⟩ := hcontact j (Finset.mem_union_right _ hj)
  refine ⟨⟨hpi, hpj⟩, ?_⟩
  change |deriv (g i) p.2 - deriv (g j) p.2| < 9 * κ * dist (q i) (q j)
  have ht := abs_sub_le (deriv (g i) p.2) (deriv (g a) p.2) (deriv (g j) p.2)
  rw [abs_sub_comm (deriv (g a) p.2) (deriv (g j) p.2)] at ht
  have hfar := mul_le_mul_of_nonneg_left (hcross i (hAs hi) j (hBs hj)).1 hκ.le
  have hpos := mul_pos hκ hD
  linarith [hci.2, hcj.2]

/-- Rich contacts persist in a common curved band at every time scale meeting
both the linear and quadratic variation budgets. -/
theorem exists_rich_contact_band {n : ℕ} (A B : Finset (Fin n))
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    {δ κ D μ L : ℝ} {p : ℝ × ℝ}
    (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hD : 0 ≤ D) (hμ : 0 < μ) (hL : 0 ≤ L)
    (hdiamA : ∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D / 100)
    (hupper : ∀ i ∈ A, ∀ j ∈ B, dist (q i) (q j) ≤ 2 * D)
    (hA : ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p)
    (hB : ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p)
    (hT : transverseMultiplicity A B δ κ q g p < ENNReal.ofReal (μ ^ 2 / 100))
    (hlinear : κ * D * L ≤ δ) (hquadratic : D * L ^ 2 ≤ δ) :
    ∃ a ∈ A, p ∈ strip δ (g a) ∧
      ∃ A' B' : Finset (Fin n), A' ⊆ A ∧ B' ⊆ B ∧
        μ / 2 ≤ (A'.card : ℝ) ∧ μ / 2 ≤ (B'.card : ℝ) ∧
        ∀ v : ℝ × ℝ, v ∈ strip δ (g a) → |v.2 - p.2| ≤ L →
          ∀ i ∈ A' ∪ B', v ∈ strip (45 * δ) (g i) := by
  classical
  obtain ⟨a, ha, hpa, A', B', hAs, hBs, hAc, hBc, hcontact⟩ :=
    exists_dense_contacts A B hκ hD hμ hupper hA hB hT
  refine ⟨a, ha, hpa, A', B', hAs, hBs, hAc, hBc, ?_⟩
  intro v hv htime i hi
  have hdist : dist (q i) (q a) ≤ 2 * D := by
    rcases Finset.mem_union.mp hi with hi | hi
    · have hd := hdiamA i (hAs hi) a ha
      linarith
    · rw [dist_comm]
      exact hupper a ha i (hBs hi)
  exact ⟨hv.1, contact_band_value_le hg hjet i a hδ hκ hD hL hdist hpa.1 hv.1
    htime hv.2 (hcontact i hi).2 hlinear hquadratic⟩

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
