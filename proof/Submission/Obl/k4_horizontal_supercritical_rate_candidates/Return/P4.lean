import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.P3
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Spread
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.BlockNorm

/-!
# Fourth pruning: Scalar states against deep labels

Entries are (candidate label, Scalar cell, terminal bin) inside a kept set `G ⊆ G0`. The
reference weight of an entry is the total `q_e ν(A_e)` of the deep labels meeting it; a deep
label meets at most 27 entries, so the budget is 27. Velocity domination of the deep labels then
gives every kept entry the conditional palette bound
`ρs(E ∩ direction v) ≤ K K₁ ρs(E) π(v)`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem measurable_tau (t₀ q : ℝ) : Measurable (fun p : α × ℝ => tau t₀ q p.2) := by
  unfold tau; exact (measurable_snd.sub_const _).div_const _

theorem measurableSet_blockCell_eq {y0 y1 : α → ℝ} (hy0 : Measurable y0) (hy1 : Measurable y1)
    (t₀ q σ : ℝ) (z : Fin 2 → ℤ) :
    MeasurableSet {p : α × ℝ | blockCell t₀ q σ y0 y1 p = z} := by
  have h0 : Measurable (fun p : α × ℝ => ⌊tau t₀ q p.2 / σ⌋) :=
    Int.measurable_floor.comp ((measurable_tau t₀ q).div_const σ)
  have h1 : Measurable (fun p : α × ℝ => ⌊(y0 p.1 + tau t₀ q p.2 * y1 p.1) / σ⌋) :=
    Int.measurable_floor.comp (((hy0.comp measurable_fst).add
      ((measurable_tau t₀ q).mul (hy1.comp measurable_fst))).div_const σ)
  have e : {p : α × ℝ | blockCell t₀ q σ y0 y1 p = z} =
      {p | ⌊tau t₀ q p.2 / σ⌋ = z 0} ∩ {p | ⌊(y0 p.1 + tau t₀ q p.2 * y1 p.1) / σ⌋ = z 1} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · intro h; exact ⟨by rw [← h]; rfl, by rw [← h]; rfl⟩
    · rintro ⟨e0, e1⟩
      funext k
      fin_cases k
      · exact e0
      · exact e1
  rw [e]
  exact (h0 (measurableSet_singleton _)).inter (h1 (measurableSet_singleton _))

theorem measurable_blockVal {x0 x1 : α → ℝ} (hx0 : Measurable x0) (hx1 : Measurable x1)
    (t₀ q : ℝ) : Measurable (blockVal t₀ q x0 x1) := by
  unfold blockVal
  exact (hx0.comp measurable_fst).add ((measurable_tau t₀ q).mul (hx1.comp measurable_fst))

namespace CoreData

variable (D : CoreData α)

/-- Scalar cell of a point in the block of candidate label `iq`. -/
def zc (σ : ℝ) (iq : Fin D.fc.n) (p : α × ℝ) : Fin 2 → ℤ :=
  blockCell (D.tQ iq) D.fc.q σ (D.ny0 iq) (D.ny1 iq) p

/-- Scalar value of a point in the block of candidate label `iq`. -/
def xv (iq : Fin D.fc.n) (p : α × ℝ) : ℝ := blockVal (D.tQ iq) D.fc.q (D.nx0 iq) (D.nx1 iq) p

/-- P4 entries. -/
def E4 (G : Set (α × ℝ)) (σ at' : ℝ) (e : (Fin D.fc.n × (Fin 2 → ℤ)) × ℤ) : Set (α × ℝ) :=
  G ∩ (D.fc.B e.1.1 ×ˢ D.fc.I e.1.1) ∩ {p | D.zc σ e.1.1 p = e.1.2} ∩
    {p | ⌊D.xv e.1.1 p / at'⌋ = e.2}

/-- Deep labels meeting an entry. -/
def deepMeet (G : Set (α × ℝ)) (σ at' : ℝ) (e : (Fin D.fc.n × (Fin 2 → ℤ)) × ℤ) :
    Finset (Fin D.fe.n) := by
  classical
  exact Finset.univ.filter (fun e' => (D.E4 G σ at' e ∩ (D.fe.B e' ×ˢ D.fe.I e')).Nonempty)

/-- P4 reference weights. -/
def R4 (G : Set (α × ℝ)) (σ at' : ℝ) (e : (Fin D.fc.n × (Fin 2 → ℤ)) × ℤ) : ℝ≥0∞ :=
  ∑ e' ∈ D.deepMeet G σ at' e, ENNReal.ofReal D.fe.q * D.ν (D.fe.A e')

/-- Points kept by P4. -/
def G4 (G : Set (α × ℝ)) (σ at' K₁ : ℝ) : Set (α × ℝ) :=
  pruned D.ρs G (D.E4 G σ at') (D.R4 G σ at') (ENNReal.ofReal K₁)

end CoreData

/-- The ancestor fit of a candidate label is the coarse fit of the point's coarse label. -/
theorem Lanc_eq (D : CoreData α) (H : CoreHyp D) {iq : Fin D.fc.n} {p : α × ℝ}
    (hp0 : p ∈ D.G0) (hpq : p.1 ∈ D.fc.B iq ∧ p.2 ∈ D.fc.I iq) {j : Fin D.f₀.n}
    (hj : p.1 ∈ D.f₀.B j ∧ p.2 ∈ D.f₀.I j) : D.Lanc iq = D.f₀.L j := by
  classical
  have hex : ∃ h₀ : Fin D.f₀.n, D.fc.A iq ⊆ D.f₀.A h₀ ∧ D.fc.I iq ⊆ D.f₀.I h₀ := H.nest0 iq
  unfold CoreData.Lanc
  rw [dite_cond_eq_true (eq_true hex)]
  have hspec := Classical.choose_spec hex
  have : Classical.choose hex = j := D.f₀.label_unique H.f₀good.disj hp0.2.1
    ⟨hspec.1 (H.fcgood.BA iq hpq.1), hspec.2 hpq.2⟩ ⟨H.f₀good.BA j hj.1, hj.2⟩
  rw [this]

/-- Coefficient bounds of the ancestor fit. -/
theorem Lanc_coeff (D : CoreData α) (H : CoreHyp D) {iq : Fin D.fc.n} {p : α × ℝ}
    (hp0 : p ∈ D.G0) (hpq : p.1 ∈ D.fc.B iq ∧ p.2 ∈ D.fc.I iq) :
    |D.Lanc iq 1| ≤ 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) ∧
      |D.Lanc iq 2| ≤ 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) ∧
      |D.Lanc iq 3| ≤ 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) := by
  obtain ⟨j, hBj, hIj⟩ := hp0.2.2.2.2.1
  rw [Lanc_eq D H hp0 hpq ⟨hBj, hIj⟩]
  have hN0 : 0 < D.N := by linarith [H.N2]
  exact horizontal_affine_coeff_bounds (D.f₀.L j) H.K1 (Real.rpow_nonneg hN0.le _)
    (f₀_q_pos D) (f₀_q_le_one D) (abs_x1_le_of_native D hp0.1) hp0.1.1 (H.f₀good.L3bd j)
    (H.f₀good.slope j p.1 hBj p.2 hIj)

/-- Difference of Scalar values of two points of one candidate label. -/
theorem xv_sub_le (D : CoreData α) (H : CoreHyp D) {iq : Fin D.fc.n} {p p' : α × ℝ}
    (hp0 : p ∈ D.G0) (hpq : p.1 ∈ D.fc.B iq ∧ p.2 ∈ D.fc.I iq) :
    |D.xv iq p - D.xv iq p'| ≤ (|x3 D.b p.1 p.2 - x3 D.b p'.1 p'.2| +
      2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) * (|p.2 - p'.2| + |x1 D.b p.1 p.2 - x1 D.b p'.1 p'.2| +
        |x2 D.b p.1 p.2 - x2 D.b p'.1 p'.2|)) / D.a₀ := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hq : D.fc.q ≠ 0 := by unfold Fam.q; positivity
  obtain ⟨c1, c2, c3⟩ := Lanc_coeff D H hp0 hpq
  unfold CoreData.xv
  rw [D.blockVal_eq iq p hq, D.blockVal_eq iq p' hq, ← sub_div, abs_div, abs_of_pos ha0]
  apply div_le_div_of_nonneg_right _ ha0.le
  set C := 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2)
  set L := D.Lanc iq
  have e : x3 D.b p.1 p.2 - (L 0 + L 1 * p.2 + L 2 * x1 D.b p.1 p.2 + L 3 * x2 D.b p.1 p.2) -
      (x3 D.b p'.1 p'.2 - (L 0 + L 1 * p'.2 + L 2 * x1 D.b p'.1 p'.2 + L 3 * x2 D.b p'.1 p'.2)) =
      (x3 D.b p.1 p.2 - x3 D.b p'.1 p'.2) - (L 1 * (p.2 - p'.2) +
        L 2 * (x1 D.b p.1 p.2 - x1 D.b p'.1 p'.2) + L 3 * (x2 D.b p.1 p.2 - x2 D.b p'.1 p'.2)) := by
    ring
  rw [e]
  have hC : 0 ≤ C := (abs_nonneg _).trans c1
  calc _ ≤ |x3 D.b p.1 p.2 - x3 D.b p'.1 p'.2| + |L 1 * (p.2 - p'.2) +
        L 2 * (x1 D.b p.1 p.2 - x1 D.b p'.1 p'.2) + L 3 * (x2 D.b p.1 p.2 - x2 D.b p'.1 p'.2)| :=
        abs_sub _ _
    _ ≤ |x3 D.b p.1 p.2 - x3 D.b p'.1 p'.2| + (C * |p.2 - p'.2| +
        C * |x1 D.b p.1 p.2 - x1 D.b p'.1 p'.2| + C * |x2 D.b p.1 p.2 - x2 D.b p'.1 p'.2|) := by
        gcongr
        refine (abs_add_three _ _ _).trans (add_le_add (add_le_add ?_ ?_) ?_) <;> rw [abs_mul]
        · exact mul_le_mul_of_nonneg_right c1 (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_right c2 (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_right c3 (abs_nonneg _)
    _ = _ := by ring

/-- Scalar coordinates of a point of a candidate label. -/
theorem zc_apply (D : CoreData α) (σ : ℝ) (iq : Fin D.fc.n) (p : α × ℝ) :
    D.zc σ iq p 0 = ⌊(p.2 - D.tQ iq) / D.fc.q / σ⌋ ∧
      D.zc σ iq p 1 = ⌊(x1 D.b p.1 p.2 - D.ZQ iq) / D.fc.q / σ⌋ := by
  have hq : D.fc.q ≠ 0 := by unfold Fam.q; positivity
  refine ⟨rfl, ?_⟩
  show ⌊(D.ny0 iq p.1 + tau (D.tQ iq) D.fc.q p.2 * D.ny1 iq p.1) / σ⌋ = _
  rw [D.blockY_eq iq p hq]

theorem E4_uniq (D : CoreData α) (H : CoreHyp D) {G : Set (α × ℝ)} (hG : G ⊆ D.G0)
    (σ at' : ℝ) : ∀ x e e', x ∈ D.E4 G σ at' e → x ∈ D.E4 G σ at' e' → e = e' := by
  intro x e e' hx hx'
  have hiq : e.1.1 = e'.1.1 := D.fc.label_unique H.fcgood.disj (hG hx.1.1.1).2.2.1
    ⟨H.fcgood.BA _ hx.1.1.2.1, hx.1.1.2.2⟩ ⟨H.fcgood.BA _ hx'.1.1.2.1, hx'.1.1.2.2⟩
  obtain ⟨⟨⟨-, -⟩, hz⟩, hj⟩ := hx
  obtain ⟨⟨⟨-, -⟩, hz'⟩, hj'⟩ := hx'
  have hz2 : e.1.2 = e'.1.2 := by
    rw [← hz, ← hz']; simp only [mem_ofPred_eq] at hz hz' ⊢; rw [hiq]
  have hj2 : e.2 = e'.2 := by
    rw [← hj, ← hj']; simp only [mem_ofPred_eq] at hj hj' ⊢; rw [hiq]
  exact Prod.ext (Prod.ext hiq hz2) hj2

theorem E4_subset (D : CoreData α) (G : Set (α × ℝ)) (σ at' : ℝ)
    (e : (Fin D.fc.n × (Fin 2 → ℤ)) × ℤ) : D.E4 G σ at' e ⊆ G := fun _ hx => hx.1.1.1

theorem measurableSet_E4 (D : CoreData α) (H : CoreHyp D) {G : Set (α × ℝ)}
    (hGm : MeasurableSet G) (σ at' : ℝ) (e : (Fin D.fc.n × (Fin 2 → ℤ)) × ℤ) :
    MeasurableSet (D.E4 G σ at' e) := by
  have hI : MeasurableSet (D.fc.I e.1.1) := by unfold Fam.I blk; exact measurableSet_Icc
  have hz : MeasurableSet {p : α × ℝ | D.zc σ e.1.1 p = e.1.2} :=
    measurableSet_blockCell_eq (D.measurable_ny0 H.bmeas) (D.measurable_ny1 H.bmeas) _ _ _ _
  have hj : MeasurableSet {p : α × ℝ | ⌊D.xv e.1.1 p / at'⌋ = e.2} :=
    (Int.measurable_floor.comp ((measurable_blockVal (D.measurable_nx0 H.bmeas)
      (D.measurable_nx1 H.bmeas) _ _).div_const at')) (measurableSet_singleton _)
  exact ((hGm.inter ((H.fcgood.measB e.1.1).prod hI)).inter hz).inter hj

theorem G4_subset (D : CoreData α) (G : Set (α × ℝ)) (σ at' K₁ : ℝ) :
    D.G4 G σ at' K₁ ⊆ G := pruned_subset _ _ _ _ _

theorem measurableSet_G4 (D : CoreData α) (H : CoreHyp D) {G : Set (α × ℝ)}
    (hGm : MeasurableSet G) (σ at' K₁ : ℝ) : MeasurableSet (D.G4 G σ at' K₁) :=
  measurableSet_pruned _ hGm _ _ _ (measurableSet_E4 D H hGm σ at')

theorem G4_loss (D : CoreData α) (G : Set (α × ℝ)) (σ at' K₁ : ℝ) :
    D.ρs (G \ D.G4 G σ at' K₁) ≤ (∑' e, D.R4 G σ at' e) / ENNReal.ofReal K₁ :=
  measure_diff_pruned_le _ _ _ _ _

/-- A kept entry survives whole and satisfies the conditional palette bound. -/
theorem G4_palette (D : CoreData α) (H : CoreHyp D) {G : Set (α × ℝ)} (hG : G ⊆ D.G0)
    {σ at' K₁ : ℝ} (hK₁ : 0 < K₁) {p : α × ℝ} (hp : p ∈ D.G4 G σ at' K₁)
    {e : (Fin D.fc.n × (Fin 2 → ℤ)) × ℤ} (hpe : p ∈ D.E4 G σ at' e) :
    D.E4 G σ at' e ⊆ D.G4 G σ at' K₁ ∧ ∀ v : ℤ,
      D.ρs (D.E4 G σ at' e ∩ {q | ⌊D.b q.1 3 / D.χ⌋ = v}) ≤
        ENNReal.ofReal (D.K * K₁) * D.ρs (D.E4 G σ at' e) *
          D.π (Ico ((v : ℝ) * D.χ) (((v : ℝ) + 1) * D.χ)) := by
  classical
  obtain ⟨hsub, hheavy⟩ := entry_subset_pruned (E4_uniq D H hG σ at') (E4_subset D G σ at') hp hpe
  refine ⟨hsub, fun v => ?_⟩
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hχ : 0 < D.χ := Real.rpow_pos_of_pos hN0 _
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  have hbin : {w : ℝ | ⌊w / D.χ⌋ = v} = Ico ((v : ℝ) * D.χ) (((v : ℝ) + 1) * D.χ) := by
    ext w; simp only [mem_ofPred_eq]; exact floor_div_eq_iff_mem_Ico hχ _
  set πv := D.π (Ico ((v : ℝ) * D.χ) (((v : ℝ) + 1) * D.χ))
  have hR : D.R4 G σ at' e ≤ ENNReal.ofReal K₁ * D.ρs (D.E4 G σ at' e) := by
    rw [ENNReal.div_le_iff (by simpa using hK₁) ENNReal.ofReal_ne_top] at hheavy
    rw [mul_comm]; exact hheavy
  have hcov : D.E4 G σ at' e ∩ {q | ⌊D.b q.1 3 / D.χ⌋ = v} ⊆
      ⋃ e' ∈ D.deepMeet G σ at' e, {q | q.1 ∈ D.fe.B e' ∧ q.2 ∈ D.fe.I e' ∧
        ⌊D.b q.1 3 / D.χ⌋ = v} := by
    intro q hq
    obtain ⟨e', hB, hI⟩ := (hG (E4_subset D G σ at' e hq.1)).2.2.2.2.2.2.1
    refine mem_iUnion₂.mpr ⟨e', ?_, hB, hI, hq.2⟩
    unfold CoreData.deepMeet
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hq.1, hB, hI⟩
  calc D.ρs (D.E4 G σ at' e ∩ {q | ⌊D.b q.1 3 / D.χ⌋ = v})
      ≤ ∑ e' ∈ D.deepMeet G σ at' e, D.μ {q | q.1 ∈ D.fe.B e' ∧ q.2 ∈ D.fe.I e' ∧
          ⌊D.b q.1 3 / D.χ⌋ = v} :=
        (measure_mono hcov).trans ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum (fun e' _ => (H.ρsρ.trans H.ρμ) _)))
    _ ≤ ∑ e' ∈ D.deepMeet G σ at' e, ENNReal.ofReal D.K * (ENNReal.ofReal D.fe.q *
          D.ν (D.fe.A e')) * πv := by
        refine Finset.sum_le_sum (fun e' _ => (H.fegood.vdom e' v).trans (le_of_eq ?_))
        rw [hbin, ENNReal.ofReal_mul hK0, mul_assoc (ENNReal.ofReal D.K)]
    _ = ENNReal.ofReal D.K * D.R4 G σ at' e * πv := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]; rfl
    _ ≤ ENNReal.ofReal D.K * (ENNReal.ofReal K₁ * D.ρs (D.E4 G σ at' e)) * πv := by gcongr
    _ = ENNReal.ofReal (D.K * K₁) * D.ρs (D.E4 G σ at' e) * πv := by
        rw [ENNReal.ofReal_mul hK0]; ring

/-- Points of one deep label lie in one candidate label. -/
theorem deep_same_cand (D : CoreData α) (H : CoreHyp D) {p : α × ℝ} (hp0 : p ∈ D.G0)
    {e' : Fin D.fe.n} (hpe : p.1 ∈ D.fe.B e' ∧ p.2 ∈ D.fe.I e') {iq : Fin D.fc.n}
    (hq : p.1 ∈ D.fc.B iq ∧ p.2 ∈ D.fc.I iq) :
    ∃ h : Fin D.fc.n, D.fe.A e' ⊆ D.fc.A h ∧ D.fe.I e' ⊆ D.fc.I h ∧ iq = h := by
  obtain ⟨h, hA, hI⟩ := H.nest1 e'
  exact ⟨h, hA, hI, D.fc.label_unique H.fcgood.disj hp0.2.2.1 ⟨H.fcgood.BA iq hq.1, hq.2⟩
    ⟨hA (H.fegood.BA e' hpe.1), hI hpe.2⟩⟩

/-- The deep spread hypothesis, in Scalar value units. -/
def CoreData.deepSpread (D : CoreData α) : ℝ :=
  (2 * (D.K * D.N ^ (-D.se)) + D.K * (1 + D.N ^ (-D.se) / D.fe.q) * (D.fe.q + 3 * D.K * D.fe.q) +
    D.K * (1 + D.N ^ (-D.se) / D.fe.q ^ 2) *
      (5 / 2 * D.K * D.fe.q * D.fe.q + 3 / 2 * D.K * D.fe.q * (3 * D.K * D.fe.q) +
        2 * (D.K * D.fe.q * D.N ^ (-D.κ * D.se))) +
    2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) * (D.fe.q + 3 * D.K * D.fe.q +
      (D.K * D.fe.q + D.K * (3 * D.K * D.fe.q) + 2 * (D.K * D.fe.q * D.N ^ (-D.κ * D.se))))) / D.a₀

/-- Two points of one deep label have Scalar states within one of each other. -/
theorem deep_state_close (D : CoreData α) (H : CoreHyp D) {σ at' : ℝ} (hσ : 0 < σ) (hat : 0 < at')
    (ht : D.fe.q / D.fc.q ≤ σ) (h1 : 3 * D.K * D.fe.q / D.fc.q ≤ σ) (hv : D.deepSpread ≤ at')
    {p p' : α × ℝ} (hp0 : p ∈ D.G0) (hp0' : p' ∈ D.G0) {e' : Fin D.fe.n}
    (hpe : p.1 ∈ D.fe.B e' ∧ p.2 ∈ D.fe.I e') (hpe' : p'.1 ∈ D.fe.B e' ∧ p'.2 ∈ D.fe.I e')
    {iq : Fin D.fc.n} (hq : p.1 ∈ D.fc.B iq ∧ p.2 ∈ D.fc.I iq) :
    |D.zc σ iq p 0 - D.zc σ iq p' 0| ≤ 1 ∧ |D.zc σ iq p 1 - D.zc σ iq p' 1| ≤ 1 ∧
      |⌊D.xv iq p / at'⌋ - ⌊D.xv iq p' / at'⌋| ≤ 1 := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  obtain ⟨hdt, hd1⟩ := label_spread_basic H.fegood ⟨H.fegood.BA e' hpe.1, hpe.2⟩
    ⟨H.fegood.BA e' hpe'.1, hpe'.2⟩
  obtain ⟨hd2, hd3⟩ := label_spread H.fegood H.K1 hN0 hpe hpe' hdt hd1
  obtain ⟨a0, a1⟩ := zc_apply D σ iq p
  obtain ⟨b0, b1⟩ := zc_apply D σ iq p'
  refine ⟨?_, ?_, ?_⟩
  · rw [a0, b0]
    apply floor_close hσ
    rw [← sub_div, abs_div, abs_of_pos hqc]
    have : (p.2 - D.tQ iq - (p'.2 - D.tQ iq)) = p.2 - p'.2 := by ring
    rw [this]
    exact (div_le_div_of_nonneg_right hdt hqc.le).trans ht
  · rw [a1, b1]
    apply floor_close hσ
    rw [← sub_div, abs_div, abs_of_pos hqc]
    have : (x1 D.b p.1 p.2 - D.ZQ iq - (x1 D.b p'.1 p'.2 - D.ZQ iq)) =
        x1 D.b p.1 p.2 - x1 D.b p'.1 p'.2 := by ring
    rw [this]
    exact (div_le_div_of_nonneg_right hd1 hqc.le).trans h1
  · apply floor_close hat
    refine (xv_sub_le D H hp0 hq).trans (le_trans ?_ hv)
    have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
    unfold CoreData.deepSpread
    apply div_le_div_of_nonneg_right _ ha0.le
    have hC : 0 ≤ 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) := by
      have := f₀_q_pos D; positivity
    have hsum : |p.2 - p'.2| + |x1 D.b p.1 p.2 - x1 D.b p'.1 p'.2| +
        |x2 D.b p.1 p.2 - x2 D.b p'.1 p'.2| ≤ D.fe.q + 3 * D.K * D.fe.q +
          (D.K * D.fe.q + D.K * (3 * D.K * D.fe.q) + 2 * (D.K * D.fe.q * D.N ^ (-D.κ * D.se))) :=
      add_le_add (add_le_add hdt hd1) hd2
    have := mul_le_mul_of_nonneg_left hsum hC
    linarith

/-- The P4 reference budget. -/
theorem R4_tsum_le (D : CoreData α) (H : CoreHyp D) {G : Set (α × ℝ)} (hG : G ⊆ D.G0)
    {σ at' : ℝ} (hσ : 0 < σ) (hat : 0 < at') (ht : D.fe.q / D.fc.q ≤ σ)
    (h1 : 3 * D.K * D.fe.q / D.fc.q ≤ σ) (hv : D.deepSpread ≤ at') :
    ∑' e, D.R4 G σ at' e ≤ 27 := by
  classical
  haveI := H.νprob
  set w : Fin D.fe.n → ℝ≥0∞ := fun e' => ENNReal.ofReal D.fe.q * D.ν (D.fe.A e') with hw
  have hR : ∀ e, D.R4 G σ at' e = ∑ e' : Fin D.fe.n,
      if (D.E4 G σ at' e ∩ (D.fe.B e' ×ˢ D.fe.I e')).Nonempty then w e' else 0 := by
    intro e; unfold CoreData.R4 CoreData.deepMeet; rw [Finset.sum_filter]
  have hper : ∀ e' : Fin D.fe.n, ∑' e : (Fin D.fc.n × (Fin 2 → ℤ)) × ℤ,
      (if (D.E4 G σ at' e ∩ (D.fe.B e' ×ˢ D.fe.I e')).Nonempty then w e' else 0) ≤ 27 * w e' := by
    intro e'
    by_cases hex : ∃ e₀, (D.E4 G σ at' e₀ ∩ (D.fe.B e' ×ˢ D.fe.I e')).Nonempty
    · obtain ⟨e₀, p₀, hp₀, hp₀e⟩ := hex
      set T : Finset ((Fin D.fc.n × (Fin 2 → ℤ)) × ℤ) :=
        ((Finset.Icc (-1 : ℤ) 1 ×ˢ Finset.Icc (-1 : ℤ) 1) ×ˢ Finset.Icc (-1 : ℤ) 1).image
          (fun abc => ((e₀.1.1, ![e₀.1.2 0 + abc.1.1, e₀.1.2 1 + abc.1.2]), e₀.2 + abc.2)) with hT
      have hTc : T.card ≤ 27 := by
        refine Finset.card_image_le.trans ?_
        simp
      have hmem : ∀ e, (D.E4 G σ at' e ∩ (D.fe.B e' ×ˢ D.fe.I e')).Nonempty → e ∈ T := by
        intro e ⟨p, hp, hpe⟩
        have hp0 := hG hp.1.1.1
        have hp₀0 := hG hp₀.1.1.1
        obtain ⟨h, -, -, hiq⟩ := deep_same_cand D H hp0 hpe hp.1.1.2
        obtain ⟨h', -, -, hiq₀⟩ := deep_same_cand D H hp₀0 hp₀e hp₀.1.1.2
        have hhh : h = h' := by
          obtain ⟨h1', hA1, hI1⟩ := H.nest1 e'
          have u1 : h = h1' := D.fc.label_unique H.fcgood.disj hp0.2.2.1
            ⟨hiq ▸ H.fcgood.BA _ hp.1.1.2.1, hiq ▸ hp.1.1.2.2⟩ ⟨hA1 (H.fegood.BA e' hpe.1), hI1 hpe.2⟩
          have u2 : h' = h1' := D.fc.label_unique H.fcgood.disj hp₀0.2.2.1
            ⟨hiq₀ ▸ H.fcgood.BA _ hp₀.1.1.2.1, hiq₀ ▸ hp₀.1.1.2.2⟩
            ⟨hA1 (H.fegood.BA e' hp₀e.1), hI1 hp₀e.2⟩
          rw [u1, u2]
        have hiqe : e.1.1 = e₀.1.1 := by rw [hiq, hiq₀, hhh]
        have hpq : p.1 ∈ D.fc.B e₀.1.1 ∧ p.2 ∈ D.fc.I e₀.1.1 := hiqe ▸ hp.1.1.2
        obtain ⟨c0, c1, cj⟩ := deep_state_close D H hσ hat ht h1 hv hp0 hp₀0 hpe hp₀e hpq
        have hz : D.zc σ e₀.1.1 p = e.1.2 := by rw [← hiqe]; exact hp.1.2
        have hj : ⌊D.xv e₀.1.1 p / at'⌋ = e.2 := by rw [← hiqe]; exact hp.2
        have hz₀ : D.zc σ e₀.1.1 p₀ = e₀.1.2 := hp₀.1.2
        have hj₀ : ⌊D.xv e₀.1.1 p₀ / at'⌋ = e₀.2 := hp₀.2
        rw [hz, hz₀] at c0 c1
        rw [hj, hj₀] at cj
        refine Finset.mem_image.mpr ⟨((e.1.2 0 - e₀.1.2 0, e.1.2 1 - e₀.1.2 1), e.2 - e₀.2), ?_, ?_⟩
        · have a0 := abs_le.mp c0; have a1 := abs_le.mp c1; have a2 := abs_le.mp cj
          simp only [Finset.mem_product, Finset.mem_Icc]
          omega
        · refine Prod.ext (Prod.ext ?_ ?_) ?_
          · exact hiqe.symm
          · funext k; fin_cases k <;> simp
          · simp
      rw [tsum_eq_sum (s := T) (fun e he => by
        rw [if_neg (fun h => he (hmem e h))])]
      calc ∑ e ∈ T, (if (D.E4 G σ at' e ∩ (D.fe.B e' ×ˢ D.fe.I e')).Nonempty then w e' else 0)
          ≤ ∑ _e ∈ T, w e' := Finset.sum_le_sum (fun e _ => by split_ifs <;> simp)
        _ = (T.card : ℝ≥0∞) * w e' := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 27 * w e' := by gcongr; exact_mod_cast hTc
    · push Not at hex
      have h0 : ∀ e : (Fin D.fc.n × (Fin 2 → ℤ)) × ℤ,
          (if (D.E4 G σ at' e ∩ (D.fe.B e' ×ˢ D.fe.I e')).Nonempty then w e' else 0) = 0 := by
        intro e; rw [if_neg (by rw [Set.not_nonempty_iff_eq_empty]; exact hex e)]
      simp only [h0, tsum_zero, zero_le]
  calc ∑' e, D.R4 G σ at' e
      = ∑' e : (Fin D.fc.n × (Fin 2 → ℤ)) × ℤ, ∑ e' : Fin D.fe.n,
          (if (D.E4 G σ at' e ∩ (D.fe.B e' ×ˢ D.fe.I e')).Nonempty then w e' else 0) :=
        tsum_congr hR
    _ = ∑ e' : Fin D.fe.n, ∑' e : (Fin D.fc.n × (Fin 2 → ℤ)) × ℤ,
          (if (D.E4 G σ at' e ∩ (D.fe.B e' ×ˢ D.fe.I e')).Nonempty then w e' else 0) :=
        Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ ≤ ∑ e' : Fin D.fe.n, 27 * w e' := Finset.sum_le_sum (fun e' _ => hper e')
    _ = 27 * ∑ e' : Fin D.fe.n, w e' := by rw [Finset.mul_sum]
    _ ≤ 27 * 1 := by
        gcongr
        exact label_weights_le_one D.ν D.fe H.fegood.measA H.fegood.disj
    _ = 27 := mul_one _

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
