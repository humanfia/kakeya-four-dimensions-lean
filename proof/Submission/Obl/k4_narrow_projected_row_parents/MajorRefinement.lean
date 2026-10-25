import Submission.Obl.k4_narrow_projected_row_parents.AlignedBins
import Submission.Obl.k4_general_parent_projected_layers.Layers
import Submission.Obl.k4_horizontal_coefficient_count.Selection
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

namespace Submission.Obl.k4_narrow_projected_row_parents.MajorRefinement

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

variable {α : Type} [MeasurableSpace α]

abbrev Index (n J : ℕ) := Fin n × Fin J × Fin J

def decode (n J : ℕ) : Fin (Fintype.card (Index n J)) ≃ Index n J :=
  (Fintype.equivFin (Index n J)).symm

def old (L : ProjLayer α) (J : ℕ) (i : Fin (Fintype.card (Index L.n J))) : Fin L.n :=
  (decode L.n J i).1

def fineTag (L : ProjLayer α) (J : ℕ) (i : Fin (Fintype.card (Index L.n J))) : Fin 2 → ℤ :=
  ![(J : ℤ) * L.tag (old L J i) 0 + ((decode L.n J i).2.1 : ℕ),
    (J : ℤ) * L.tag (old L J i) 1 + ((decode L.n J i).2.2 : ℕ)]

/-- Split each projected assignment into aligned major intercept and velocity bins. -/
def aligned (L : ProjLayer α) (b : α → Fin 6 → ℝ) (χ : ℝ) (J : ℕ) : ProjLayer α where
  n := Fintype.card (Index L.n J)
  β := L.β
  C := fun i => L.C (old L J i) ∩
    {l | ⌊b l 3 / (χ / J)⌋ = fineTag L J i 0 ∧ ⌊b l 0 / (χ / J)⌋ = fineTag L J i 1}
  tag := fineTag L J
  u := fun i => L.u (old L J i)
  v := fun i => L.v (old L J i)
  G := fun i => L.G (old L J i)

theorem aligned_measurable (L : ProjLayer α) {b : α → Fin 6 → ℝ} (hb : Measurable b)
    (χ : ℝ) (J : ℕ) (hL : ∀ i, MeasurableSet (L.C i)) :
    ∀ i, MeasurableSet ((aligned L b χ J).C i) := by
  intro i
  exact (hL _).inter ((measurableSet_eq_fun (by fun_prop) measurable_const).inter
    (measurableSet_eq_fun (by fun_prop) measurable_const))

theorem aligned_disjoint (L : ProjLayer α) (b : α → Fin 6 → ℝ) (χ : ℝ) (J : ℕ)
    (hL : ∀ i i', i ≠ i' → Disjoint (L.C i) (L.C i')) :
    ∀ i i', i ≠ i' → Disjoint ((aligned L b χ J).C i) ((aligned L b χ J).C i') := by
  intro i i' hii'
  apply disjoint_left.mpr
  rintro l ⟨hlo, hla, hlb⟩ ⟨hlo', hla', hlb'⟩
  have ho : old L J i = old L J i' := by
    by_contra hne
    exact disjoint_left.mp (hL _ _ hne) hlo hlo'
  apply hii'
  apply (decode L.n J).injective
  apply Prod.ext
  · exact ho
  · apply Prod.ext
    · apply Fin.ext
      have hval : (((decode L.n J i).2.1 : ℕ) : ℤ) = ((decode L.n J i').2.1 : ℕ) := by
        simp only [fineTag, Matrix.cons_val_zero, ho] at hla hla'
        linarith
      exact_mod_cast hval
    · apply Fin.ext
      have hval : (((decode L.n J i).2.2 : ℕ) : ℤ) = ((decode L.n J i').2.2 : ℕ) := by
        simp only [fineTag, Matrix.cons_val_one, Matrix.cons_val_fin_one, ho] at hlb hlb'
        linarith
      exact_mod_cast hval

theorem aligned_cover (L : ProjLayer α) (b : α → Fin 6 → ℝ) (χ : ℝ) {J : ℕ} (hJ : 0 < J)
    (htag : ∀ i l, l ∈ L.C i → ⌊b l 3 / χ⌋ = L.tag i 0 ∧ ⌊b l 0 / χ⌋ = L.tag i 1)
    {l : α} {i : Fin L.n} (hl : l ∈ L.C i) : ∃ j, l ∈ (aligned L b χ J).C j := by
  have h3 : b l 3 ∈ {x : ℝ | ⌊x / χ⌋ = L.tag i 0} := (htag i l hl).1
  have h0 : b l 0 ∈ {x : ℝ | ⌊x / χ⌋ = L.tag i 1} := (htag i l hl).2
  rw [aligned_bin_union χ hJ] at h3 h0
  obtain ⟨a, ha⟩ := mem_iUnion.mp h3
  obtain ⟨a', ha'⟩ := mem_iUnion.mp h0
  let j : Fin (Fintype.card (Index L.n J)) := (decode L.n J).symm (i, a, a')
  refine ⟨j, ?_⟩
  change l ∈ L.C (old L J j) ∧
    ⌊b l 3 / (χ / J)⌋ = fineTag L J j 0 ∧ ⌊b l 0 / (χ / J)⌋ = fineTag L J j 1
  simpa only [old, fineTag, j, Equiv.apply_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mem_ofPred_eq] using And.intro hl (And.intro ha ha')

theorem aligned_weight_sum (L : ProjLayer α) (b : α → Fin 6 → ℝ) (π : Measure ℝ)
    (N d s χ : ℝ) {J : ℕ} (hJ : 0 < J) :
    (∑ i, (aligned L b χ J).weight N d s (χ / J) π i) = ∑ i, L.weight N d s χ π i := by
  let f : Fin (Fintype.card (Index L.n J)) → ℝ≥0∞ :=
    fun i => (aligned L b χ J).weight N d s (χ / J) π i
  change (∑ i, f i) = _
  rw [← (decode L.n J).symm.sum_comp f]
  simp only [f, ProjLayer.weight, aligned, fineTag, old, Equiv.apply_symm_apply,
    Matrix.cons_val_zero, Fintype.sum_prod_type]
  simpa only [mul_assoc] using sum_aligned_reference π χ hJ (fun i : Fin L.n => L.tag i 0)
    (fun _ => (N ^ (-s)) ^ d * L.β)

/-- An arbitrary aligned subdivision admits a dense subfamily with the original
projected width and polynomial predictions. All floors remain under the original law. -/
theorem exists_dense_aligned_refinement (L : ProjLayer α)
    {N H d ell La s χ : ℝ} (hN : 0 < N) (hH : 1 ≤ H) (hχ : 0 < χ)
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (P : MvPolynomial (Fin 4) ℝ)
    (π : Measure ℝ) (ρ ζ : Measure (α × ℝ))
    (hgood : L.Good N H d ell La s χ b P π ρ)
    (hbudget : ∑ i, L.weight N d s χ π i ≤ ENNReal.ofReal H)
    (hζρ : ζ ≤ ρ) (hmass : ENNReal.ofReal H⁻¹ ≤ ζ univ)
    (hcover : ∀ᵐ z ∂ζ, z.2 ∈ Icc (0 : ℝ) 1 ∧ ∃ i, z.1 ∈ L.C i)
    {J : ℕ} (hJ : 0 < J) :
    ∃ (L' : ProjLayer α) (ζ' : Measure (α × ℝ)) (toOld : Fin L'.n → Fin L.n),
      ζ' ≤ ζ ∧ ENNReal.ofReal ((4 * H ^ 2)⁻¹) ≤ ζ' univ ∧ L'.β = L.β ∧
      L'.Good N (4 * H ^ 2) d ell La s (χ / J) b P π ρ ∧
      (∀ i, L'.C i ⊆ L.C (toOld i) ∧ L'.u i = L.u (toOld i) ∧
        L'.v i = L.v (toOld i) ∧ L'.G i = L.G (toOld i)) ∧
      ∀ᵐ z ∂ζ', ∃ i, z.1 ∈ L'.C i := by
  classical
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  let H' : ℝ := 4 * H ^ 2
  have hH'pos : 0 < H' := by dsimp [H']; positivity
  have h2H : 2 * H ≤ H' := by dsimp [H']; nlinarith
  have hHH' : H ≤ H' := by linarith
  have hχ' : 0 < χ / J := div_pos hχ (by exact_mod_cast hJ)
  let A := aligned L b χ J
  have hAm : ∀ i, MeasurableSet (A.C i) := aligned_measurable L hb χ J hgood.2.2.2.1
  have hAd : ∀ i i', i ≠ i' → Disjoint (A.C i) (A.C i') :=
    aligned_disjoint L b χ J hgood.2.2.2.2.1
  have hAW : ∑ i, A.weight N d s (χ / J) π i ≤ ENNReal.ofReal H := by
    rw [show (∑ i, A.weight N d s (χ / J) π i) = ∑ i, L.weight N d s χ π i from
      aligned_weight_sum L b π N d s χ hJ]
    exact hbudget
  let W : Fin A.n → Set (α × ℝ) := fun i => A.C i ×ˢ Icc (0 : ℝ) 1
  let w : Fin A.n → ℝ≥0∞ := fun i => ENNReal.ofReal H'⁻¹ * A.weight N d s (χ / J) π i
  have hWa : ∀ᵐ z ∂ζ, ∃ i, z ∈ W i := by
    filter_upwards [hcover] with z hz
    obtain ⟨i, hi⟩ := hz.2
    obtain ⟨j, hj⟩ := aligned_cover L b χ hJ
      (fun i l hl => And.intro ((hgood.2.2.2.2.2 i).2.2.2.1 l hl).1
        ((hgood.2.2.2.2.2 i).2.2.2.1 l hl).2.1) hi
    exact ⟨j, hj, hz.1⟩
  obtain ⟨ζ', hζ', hloss, n', idx, hinj, hfloor, hcov⟩ :=
    Submission.Obl.k4_horizontal_coefficient_count.finite_floor_subfamilies ζ
      (fun _ : Fin 1 => A.n) (fun _ i => W i)
      (fun _ i => (hAm i).prod measurableSet_Icc) (fun _ i => w i)
      (fun _ => ae_iff.mp hWa)
  have hwbudget : ∑ r : Fin 1, ∑ i, w i ≤ ENNReal.ofReal ((2 * H)⁻¹) := by
    simp only [Fin.sum_univ_one]
    calc (∑ i, w i) = ENNReal.ofReal H'⁻¹ * ∑ i, A.weight N d s (χ / J) π i := by
           dsimp [w]
           rw [Finset.mul_sum]
         _ ≤ ENNReal.ofReal H'⁻¹ * ENNReal.ofReal H := by gcongr
         _ = ENNReal.ofReal (H / H') := by
           rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hH'pos.le)]
           congr 1
           ring
         _ ≤ ENNReal.ofReal ((2 * H)⁻¹) := by
           apply ENNReal.ofReal_le_ofReal
           have hid : H / H' = (4 * H)⁻¹ := by dsimp [H']; field_simp <;> ring
           rw [hid]
           exact inv_anti₀ (by positivity) (by linarith)
  have hmass' : ENNReal.ofReal H'⁻¹ ≤ ζ' univ := by
    apply le_trans (ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) h2H))
    have hid : H⁻¹ / 2 = (2 * H)⁻¹ := by field_simp
    have hhalf := Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
      (ζ univ) (ζ' univ) (ENNReal.ofReal ((2 * H)⁻¹)) H⁻¹ (by positivity) hmass
      (hloss.trans (add_le_add le_rfl hwbudget)) (by rw [hid])
    simpa only [hid] using hhalf
  let L' : ProjLayer α :=
    ⟨n' 0, L.β, fun i => A.C (idx 0 i), fun i => A.tag (idx 0 i),
      fun i => A.u (idx 0 i), fun i => A.v (idx 0 i), fun i => A.G (idx 0 i)⟩
  have hweight (i : Fin A.n) : ENNReal.ofReal ((χ / J) * (N ^ (-s)) ^ d * A.β / H') *
      π {x : ℝ | ⌊x / (χ / J)⌋ = A.tag i 0} = w i := by
    have hbase : 0 ≤ (χ / J) * (N ^ (-s)) ^ d * A.β := by
      have hβ : 0 < A.β := hgood.1
      positivity
    dsimp [w, ProjLayer.weight]
    rw [div_eq_mul_inv, ENNReal.ofReal_mul hbase]
    ac_rfl
  have hgoodH' := hgood.mono hN hHpos hHH' hχ.le
  obtain ⟨hβ, hlo, hup, -, -, hlabels⟩ := hgoodH'
  have hL' : L'.Good N H' d ell La s (χ / J) b P π ρ := by
    refine ⟨hβ, hlo, hup, fun i => hAm _, ?_, ?_⟩
    · intro i i' hii'
      exact hAd _ _ (fun h => hii' (hinj 0 h))
    · intro i
      have hi := hlabels (old L J (idx 0 i))
      refine ⟨hi.1, hi.2.1, hi.2.2.1, ?_, ?_⟩
      · rintro l ⟨hl, hb3, hb0⟩
        exact ⟨hb3, hb0, ((hi.2.2.2.1 l hl).2.2)⟩
      · change ENNReal.ofReal ((χ / J) * (N ^ (-s)) ^ d * A.β / H') *
          π {x : ℝ | ⌊x / (χ / J)⌋ = A.tag (idx 0 i) 0} ≤ ρ (W (idx 0 i))
        rw [hweight]
        exact (hfloor 0 i).trans ((hζ'.trans hζρ) _)
  refine ⟨L', ζ', fun i => old L J (idx 0 i), hζ', hmass', rfl, hL', ?_, ?_⟩
  · intro i
    exact ⟨inter_subset_left, rfl, rfl, rfl⟩
  · have hc : ∀ᵐ z ∂ζ', ∃ i, z ∈ W (idx 0 i) := ae_iff.mpr (hcov 0)
    filter_upwards [hc] with z hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, hi.1⟩

end

end Submission.Obl.k4_narrow_projected_row_parents.MajorRefinement
