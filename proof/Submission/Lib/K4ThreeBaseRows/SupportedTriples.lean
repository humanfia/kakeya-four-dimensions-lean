/-
Adapted from: here:o266
Original: session x0947, branch x0947 of o266, file
Submission/Obl/k4_narrow_original_potential_atlas/SupportedTriples.lean (commit 7a10c8d8).
Moved into a library namespace; imports only Mathlib and modules already in lib.
-/

import Submission.Lib.K4ThreeBaseRows.RowBins
import Submission.Lib.K4DeterminantBreadth

/-! SUPPORTED SPANNING TRIPLES FROM AN ACTUAL CELL LAW.

Let one finite nonzero cell law `μ` with source `E` (`μ Eᶜ = 0`) be `Broad` in its lifted base
directions `(1, V)` at radius `ρ` with fraction `c`, and dominated per velocity bin of width
`s ≤ ρ/4` by an earlier palette: `μ(bin β) ≤ D M π(β)`. Then (`exists_supported_triples`):
- pick one actual incidence of `E` in each positive bin;
- the normalized bin weights stay broad at radius `ρ/2`;
- `K4DeterminantBreadth.good_weight` (`n = 3`) gives `Good` triples of total product weight
  `≥ c³`, and each has determinant `≥ (ρ/2)³` (`abs_det_ge_prod_infDist`);
- per-bin domination turns this into `c³ ≤ D³ Σ_{supported t} ∏ π(t_i)`.

The witnesses are actual incidences of `E`, so graph fits and `X'` lists that hold on `E` hold for
them. `coarse_row_bins_card_le_of_broad` feeds this into
`RowBinLists.coarse_row_bins_card_le_weighted`, with `K₁ = (D/c)³` and `δ = (ρ/2)³`. -/

namespace Submission.Lib.K4ThreeBaseRows

open MeasureTheory Set

noncomputable section

/-- Breadth of one finite law: every proper subspace misses a `c` fraction at distance `ρ`.
(The same definition as `Broad` in o266's `Breadth.lean`, by session x0947.) -/
def Broad {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (e : Ω → EuclideanSpace ℝ (Fin 3))
    (ρ c : ℝ) : Prop :=
  ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)), Module.finrank ℝ V < 3 →
    c * ν.real univ ≤ ν.real {x | ρ ≤ Metric.infDist (e x) (V : Set _)}

namespace SupportedTriples

open RowBinLists
open Submission.Lib.K4DeterminantBreadth (good_weight abs_det_ge_prod_infDist Good)

/-- The lifted base direction `(1, V₀, V₁)` as a Euclidean vector. -/
def liftE (V : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (lift V)

theorem liftE_apply (V : Fin 2 → ℝ) (k : Fin 3) : liftE V k = lift V k := rfl

theorem dist_liftE_le {V V' : Fin 2 → ℝ} {s : ℝ} (hs : 0 ≤ s) (h : ∀ k, |V k - V' k| ≤ s) :
    dist (liftE V) (liftE V') ≤ 2 * s := by
  rw [EuclideanSpace.dist_eq]
  have h0 := h 0
  have h1 := h 1
  have hsum : ∑ i : Fin 3, dist (liftE V i) (liftE V' i) ^ 2 ≤ (2 * s) ^ 2 := by
    simp only [Fin.sum_univ_three, liftE_apply, lift, Real.dist_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sub_self,
      abs_zero, sq_abs]
    have e0 : (V 0 - V' 0) ^ 2 ≤ s ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
    have e1 : (V 1 - V' 1) ^ 2 ≤ s ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith
  calc Real.sqrt (∑ i : Fin 3, dist (liftE V i) (liftE V' i) ^ 2) ≤ Real.sqrt ((2 * s) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = 2 * s := Real.sqrt_sq (by positivity)

theorem matrix_liftE_eq (V : Fin 3 → Fin 2 → ℝ) :
    (Matrix.of fun i j => liftE (V i) j) = witnessMatrix V := by
  ext i j
  rfl

theorem measurable_vbin {Ω : Type*} [MeasurableSpace Ω] {V : Ω → Fin 2 → ℝ} (hV : Measurable V)
    (s : ℝ) : Measurable fun x => vbin s (V x) := by
  apply measurable_pi_iff.mpr
  intro k
  exact (((measurable_pi_apply k).comp hV).div_const s).floor

theorem abs_sub_le_of_vbin_eq {V V' : Fin 2 → ℝ} {s : ℝ} (hs : 0 < s)
    (h : vbin s V = vbin s V') (k : Fin 2) : |V k - V' k| ≤ s :=
  abs_sub_le_of_floor_eq hs (congrFun h k)

/-- **Supported spanning triples from breadth and per-bin domination.** -/
theorem exists_supported_triples {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (E : Set Ω) (hE : μ Eᶜ = 0) (V : Ω → Fin 2 → ℝ) (hV : Measurable V)
    {s ρ c D : ℝ} (Bv : Finset (Fin 2 → ℤ)) (hBv : ∀ x ∈ E, vbin s (V x) ∈ Bv)
    (π : (Fin 2 → ℤ) → ℝ) (hs : 0 < s) (h4s : 4 * s ≤ ρ) (hc : 0 ≤ c) (hD : 0 < D)
    (hM : 0 < μ.real univ)
    (hdom : ∀ β, μ.real {x | vbin s (V x) = β} ≤ D * μ.real univ * π β)
    (hbroad : Broad μ (fun x => liftE (V x)) ρ c) :
    ∃ (Tc : Finset (Fin 3 → Fin 2 → ℤ)) (wit : (Fin 3 → Fin 2 → ℤ) → Fin 3 → Ω),
      (∀ t ∈ Tc, ∀ i, wit t i ∈ E ∧ vbin s (V (wit t i)) = t i ∧ t i ∈ Bv) ∧
      (∀ t ∈ Tc, (ρ / 2) ^ 3 ≤ |(witnessMatrix fun i => V (wit t i)).det|) ∧
      c ^ 3 ≤ D ^ 3 * ∑ t ∈ Tc, ∏ i, π (t i) := by
  classical
  set M := μ.real univ with hMdef
  let bin : (Fin 2 → ℤ) → Set Ω := fun β => {x | vbin s (V x) = β}
  have hbinm : ∀ β, MeasurableSet (bin β) := fun β =>
    measurable_vbin hV s (measurableSet_singleton β)
  set Bpos := Bv.filter fun β => 0 < μ.real (bin β) with hBpos
  have hex : ∀ β ∈ Bpos, ∃ x ∈ E, vbin s (V x) = β := by
    intro β hβ
    have hpos : 0 < μ.real (bin β) := (Finset.mem_filter.mp hβ).2
    by_contra hno
    push_neg at hno
    have hsub : bin β ⊆ Eᶜ := fun x hx hxE => hno x hxE hx
    have h0 : μ (bin β) = 0 := measure_mono_null hsub hE
    rw [Measure.real, h0, ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  have hne : (univ : Set Ω).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have h0 : μ.real (univ : Set Ω) = 0 := by rw [h, measureReal_empty]
    rw [← hMdef] at h0
    linarith
  obtain ⟨x₀, -⟩ := hne
  let ι := {β // β ∈ Bpos}
  let rep : ι → Ω := fun β => (hex β.1 β.2).choose
  have hrepE : ∀ β, rep β ∈ E := fun β => (hex β.1 β.2).choose_spec.1
  have hrepbin : ∀ β, vbin s (V (rep β)) = β.1 := fun β => (hex β.1 β.2).choose_spec.2
  let e : ι → EuclideanSpace ℝ (Fin 3) := fun β => liftE (V (rep β))
  let w : ι → ℝ := fun β => μ.real (bin β.1) / M
  have hw0 : ∀ β, 0 ≤ w β := fun β => div_nonneg measureReal_nonneg hM.le
  -- the bins of `Bv` carry all the mass
  have hcover : ∀ x ∈ E, x ∈ ⋃ β ∈ Bv, bin β := fun x hx =>
    mem_iUnion₂.mpr ⟨vbin s (V x), hBv x hx, rfl⟩
  have hzero : ∀ β ∈ Bv, β ∉ Bpos → μ (bin β) = 0 := by
    intro β hβ hnot
    have hle : μ.real (bin β) ≤ 0 := by
      by_contra h
      push_neg at h
      exact hnot (Finset.mem_filter.mpr ⟨hβ, h⟩)
    have h0 : μ.real (bin β) = 0 := le_antisymm hle measureReal_nonneg
    exact (measureReal_eq_zero_iff).mp h0
  have hdisj : Set.PairwiseDisjoint (↑Bv : Set (Fin 2 → ℤ)) bin := by
    intro β _ β' _ hne'
    exact Set.disjoint_left.mpr fun x hx hx' => hne' (hx.symm.trans hx')
  have hsumBv : ∑ β ∈ Bv, μ.real (bin β) = M := by
    rw [← measureReal_biUnion_finset hdisj fun β _ => hbinm β]
    apply le_antisymm (measureReal_mono (subset_univ _))
    have hsub : univ ⊆ (⋃ β ∈ Bv, bin β) ∪ Eᶜ := by
      intro x _
      by_cases hx : x ∈ E
      · exact Or.inl (hcover x hx)
      · exact Or.inr hx
    have hEr : μ.real Eᶜ = 0 := by rw [Measure.real, hE, ENNReal.toReal_zero]
    calc M ≤ μ.real ((⋃ β ∈ Bv, bin β) ∪ Eᶜ) := measureReal_mono hsub
      _ ≤ μ.real (⋃ β ∈ Bv, bin β) + μ.real Eᶜ := measureReal_union_le _ _
      _ = μ.real (⋃ β ∈ Bv, bin β) := by rw [hEr, add_zero]
  have hsumBpos : ∑ β ∈ Bpos, μ.real (bin β) = M := by
    rw [← hsumBv, hBpos, Finset.sum_filter]
    refine Finset.sum_congr rfl fun β hβ => ?_
    split_ifs with h
    · rfl
    · have h0 : μ (bin β) = 0 := hzero β hβ (fun hm => h (Finset.mem_filter.mp hm).2)
      rw [Measure.real, h0, ENNReal.toReal_zero]
  have hwsum : ∑ β : ι, w β = 1 := by
    have h1 : ∑ β : ι, w β = (∑ β ∈ Bpos, μ.real (bin β)) / M := by
      rw [Finset.sum_div]
      exact (Finset.sum_coe_sort Bpos fun β => μ.real (bin β) / M)
    rw [h1, hsumBpos, div_self hM.ne']
  -- finite breadth at radius `ρ/2`
  have hfin : ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)), Module.finrank ℝ W < 3 →
      c * ∑ t, w t ≤ ∑ t, if ρ / 2 ≤ Metric.infDist (e t) (W : Set _) then w t else 0 := by
    intro W hW
    have hb := hbroad W hW
    set Sfar := {x : Ω | ρ ≤ Metric.infDist (liftE (V x)) (W : Set _)} with hSfar
    let good : Finset ι := Finset.univ.filter fun t => ρ / 2 ≤ Metric.infDist (e t) (W : Set _)
    have hsub : Sfar ⊆ (⋃ t ∈ good, bin t.1) ∪ ((⋃ β ∈ Bv.filter (· ∉ Bpos), bin β) ∪ Eᶜ) := by
      intro x hx
      by_cases hxE : x ∈ E
      · have hβ := hBv x hxE
        by_cases hpos : vbin s (V x) ∈ Bpos
        · left
          let t : ι := ⟨vbin s (V x), hpos⟩
          refine mem_iUnion₂.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
          have hclose : dist (liftE (V x)) (e t) ≤ 2 * s :=
            dist_liftE_le hs.le fun k =>
              abs_sub_le_of_vbin_eq hs ((hrepbin t).symm ▸ rfl) k
          have hlip := Metric.infDist_le_infDist_add_dist (x := liftE (V x)) (y := e t)
            (s := (W : Set (EuclideanSpace ℝ (Fin 3))))
          have hx' : ρ ≤ Metric.infDist (liftE (V x)) (W : Set _) := hx
          linarith
        · right; left
          exact mem_iUnion₂.mpr ⟨vbin s (V x), Finset.mem_filter.mpr ⟨hβ, hpos⟩, rfl⟩
      · right; right
        exact hxE
    have hnull : μ.real ((⋃ β ∈ Bv.filter (· ∉ Bpos), bin β) ∪ Eᶜ) = 0 := by
      apply (measureReal_eq_zero_iff).mpr
      refine measure_union_null ?_ hE
      refine (measure_biUnion_null_iff (Finset.countable_toSet _)).mpr fun β hβ => ?_
      have hβ' := Finset.mem_filter.mp hβ
      exact hzero β hβ'.1 hβ'.2
    have hupper : μ.real Sfar ≤ ∑ t ∈ good, μ.real (bin t.1) := by
      calc μ.real Sfar ≤ μ.real ((⋃ t ∈ good, bin t.1) ∪
            ((⋃ β ∈ Bv.filter (· ∉ Bpos), bin β) ∪ Eᶜ)) := measureReal_mono hsub
        _ ≤ μ.real (⋃ t ∈ good, bin t.1) +
            μ.real ((⋃ β ∈ Bv.filter (· ∉ Bpos), bin β) ∪ Eᶜ) := measureReal_union_le _ _
        _ = μ.real (⋃ t ∈ good, bin t.1) := by rw [hnull, add_zero]
        _ ≤ ∑ t ∈ good, μ.real (bin t.1) := measureReal_biUnion_finset_le _ _
    have hgoodsum : ∑ t ∈ good, μ.real (bin t.1) =
        M * ∑ t, if ρ / 2 ≤ Metric.infDist (e t) (W : Set _) then w t else 0 := by
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs
      · simp only [w]; field_simp
      · rw [mul_zero]
    rw [hwsum, mul_one]
    have hcM : c * M ≤ M * ∑ t, if ρ / 2 ≤ Metric.infDist (e t) (W : Set _) then w t else 0 := by
      calc c * M ≤ μ.real Sfar := hb
        _ ≤ _ := hupper
        _ = _ := hgoodsum
    have := (mul_le_mul_iff_of_pos_left hM).mp (by linarith [hcM] :
      M * c ≤ M * ∑ t, if ρ / 2 ≤ Metric.infDist (e t) (W : Set _) then w t else 0)
    exact this
  have hG := good_weight e w hw0 (ρ / 2) c hc hfin 3 le_rfl
  rw [hwsum, mul_one] at hG
  -- the supported triples
  let goodT : Finset (Fin 3 → ι) := Finset.univ.filter fun T => Good e (ρ / 2) T
  let toT : (Fin 3 → ι) → Fin 3 → Fin 2 → ℤ := fun T i => (T i).1
  have hinj : Function.Injective toT := by
    intro T T' h
    funext i
    exact Subtype.ext (congrFun h i)
  refine ⟨goodT.image toT, fun t i => if h : t i ∈ Bpos then rep ⟨t i, h⟩ else x₀, ?_, ?_, ?_⟩
  · intro t ht i
    obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp ht
    have hmem : (T i).1 ∈ Bpos := (T i).2
    simp only [toT, hmem, dite_true]
    refine ⟨hrepE _, hrepbin _, (Finset.mem_filter.mp hmem).1⟩
  · intro t ht
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp ht
    have hgood : Good e (ρ / 2) T := (Finset.mem_filter.mp hT).2
    have hwit : (fun i => V (if h : (toT T) i ∈ Bpos then rep ⟨(toT T) i, h⟩ else x₀)) =
        fun i => V (rep (T i)) := by
      funext i
      have hmem : (T i).1 ∈ Bpos := (T i).2
      simp only [toT, hmem, dite_true, Subtype.coe_eta]
    rw [hwit, ← matrix_liftE_eq]
    have hρ2 : 0 ≤ ρ / 2 := by linarith
    calc (ρ / 2) ^ 3 = ∏ _i : Fin 3, ρ / 2 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i : Fin 3, Metric.infDist (e (T i))
          (Submodule.span ℝ ((fun i => e (T i)) '' Set.Iio i) :
            Set (EuclideanSpace ℝ (Fin 3))) :=
          Finset.prod_le_prod₀ (fun _ _ => hρ2) (fun i _ => hgood i)
      _ ≤ |(Matrix.of fun i j => e (T i) j).det| := abs_det_ge_prod_infDist 3 (fun i => e (T i))
  · rw [Finset.sum_image fun T _ T' _ h => hinj h]
    have hπw : ∀ β : ι, w β ≤ D * π β.1 := by
      intro β
      have h := hdom β.1
      calc w β = μ.real (bin β.1) / M := rfl
        _ ≤ D * M * π β.1 / M := div_le_div_of_nonneg_right h hM.le
        _ = D * π β.1 := by field_simp
    calc c ^ 3 ≤ ∑ T : Fin 3 → ι, if Good e (ρ / 2) T then ∏ j, w (T j) else 0 := hG
      _ = ∑ T ∈ goodT, ∏ j, w (T j) := by rw [Finset.sum_filter]
      _ ≤ ∑ T ∈ goodT, ∏ j, (D * π (T j).1) :=
          Finset.sum_le_sum fun T _ => Finset.prod_le_prod₀ (fun j _ => hw0 _) fun j _ => hπw _
      _ = D ^ 3 * ∑ T ∈ goodT, ∏ i, π (toT T i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Coarse row lists from actual broad cell laws.** Each fine cell `c` of a coarse cell has:
- a finite law `μ c` of positive mass, with source `E c` (`μ c (E c)ᶜ = 0`);
- velocity bins (width `s ≤ ρ/4`) in `Bv`;
- per-bin palette domination `μ c(bin β) ≤ D M_c π β`;
- `Broad` lifted base directions at radius `ρ` with fraction `c₀ > 0`;
- on `E c`, velocities `≤ K`, the graph fit `|X' - G c · (1,V)| ≤ ε`, and `X'` lists `L`;
- a row with `|G c| ≤ K`.

Then the occurring row bins number at most `(D/c₀)³ KL³ (2D'/s + 2)³ (Σ_{Bv} π)³`, where
`D' = rowRadius K ε s (ρ/2)³`. All witnesses are actual incidences of the sources. -/
theorem coarse_row_bins_card_le_of_broad {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    [Nonempty Ω] (cells : Finset ι) (μ : ι → Measure Ω) [∀ c, IsFiniteMeasure (μ c)]
    (E : ι → Set Ω) (G : ι → Fin 3 → ℝ) (V : Ω → Fin 2 → ℝ) (hVm : Measurable V) (X' : Ω → ℝ)
    (L : (Fin 2 → ℤ) → Finset ℤ) (π : (Fin 2 → ℤ) → ℝ) (Bv : Finset (Fin 2 → ℤ))
    {K ε s ρ c₀ D KL : ℝ} (hs : 0 < s) (h4s : 4 * s ≤ ρ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hc₀ : 0 < c₀) (hD : 0 < D)
    (hE : ∀ c ∈ cells, μ c (E c)ᶜ = 0) (hM : ∀ c ∈ cells, 0 < (μ c).real univ)
    (hG : ∀ c ∈ cells, ∀ k, |G c k| ≤ K)
    (hsrc : ∀ c ∈ cells, ∀ x ∈ E c, (∀ k, |V x k| ≤ K) ∧
      |X' x - rowEval (G c) (V x)| ≤ ε ∧ ⌊X' x / s⌋ ∈ L (vbin s (V x)) ∧ vbin s (V x) ∈ Bv)
    (hLcard : ∀ β, ((L β).card : ℝ) ≤ KL) (hπ0 : ∀ β, 0 ≤ π β)
    (hdom : ∀ c ∈ cells, ∀ β, (μ c).real {x | vbin s (V x) = β} ≤ D * (μ c).real univ * π β)
    (hbroad : ∀ c ∈ cells, Broad (μ c) (fun x => liftE (V x)) ρ c₀) :
    ((cells.image fun c => rowBin s (G c)).card : ℝ) ≤
      (D / c₀) ^ 3 * (KL ^ 3 * (2 * rowRadius K ε s ((ρ / 2) ^ 3) / s + 2) ^ 3) *
        (∑ β ∈ Bv, π β) ^ 3 := by
  classical
  have hρ : 0 < ρ := by linarith
  have hsup : ∀ c ∈ cells, ∃ (Tc : Finset (Fin 3 → Fin 2 → ℤ))
      (wit : (Fin 3 → Fin 2 → ℤ) → Fin 3 → Ω),
      (∀ t ∈ Tc, ∀ i, wit t i ∈ E c ∧ vbin s (V (wit t i)) = t i ∧ t i ∈ Bv) ∧
      (∀ t ∈ Tc, (ρ / 2) ^ 3 ≤ |(witnessMatrix fun i => V (wit t i)).det|) ∧
      c₀ ^ 3 ≤ D ^ 3 * ∑ t ∈ Tc, ∏ i, π (t i) := fun c hc =>
    exists_supported_triples (μ c) (E c) (hE c hc) V hVm Bv (fun x hx => (hsrc c hc x hx).2.2.2)
      π hs h4s hc₀.le hD (hM c hc) (hdom c hc) (hbroad c hc)
  choose! Tc wit hwit hdet hpal using hsup
  have hK₁ : 0 ≤ (D / c₀) ^ 3 := by positivity
  refine coarse_row_bins_card_le_weighted cells G Tc (fun c t i => V (wit c t i))
    (fun c t i => X' (wit c t i)) L π Bv hs (by positivity) hK hε hK₁ hG ?_ ?_ ?_ ?_ ?_ hLcard
    hπ0 ?_ ?_
  · intro c hc t ht i k
    exact (hsrc c hc _ (hwit c hc t ht i).1).1 k
  · intro c hc t ht i
    exact (hwit c hc t ht i).2.1
  · intro c hc t ht i
    exact (hsrc c hc _ (hwit c hc t ht i).1).2.1
  · intro c hc t ht
    exact hdet c hc t ht
  · intro c hc t ht i
    have h := (hsrc c hc _ (hwit c hc t ht i).1).2.2.1
    rwa [(hwit c hc t ht i).2.1] at h
  · intro c hc t ht i
    exact (hwit c hc t ht i).2.2
  · intro c hc
    have h := hpal c hc
    have hc3 : 0 < c₀ ^ 3 := by positivity
    have hD3 : 0 < D ^ 3 := by positivity
    rw [div_pow]
    calc (1 : ℝ) = (D ^ 3 / c₀ ^ 3) * (c₀ ^ 3 / D ^ 3) := by field_simp
      _ ≤ (D ^ 3 / c₀ ^ 3) * ∑ t ∈ Tc c, ∏ i, π (t i) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ hD3]
          linarith [h]

/-- Row bins of rows with components `≤ K` lie in a box: at most `(2K/s + 2)³` of them. -/
theorem card_rowBins_le_of_norm {ι : Type*} [DecidableEq ι] (cells : Finset ι)
    (G : ι → Fin 3 → ℝ) {K s : ℝ} (hs : 0 < s) (hK : 0 ≤ K)
    (hG : ∀ c ∈ cells, ∀ k, |G c k| ≤ K) :
    ((cells.image fun c => rowBin s (G c)).card : ℝ) ≤ (2 * K / s + 2) ^ 3 := by
  classical
  let box : Finset (Fin 3 → ℤ) := Fintype.piFinset fun _ => Full7EntryPruning.binsAround s 0 K
  have hsub : (cells.image fun c => rowBin s (G c)) ⊆ box := by
    intro g hg
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hg
    rw [Fintype.mem_piFinset]
    intro k
    exact Full7EntryPruning.floor_mem_binsAround hs (by simpa using hG c hc k)
  calc ((cells.image fun c => rowBin s (G c)).card : ℝ) ≤ (box.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ∏ _k : Fin 3, ((Full7EntryPruning.binsAround s 0 K).card : ℝ) := by
        simp only [box, Fintype.card_piFinset]
        push_cast
        rfl
    _ ≤ ∏ _k : Fin 3, (2 * K / s + 2) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
          (fun _ _ => Full7EntryPruning.card_binsAround_le hs hK)
    _ = (2 * K / s + 2) ^ 3 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Coarse row lists at every mesh `s > 0`.** No `4s ≤ ρ` premise: fine meshes use the
supported triples of the broad cell laws, coarse meshes (`ρ < 4s`) the direct count from `|G| ≤ K`.
The bound is the sum of the two expressions. -/
theorem coarse_row_bins_card_le_all_meshes {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    [Nonempty Ω] (cells : Finset ι) (μ : ι → Measure Ω) [∀ c, IsFiniteMeasure (μ c)]
    (E : ι → Set Ω) (G : ι → Fin 3 → ℝ) (V : Ω → Fin 2 → ℝ) (hVm : Measurable V) (X' : Ω → ℝ)
    (L : (Fin 2 → ℤ) → Finset ℤ) (π : (Fin 2 → ℤ) → ℝ) (Bv : Finset (Fin 2 → ℤ))
    {K ε s ρ c₀ D KL : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hc₀ : 0 < c₀) (hD : 0 < D)
    (hE : ∀ c ∈ cells, μ c (E c)ᶜ = 0) (hM : ∀ c ∈ cells, 0 < (μ c).real univ)
    (hG : ∀ c ∈ cells, ∀ k, |G c k| ≤ K)
    (hsrc : ∀ c ∈ cells, ∀ x ∈ E c, (∀ k, |V x k| ≤ K) ∧
      |X' x - rowEval (G c) (V x)| ≤ ε ∧ ⌊X' x / s⌋ ∈ L (vbin s (V x)) ∧ vbin s (V x) ∈ Bv)
    (hLcard : ∀ β, ((L β).card : ℝ) ≤ KL) (hπ0 : ∀ β, 0 ≤ π β)
    (hdom : ∀ c ∈ cells, ∀ β, (μ c).real {x | vbin s (V x) = β} ≤ D * (μ c).real univ * π β)
    (hbroad : ∀ c ∈ cells, Broad (μ c) (fun x => liftE (V x)) ρ c₀) :
    ((cells.image fun c => rowBin s (G c)).card : ℝ) ≤
      (D / c₀) ^ 3 * (KL ^ 3 * (2 * rowRadius K ε s ((ρ / 2) ^ 3) / s + 2) ^ 3) *
        (∑ β ∈ Bv, π β) ^ 3 + (8 * K / ρ + 2) ^ 3 := by
  have hKL : 0 ≤ KL := (Nat.cast_nonneg _).trans (hLcard (fun _ => 0))
  have hfine0 : 0 ≤ (D / c₀) ^ 3 * (KL ^ 3 * (2 * rowRadius K ε s ((ρ / 2) ^ 3) / s + 2) ^ 3) *
      (∑ β ∈ Bv, π β) ^ 3 := by
    have hr : 0 ≤ rowRadius K ε s ((ρ / 2) ^ 3) := by unfold rowRadius; positivity
    have hp : 0 ≤ ∑ β ∈ Bv, π β := Finset.sum_nonneg fun β _ => hπ0 β
    positivity
  by_cases h4s : 4 * s ≤ ρ
  · have h := coarse_row_bins_card_le_of_broad cells μ E G V hVm X' L π Bv hs h4s hK hε hc₀ hD
      hE hM hG hsrc hLcard hπ0 hdom hbroad
    have hc : 0 ≤ (8 * K / ρ + 2) ^ 3 := by positivity
    linarith
  · push_neg at h4s
    have h := card_rowBins_le_of_norm cells G hs hK hG
    have hmono : 2 * K / s + 2 ≤ 8 * K / ρ + 2 := by
      have : 2 * K / s ≤ 8 * K / ρ := by
        rw [div_le_div_iff₀ hs hρ]
        nlinarith
      linarith
    have hpow : (2 * K / s + 2) ^ 3 ≤ (8 * K / ρ + 2) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hmono 3
    linarith

/-- **Normalized form.** If `K, KL, D, 1/c₀, 1/ρ, ε/s ≤ A` with `A ≥ 1` and `Σ_{Bv} π ≤ P`, the
coarse row bins number at most `10¹⁰ A²⁷ (P³ + 1)` at every mesh. For `A` a subpower and `P`
bounded (the actual `Σ π ≤ 36`), this is a subpower count, uniform over meshes, with no alphabet
factor. -/
theorem coarse_row_bins_card_le_normalized {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]
    [Nonempty Ω] (cells : Finset ι) (μ : ι → Measure Ω) [∀ c, IsFiniteMeasure (μ c)]
    (E : ι → Set Ω) (G : ι → Fin 3 → ℝ) (V : Ω → Fin 2 → ℝ) (hVm : Measurable V) (X' : Ω → ℝ)
    (L : (Fin 2 → ℤ) → Finset ℤ) (π : (Fin 2 → ℤ) → ℝ) (Bv : Finset (Fin 2 → ℤ))
    {K ε s ρ c₀ D KL A P : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hc₀ : 0 < c₀) (hD : 0 < D) (hA : 1 ≤ A) (hKA : K ≤ A) (hKLA : KL ≤ A) (hDA : D ≤ A)
    (hcA : c₀⁻¹ ≤ A) (hρA : ρ⁻¹ ≤ A) (hεA : ε / s ≤ A)
    (hE : ∀ c ∈ cells, μ c (E c)ᶜ = 0) (hM : ∀ c ∈ cells, 0 < (μ c).real univ)
    (hG : ∀ c ∈ cells, ∀ k, |G c k| ≤ K)
    (hsrc : ∀ c ∈ cells, ∀ x ∈ E c, (∀ k, |V x k| ≤ K) ∧
      |X' x - rowEval (G c) (V x)| ≤ ε ∧ ⌊X' x / s⌋ ∈ L (vbin s (V x)) ∧ vbin s (V x) ∈ Bv)
    (hLcard : ∀ β, ((L β).card : ℝ) ≤ KL) (hπ0 : ∀ β, 0 ≤ π β) (hP : ∑ β ∈ Bv, π β ≤ P)
    (hdom : ∀ c ∈ cells, ∀ β, (μ c).real {x | vbin s (V x) = β} ≤ D * (μ c).real univ * π β)
    (hbroad : ∀ c ∈ cells, Broad (μ c) (fun x => liftE (V x)) ρ c₀) :
    ((cells.image fun c => rowBin s (G c)).card : ℝ) ≤ 10 ^ 10 * A ^ 27 * (P ^ 3 + 1) := by
  have h := coarse_row_bins_card_le_all_meshes cells μ E G V hVm X' L π Bv hs hρ hK hε hc₀ hD hE
    hM hG hsrc hLcard hπ0 hdom hbroad
  have hKL : 0 ≤ KL := (Nat.cast_nonneg _).trans (hLcard (fun _ => 0))
  have hA0 : 0 < A := by linarith
  have hS0 : 0 ≤ ∑ β ∈ Bv, π β := Finset.sum_nonneg fun β _ => hπ0 β
  have hP0 : 0 ≤ P := hS0.trans hP
  -- the pieces
  have hDc : D / c₀ ≤ A ^ 2 := by
    rw [div_eq_mul_inv, sq]
    exact mul_le_mul hDA hcA (inv_nonneg.mpr hc₀.le) hA0.le
  have hρ3 : ((ρ / 2) ^ 3)⁻¹ ≤ 8 * A ^ 3 := by
    rw [div_pow, inv_div, show (2 : ℝ) ^ 3 = 8 by norm_num, div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hρ.le) hρA 3) (by norm_num)
  have hrow : 2 * rowRadius K ε s ((ρ / 2) ^ 3) / s + 2 ≤ 2000 * A ^ 6 := by
    unfold rowRadius
    have e1 : 2 * (6 * (1 + K) ^ 2 * (2 * ε + s + 2 * K * s) / (ρ / 2) ^ 3) / s =
        12 * (1 + K) ^ 2 * (2 * (ε / s) + 1 + 2 * K) * ((ρ / 2) ^ 3)⁻¹ := by
      field_simp
      norm_num
    rw [e1]
    have hK1 : (1 + K) ^ 2 ≤ 4 * A ^ 2 := by nlinarith
    have hlin : 2 * (ε / s) + 1 + 2 * K ≤ 5 * A := by nlinarith
    have hlin0 : 0 ≤ 2 * (ε / s) + 1 + 2 * K := by
      have : 0 ≤ ε / s := div_nonneg hε hs.le
      linarith
    have hA6 : A ≤ A ^ 6 := by
      calc A = A ^ 1 := (pow_one A).symm
        _ ≤ A ^ 6 := pow_le_pow_right₀ hA (by norm_num)
    calc 12 * (1 + K) ^ 2 * (2 * (ε / s) + 1 + 2 * K) * ((ρ / 2) ^ 3)⁻¹ + 2
        ≤ 12 * (4 * A ^ 2) * (5 * A) * (8 * A ^ 3) + 2 := by
          gcongr
      _ = 1920 * A ^ 6 + 2 := by ring
      _ ≤ 2000 * A ^ 6 := by nlinarith [one_le_pow₀ hA (n := 6)]
  have hfine : (D / c₀) ^ 3 * (KL ^ 3 * (2 * rowRadius K ε s ((ρ / 2) ^ 3) / s + 2) ^ 3) *
      (∑ β ∈ Bv, π β) ^ 3 ≤ (A ^ 2) ^ 3 * (A ^ 3 * (2000 * A ^ 6) ^ 3) * P ^ 3 := by
    have hrow0 : 0 ≤ 2 * rowRadius K ε s ((ρ / 2) ^ 3) / s + 2 := by
      have : 0 ≤ rowRadius K ε s ((ρ / 2) ^ 3) := by unfold rowRadius; positivity
      positivity
    gcongr
  have hcoarse : (8 * K / ρ + 2) ^ 3 ≤ (10 * A ^ 2) ^ 3 := by
    have : 8 * K / ρ + 2 ≤ 10 * A ^ 2 := by
      have h1 : 8 * K / ρ ≤ 8 * A ^ 2 := by
        rw [div_eq_mul_inv, sq]
        nlinarith [inv_nonneg.mpr hρ.le]
      nlinarith
    exact pow_le_pow_left₀ (by positivity) this 3
  have hA27 : A ^ 6 ≤ A ^ 27 := pow_le_pow_right₀ hA (by norm_num)
  calc ((cells.image fun c => rowBin s (G c)).card : ℝ)
      ≤ (A ^ 2) ^ 3 * (A ^ 3 * (2000 * A ^ 6) ^ 3) * P ^ 3 + (10 * A ^ 2) ^ 3 := by
        linarith
    _ = 8000000000 * A ^ 27 * P ^ 3 + 1000 * A ^ 6 := by ring
    _ ≤ 10 ^ 10 * A ^ 27 * (P ^ 3 + 1) := by
        have hP3 : 0 ≤ P ^ 3 := pow_nonneg hP0 3
        have hA27' : 0 ≤ A ^ 27 := by positivity
        nlinarith

end SupportedTriples

end

end Submission.Lib.K4ThreeBaseRows
