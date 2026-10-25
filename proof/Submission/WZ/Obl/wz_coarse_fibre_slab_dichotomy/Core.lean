-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy.Core.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_coarse_fibre_slab_dichotomy.CellsReal
import Submission.WZ.Obl.wz_coarse_fibre_slab_dichotomy.Geometry

/-!
# The per-scale fibre dichotomy

One greedy slab extraction per coarse fibre. Cells whose slab has half-width at least `lam`
("thick") satisfy the below-slab Frostman count relative to the doubled coarse tube; if they carry
mass at least `M` we return them. Otherwise the cells with thin slabs carry almost all of the
mass, are non-interacting inside each fibre, and lie in slabs of half-width `< lam`.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells

local notation "Sp" => LeanEval.Analysis.WangZahlKakeya.Space

/-- A default slab (only used outside the range of genuine cells). -/
noncomputable def defaultSlab : SlabSpec :=
  ⟨EuclideanSpace.single 0 1, 0, 1, by simp, one_pos⟩

/-- The empty cell. -/
def emptyCell (n : ℕ) : ShadedCell (Fin n) := ⟨∅, ∅, fun _ => ∅⟩

/-- The scalar inequality behind the below-slab count. -/
lemma real_count_bound {A B r ρ lam θ l : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hr : 0 < r)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hθ : 0 < θ) (hAc : A ≤ 3072 * (r / lam) * (B / θ))
    (hAB : A ≤ B) (hl1 : 384 ≤ l) (hl2 : 589824 * ρ / (lam * θ) ≤ l) :
    A * (96 * ρ ^ 2) ≤ l * B * (ρ * min r (ρ / 2) / 2) := by
  rcases le_total r (ρ / 2) with hrρ | hrρ
  · rw [min_eq_left hrρ]
    have h5 : A * (96 * ρ ^ 2) ≤ 3072 * (r / lam) * (B / θ) * (96 * ρ ^ 2) := by gcongr
    have h6 : 3072 * (r / lam) * (B / θ) * (96 * ρ ^ 2) =
        (589824 * ρ / (lam * θ)) * B * (ρ * r / 2) := by
      field_simp; ring
    have h7 : (589824 * ρ / (lam * θ)) * B * (ρ * r / 2) ≤ l * B * (ρ * r / 2) := by gcongr
    linarith
  · rw [min_eq_right hrρ]
    have h5 : A * (96 * ρ ^ 2) ≤ B * (96 * ρ ^ 2) := by gcongr
    have h6 : B * (96 * ρ ^ 2) = 384 * B * (ρ * (ρ / 2) / 2) := by ring
    have h7 : 384 * B * (ρ * (ρ / 2) / 2) ≤ l * B * (ρ * (ρ / 2) / 2) := by gcongr
    linarith

open Classical in
set_option maxHeartbeats 800000 in
theorem core_dichotomy
    {δ ρ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {n : ℕ} (x v : Fin n → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Sp) 1)
    (S : Finset (Fin n)) (Z : Fin n → Set Sp) (hZm : ∀ i, MeasurableSet (Z i))
    (hZT : ∀ i, Z i ⊆ thickening δ (segment ℝ (x i) (x i + v i)))
    {N : ℕ} (y w : Fin N → Sp) (hw : ∀ k, ‖w k‖ = 1) (f : Fin n → Fin N)
    (hcov : ∀ i ∈ S, thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      thickening ρ (segment ℝ (y (f i)) (y (f i) + w (f i))))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (K : ℕ) (hK : (1536 * n : ℝ) ≤ 2 ^ K)
    {lam : ℝ} (hlam : 0 < lam) {M : ℝ} (hM : 0 ≤ M) :
    (∃ S' : Finset (Fin n), S' ⊆ S ∧ M ≤ ∑ i ∈ S', (volume (Z i)).toReal ∧
      ∀ (k : Fin N) (u : Sp) (t r : ℝ), ‖u‖ = 1 → 0 < r →
        ENNReal.ofReal ((S'.filter (fun i => f i = k ∧
            thickening δ (segment ℝ (x i) (x i + v i)) ⊆
              doubled ρ (y k) (w k) ∩ slabQ u t r)).card : ℝ) *
          volume (doubled ρ (y k) (w k)) ≤
        ENNReal.ofReal (max 384 (589824 * ρ / (lam * θ)) *
            ((S'.filter (fun i => f i = k)).card : ℝ)) *
          volume (doubled ρ (y k) (w k) ∩ slabQ u t r)) ∨
    (∃ (S'' : Finset (Fin n)) (Z'' : Fin n → Set Sp) (u : Fin n → Sp) (t r : Fin n → ℝ),
      S'' ⊆ S ∧ (∀ i, MeasurableSet (Z'' i) ∧ Z'' i ⊆ Z i ∧ (i ∉ S'' → Z'' i = ∅)) ∧
      ∑ i ∈ S, (volume (Z i)).toReal ≤ 3072 * θ * n * δ ^ 2 +
        2 * (1 + 320 * K) / θ ^ 2 * (∑ i ∈ S'', (volume (Z'' i)).toReal + 2 * M) ∧
      (∀ i ∈ S'', ‖u i‖ = 1 ∧ 0 < r i ∧ r i < lam ∧
        thickening δ (segment ℝ (x i) (x i + v i)) ⊆ slabQ (u i) (t i) (r i)) ∧
      (∀ i ∈ S'', ∀ i' ∈ S'', f i = f i' → (Z'' i ∩ Z'' i').Nonempty →
        thickening δ (segment ℝ (x i') (x i' + v i')) ⊆ slabQ (u i) (t i) (r i))) := by
  set U : Fin n → Set Sp := fun i => tubeU δ (x i) (v i) with hUdef
  have hU0 : ∀ i, volume (U i) ≠ 0 := fun i => volume_tubeU_ne_zero hδ (x i) (hv i)
  have hUt : ∀ i, volume (U i) ≠ ⊤ := fun i => volume_tubeU_ne_top (hT i)
  have hZU : ∀ i, Z i ⊆ U i := fun i => (hZT i).trans (subset_tubeU δ (x i) (v i))
  have hZt : ∀ i, volume (Z i) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top (hUt i) (measure_mono (hZU i))
  set Sd := S.filter (fun i => ENNReal.ofReal (2 * θ) * volume (U i) ≤ volume (Z i)) with hSd
  set Fk : Fin N → Finset (Fin n) := fun k => Sd.filter (fun i => f i = k) with hFk
  have hdenseθ : ∀ k, ∀ i ∈ Fk k, ENNReal.ofReal θ * volume (U i) ≤ volume (Z i) := by
    intro k i hi
    have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    exact le_trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _) h2
  have hext := fun k => fibre_extraction hδ hδ1 x v hv hT K hK (Fk k) Z (fun i _ => hZm i)
    (fun i _ => hZU i) (ENNReal.ofReal θ) (hdenseθ k)
  choose m C hCv hCd hCmass using hext
  have hsl := fun k j => count_of_slabFamilyGood hδ hδ1 x v hv hT (hCv k j).2.2.1
  choose sl hslreg hslw hslcnt using hsl
  -- membership facts
  have hidx : ∀ k j i, i ∈ (C k j).indices → i ∈ Sd ∧ f i = k := fun k j i hi =>
    Finset.mem_filter.mp ((hCv k j).2.1 hi)
  have hidxS : ∀ k j i, i ∈ (C k j).indices → i ∈ S := fun k j i hi =>
    (Finset.mem_filter.mp (hidx k j i hi).1).1
  set Jt : (k : Fin N) → Finset (Fin (m k)) :=
    fun k => Finset.univ.filter (fun j => lam ≤ (sl k j).width) with hJt
  set Jn : (k : Fin N) → Finset (Fin (m k)) :=
    fun k => Finset.univ.filter (fun j => ¬ lam ≤ (sl k j).width) with hJn
  set Bt : Fin N → Finset (Fin n) := fun k => (Jt k).biUnion (fun j => (C k j).indices) with hBt
  set Bn : Fin N → Finset (Fin n) := fun k => (Jn k).biUnion (fun j => (C k j).indices) with hBn
  set S' := Finset.univ.biUnion Bt with hS'
  set Tn := Finset.univ.biUnion Bn with hTn
  have hBtf : ∀ k i, i ∈ Bt k → f i = k := by
    intro k i hi
    obtain ⟨j, _, hij⟩ := Finset.mem_biUnion.mp hi
    exact (hidx k j i hij).2
  have hBnf : ∀ k i, i ∈ Bn k → f i = k := by
    intro k i hi
    obtain ⟨j, _, hij⟩ := Finset.mem_biUnion.mp hi
    exact (hidx k j i hij).2
  have hS'k : ∀ k, S'.filter (fun i => f i = k) = Bt k := by
    intro k
    ext i
    simp only [hS', Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨k', hk'⟩, hfi⟩
      have := hBtf k' i hk'
      rw [← hfi, this]
      exact hk'
    · intro hi
      exact ⟨⟨k, hi⟩, hBtf k i hi⟩
  have hS'Sd : S' ⊆ Sd := by
    intro i hi
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨j, _, hij⟩ := Finset.mem_biUnion.mp hk
    exact (hidx k j i hij).1
  have hSdS : Sd ⊆ S := Finset.filter_subset _ _
  have hS'S : S' ⊆ S := hS'Sd.trans hSdS
  have hTnSd : Tn ⊆ Sd := by
    intro i hi
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨j, _, hij⟩ := Finset.mem_biUnion.mp hk
    exact (hidx k j i hij).1
  by_cases hM' : M ≤ ∑ i ∈ S', (volume (Z i)).toReal
  · left
    refine ⟨S', hS'S, hM', ?_⟩
    intro k u t r hu hr
    set A := S'.filter (fun i => f i = k ∧ thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      doubled ρ (y k) (w k) ∩ slabQ u t r) with hA
    rw [hS'k k]
    rcases A.eq_empty_or_nonempty with hA0 | ⟨i₀, hi₀⟩
    · rw [hA0]; simp
    have hi₀' := Finset.mem_filter.mp hi₀
    have hi₀S : i₀ ∈ S := hS'S hi₀'.1
    have hcov₀ := hcov i₀ hi₀S
    rw [hi₀'.2.1] at hcov₀
    have hWsub := thickening_subset_doubled hδ hcov₀
    have hseg : segment ℝ (x i₀) (x i₀ + v i₀) ⊆ slabQ u t r :=
      (self_subset_thickening hδ _).trans (hi₀'.2.2.trans inter_subset_right)
    have hlow := volume_inter_slab_ge hρ hr (hv i₀) hu.le hWsub hseg
    have hup := volume_doubled_le hρ hρ1 (y k) (hw k)
    -- counting
    have hAsub : A ⊆ (Jt k).biUnion (fun j => (C k j).indices.filter
        (fun i => U i ⊆ slabQ u t r)) := by
      intro i hi
      have hi' := Finset.mem_filter.mp hi
      have hiB : i ∈ Bt k := by rw [← hS'k k]; exact Finset.mem_filter.mpr ⟨hi'.1, hi'.2.1⟩
      obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hiB
      refine Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hij, ?_⟩⟩
      exact (tubeU_subset_iff (isClosed_slabQ u t r)).mpr (hi'.2.2.trans inter_subset_right)
    have hcnt1 : (A.card : ℝ) ≤ ∑ j ∈ Jt k,
        (((C k j).indices.filter (fun i => U i ⊆ slabQ u t r)).card : ℝ) := by
      have := Finset.card_le_card hAsub
      have h2 := Finset.card_biUnion_le (s := Jt k)
        (t := fun j => (C k j).indices.filter (fun i => U i ⊆ slabQ u t r))
      exact_mod_cast this.trans h2
    have hcnt2 : ∑ j ∈ Jt k, (((C k j).indices.filter (fun i => U i ⊆ slabQ u t r)).card : ℝ) ≤
        3072 * (r / lam) * ∑ j ∈ Jt k, ((C k j).indices.card : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hwj : lam ≤ (sl k j).width := (Finset.mem_filter.mp hj).2
      have h1 := hslcnt k j u t r hu hr
      have h2 : r / (sl k j).width ≤ r / lam := div_le_div_of_nonneg_left hr.le hlam hwj
      calc _ ≤ 3072 * (r / (sl k j).width) * ((C k j).indices.card : ℝ) := h1
        _ ≤ 3072 * (r / lam) * ((C k j).indices.card : ℝ) := by gcongr
    have hcnt3 : θ * ∑ j ∈ Jt k, ((C k j).indices.card : ℝ) ≤ ((Bt k).card : ℝ) :=
      cells_card_real hθ.le (hCv k) (hCd k) (fun i _ => hZU i) hU0 hUt (Jt k)
    have hAcard : (A.card : ℝ) ≤ 3072 * (r / lam) * (((Bt k).card : ℝ) / θ) := by
      have h4 : ∑ j ∈ Jt k, ((C k j).indices.card : ℝ) ≤ ((Bt k).card : ℝ) / θ := by
        rw [le_div_iff₀ hθ]; linarith
      calc (A.card : ℝ) ≤ _ := hcnt1
        _ ≤ _ := hcnt2
        _ ≤ 3072 * (r / lam) * (((Bt k).card : ℝ) / θ) := by gcongr
    have hAB : (A.card : ℝ) ≤ ((Bt k).card : ℝ) := by
      have : A ⊆ Bt k := by
        intro i hi
        have hi' := Finset.mem_filter.mp hi
        rw [← hS'k k]; exact Finset.mem_filter.mpr ⟨hi'.1, hi'.2.1⟩
      exact_mod_cast Finset.card_le_card this
    set l := max 384 (589824 * ρ / (lam * θ)) with hl
    have hl1 : 384 ≤ l := le_max_left _ _
    have hl2 : 589824 * ρ / (lam * θ) ≤ l := le_max_right _ _
    have hBk0 : (0 : ℝ) ≤ (Bt k).card := Nat.cast_nonneg _
    have hreal : (A.card : ℝ) * (96 * ρ ^ 2) ≤
        l * ((Bt k).card : ℝ) * (ρ * min r (ρ / 2) / 2) :=
      real_count_bound (Nat.cast_nonneg _) hBk0 hr hρ hlam hθ hAcard hAB hl1 hl2
    calc ENNReal.ofReal (A.card : ℝ) * volume (doubled ρ (y k) (w k))
        ≤ ENNReal.ofReal (A.card : ℝ) * ENNReal.ofReal (96 * ρ ^ 2) := by gcongr
      _ = ENNReal.ofReal ((A.card : ℝ) * (96 * ρ ^ 2)) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal (l * ((Bt k).card : ℝ) * (ρ * min r (ρ / 2) / 2)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (l * ((Bt k).card : ℝ)) * ENNReal.ofReal (ρ * min r (ρ / 2) / 2) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (l * ((Bt k).card : ℝ)) * volume (doubled ρ (y k) (w k) ∩ slabQ u t r) := by
          gcongr
  · right
    push Not at hM'
    set Ck : Fin N → ℕ → ShadedCell (Fin n) :=
      fun k j => if h : j < m k then C k ⟨j, h⟩ else emptyCell n with hCk
    set slk : Fin N → ℕ → SlabSpec :=
      fun k j => if h : j < m k then sl k ⟨j, h⟩ else defaultSlab with hslk
    have hCk_eq : ∀ k j (h : j < m k), Ck k j = C k ⟨j, h⟩ := fun k j h => by
      simp only [hCk, dif_pos h]
    have hslk_eq : ∀ k j (h : j < m k), slk k j = sl k ⟨j, h⟩ := fun k j h => by
      simp only [hslk, dif_pos h]
    set good : Fin n → ℕ → Prop := fun i j => j < m (f i) ∧ ¬ lam ≤ (slk (f i) j).width ∧
      i ∈ (Ck (f i) j).indices with hgood
    set S'' := Tn \ S' with hS''
    have hgoodex : ∀ i ∈ S'', ∃ j, good i j := by
      intro i hi
      have hiT := (Finset.mem_sdiff.mp hi).1
      obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hiT
      obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hk
      have hfi : f i = k := (hidx k j i hij).2
      refine ⟨j.val, ?_, ?_, ?_⟩
      · rw [hfi]; exact j.isLt
      · rw [hfi, hslk_eq k j.val j.isLt]; exact (Finset.mem_filter.mp hj).2
      · rw [hfi, hCk_eq k j.val j.isLt]; exact hij
    set g : Fin n → ℕ := fun i => if h : ∃ j, good i j then Nat.find h else 0 with hgdef
    have hg : ∀ i ∈ S'', good i (g i) := by
      intro i hi
      have h := hgoodex i hi
      simp only [hgdef, dif_pos h]
      exact Nat.find_spec h
    set Z'' : Fin n → Set Sp := fun i => if i ∈ S'' then (Ck (f i) (g i)).shading i else ∅
      with hZ''
    -- validity of the chosen cell
    have hval : ∀ i ∈ S'', (Ck (f i) (g i)).Valid (Fk (f i)) U Z (ENNReal.ofReal θ)
        (SlabFamilyGood U) ∧ (Ck (f i) (g i)).region = (slk (f i) (g i)).carrier := by
      intro i hi
      obtain ⟨h, -, -⟩ := hg i hi
      rw [hCk_eq _ _ h, hslk_eq _ _ h]
      exact ⟨hCv _ _, hslreg _ _⟩
    have hZ''i : ∀ i ∈ S'', Z'' i = (Ck (f i) (g i)).shading i := fun i hi => by
      simp only [hZ'', if_pos hi]
    refine ⟨S'', Z'', fun i => (slk (f i) (g i)).normal, fun i => (slk (f i) (g i)).offset,
      fun i => (slk (f i) (g i)).width, ?_, ?_, ?_, ?_, ?_⟩
    · exact (Finset.sdiff_subset).trans (hTnSd.trans hSdS)
    · intro i
      by_cases hi : i ∈ S''
      · rw [hZ''i i hi]
        obtain ⟨-, -, hmem⟩ := hg i hi
        exact ⟨(hval i hi).1.2.2.2.2.1 i hmem, (hval i hi).1.2.2.2.2.2.1 i hmem,
          fun h => absurd hi h⟩
      · have h0 : Z'' i = ∅ := by simp only [hZ'', hi, if_false]
        rw [h0]
        exact ⟨MeasurableSet.empty, empty_subset _, fun _ => rfl⟩
    · -- mass accounting, in real numbers
      have hzr0 : ∀ i, 0 ≤ (volume (Z i)).toReal := fun i => ENNReal.toReal_nonneg
      have hur0 : ∀ i, 0 ≤ (volume (U i)).toReal := fun i => ENNReal.toReal_nonneg
      have hzu : ∀ i, (volume (Z i)).toReal ≤ (volume (U i)).toReal :=
        fun i => ENNReal.toReal_mono (hUt i) (measure_mono (hZU i))
      have hdense2 : ∀ i ∈ Sd, 2 * θ * (volume (U i)).toReal ≤ (volume (Z i)).toReal := by
        intro i hi
        have := ENNReal.toReal_mono (hZt i) (Finset.mem_filter.mp hi).2
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
      -- (R1) the non-dense tubes
      have hR1 : ∑ i ∈ S, (volume (Z i)).toReal ≤
          ∑ i ∈ Sd, (volume (Z i)).toReal + 3072 * θ * n * δ ^ 2 := by
        rw [← Finset.sum_filter_add_sum_filter_not S
          (fun i => ENNReal.ofReal (2 * θ) * volume (U i) ≤ volume (Z i))]
        have hnd : ∀ i ∈ S.filter (fun i => ¬ (ENNReal.ofReal (2 * θ) * volume (U i) ≤
            volume (Z i))), (volume (Z i)).toReal ≤ 3072 * θ * δ ^ 2 := by
          intro i hi
          have hlt := not_le.mp (Finset.mem_filter.mp hi).2
          have hb : volume (Z i) ≤ ENNReal.ofReal (3072 * θ * δ ^ 2) := by
            calc volume (Z i) ≤ ENNReal.ofReal (2 * θ) * volume (U i) := hlt.le
              _ ≤ ENNReal.ofReal (2 * θ) * ENNReal.ofReal (1536 * δ ^ 2) := by
                  gcongr; exact volume_tubeU_le hδ hδ1 (x i) (hv i)
              _ = ENNReal.ofReal (3072 * θ * δ ^ 2) := by
                  rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) hb
        have hcard : ((S.filter (fun i => ¬ (ENNReal.ofReal (2 * θ) * volume (U i) ≤
            volume (Z i)))).card : ℝ) ≤ n := by
          exact_mod_cast (Finset.card_le_univ _).trans (by simp)
        have h2 : ∑ i ∈ S.filter (fun i => ¬ (ENNReal.ofReal (2 * θ) * volume (U i) ≤
            volume (Z i))), (volume (Z i)).toReal ≤ 3072 * θ * n * δ ^ 2 := by
          calc _ ≤ ∑ i ∈ S.filter (fun i => ¬ (ENNReal.ofReal (2 * θ) * volume (U i) ≤
                volume (Z i))), 3072 * θ * δ ^ 2 := Finset.sum_le_sum hnd
            _ = ((S.filter (fun i => ¬ (ENNReal.ofReal (2 * θ) * volume (U i) ≤
                volume (Z i)))).card : ℝ) * (3072 * θ * δ ^ 2) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (n : ℝ) * (3072 * θ * δ ^ 2) := by gcongr
            _ = 3072 * θ * n * δ ^ 2 := by ring
        linarith
      -- (R2,R3,R4) per-fibre greedy accounting
      set th : Fin N → ℝ := fun k => ∑ j ∈ Jt k, ∑ i ∈ (C k j).indices, (volume (U i)).toReal
        with hth
      set tn : Fin N → ℝ := fun k => ∑ j ∈ Jn k, ∑ i ∈ (C k j).indices, (volume (U i)).toReal
        with htn
      have hR3 : ∀ k, ∑ i ∈ Fk k, (volume (Z i)).toReal ≤ 2 * (1 + 320 * K) * (th k + tn k) := by
        intro k
        have h := fibre_mass_real (C := C k) (F := Fk k) (U := U) (Y := Z) hθ.le (by positivity)
          hUt hZU (fun i hi => (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2) (hCmass k)
        have hsplit : ∑ j, ∑ i ∈ (C k j).indices, (volume (U i)).toReal = th k + tn k := by
          simp only [hth, htn, hJt, hJn]
          exact (Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun j => lam ≤ (sl k j).width) _).symm
        rw [hsplit] at h
        exact h
      have hR2 : ∑ i ∈ Sd, (volume (Z i)).toReal = ∑ k, ∑ i ∈ Fk k, (volume (Z i)).toReal :=
        (Finset.sum_fiberwise Sd f (fun i => (volume (Z i)).toReal)).symm
      -- (R5) thick cells
      have hdisjBt : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint Bt := by
        intro k _ k' _ hkk'
        rw [Function.onFun, Finset.disjoint_left]
        intro i hi hi'
        exact hkk' ((hBtf k i hi).symm.trans (hBtf k' i hi'))
      have hdisjBn : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint Bn := by
        intro k _ k' _ hkk'
        rw [Function.onFun, Finset.disjoint_left]
        intro i hi hi'
        exact hkk' ((hBnf k i hi).symm.trans (hBnf k' i hi'))
      have hR5 : θ * ∑ k, th k ≤ ∑ i ∈ S', (volume (Z i)).toReal := by
        rw [hS', Finset.sum_biUnion hdisjBt, Finset.mul_sum]
        exact Finset.sum_le_sum (fun k _ =>
          cells_mass_real hθ.le (hCv k) (hCd k) hUt hZU (Jt k))
      -- (R6) thin cells
      have hR6 : θ * ∑ k, tn k ≤ ∑ i ∈ Tn, (volume (U i)).toReal := by
        rw [hTn, Finset.sum_biUnion hdisjBn, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k _
        exact (cells_mass_real hθ.le (hCv k) (hCd k) hUt hZU (Jn k)).trans
          (Finset.sum_le_sum (fun i _ => hzu i))
      -- (R7) the thin indices lie in `S'' ∪ S'`
      have hR7 : ∑ i ∈ Tn, (volume (U i)).toReal ≤
          ∑ i ∈ S'', (volume (U i)).toReal + ∑ i ∈ S', (volume (U i)).toReal := by
        have hsub : Tn ⊆ S'' ∪ S' := by
          intro i hi
          by_cases h : i ∈ S'
          · exact Finset.mem_union_right _ h
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, h⟩)
        rw [← Finset.sum_union Finset.sdiff_disjoint]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hur0 i)
      -- (R8) the thick indices are dense
      have hR8 : 2 * θ * ∑ i ∈ S', (volume (U i)).toReal ≤ ∑ i ∈ S', (volume (Z i)).toReal := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i hi => hdense2 i (hS'Sd hi))
      -- (R9) the chosen cells keep a `θ` share of each tube
      have hR9 : θ * ∑ i ∈ S'', (volume (U i)).toReal ≤ ∑ i ∈ S'', (volume (Z'' i)).toReal := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨-, -, hmem⟩ := hg i hi
        have h1 := (hval i hi).1.2.2.2.2.2.2 i hmem
        rw [← hZ''i i hi] at h1
        have hZ''t : volume (Z'' i) ≠ ⊤ := by
          rw [hZ''i i hi]
          exact ne_top_of_le_ne_top (hZt i) (measure_mono ((hval i hi).1.2.2.2.2.2.1 i hmem))
        have := ENNReal.toReal_mono hZ''t h1
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le] at this
      -- combine
      set X := ∑ k, th k with hX
      set Yt := ∑ k, tn k with hYt
      set P := ∑ i ∈ S'', (volume (Z'' i)).toReal with hP
      set A' := ∑ i ∈ S', (volume (Z i)).toReal with hA'
      have hA'0 : 0 ≤ A' := Finset.sum_nonneg (fun i _ => hzr0 i)
      have hsum3 : ∑ i ∈ S, (volume (Z i)).toReal ≤ 3072 * θ * n * δ ^ 2 +
          2 * (1 + 320 * K) * (X + Yt) := by
        have h1 : ∑ k, ∑ i ∈ Fk k, (volume (Z i)).toReal ≤
            ∑ k, 2 * (1 + 320 * K) * (th k + tn k) := Finset.sum_le_sum (fun k _ => hR3 k)
        rw [← Finset.mul_sum, Finset.sum_add_distrib] at h1
        linarith
      have hU''0 : 0 ≤ ∑ i ∈ S'', (volume (U i)).toReal := Finset.sum_nonneg (fun i _ => hur0 i)
      have hU'0 : 0 ≤ ∑ i ∈ S', (volume (U i)).toReal := Finset.sum_nonneg (fun i _ => hur0 i)
      have hkey : θ ^ 2 * (X + Yt) ≤ P + 2 * M := by
        have e1 : θ ^ 2 * X ≤ A' := by
          have : θ * X ≤ A' := hR5
          have hX0 : 0 ≤ X := Finset.sum_nonneg (fun k _ => Finset.sum_nonneg
            (fun j _ => Finset.sum_nonneg (fun i _ => hur0 i)))
          nlinarith
        have e2 : θ ^ 2 * Yt ≤ P + A' / 2 := by
          have h1 : θ * Yt ≤ ∑ i ∈ S'', (volume (U i)).toReal + ∑ i ∈ S', (volume (U i)).toReal :=
            hR6.trans hR7
          have h2 : θ * (θ * Yt) ≤ θ * (∑ i ∈ S'', (volume (U i)).toReal +
              ∑ i ∈ S', (volume (U i)).toReal) := mul_le_mul_of_nonneg_left h1 hθ.le
          nlinarith
        nlinarith
      have hθ2 : 0 < θ ^ 2 := by positivity
      have hfinal : 2 * (1 + 320 * K) * (X + Yt) ≤ 2 * (1 + 320 * K) / θ ^ 2 * (P + 2 * M) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hθ2]
        have hLpos : (0 : ℝ) ≤ 2 * (1 + 320 * K) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hkey hLpos]
      linarith
    · intro i hi
      obtain ⟨h, hthin, hmem⟩ := hg i hi
      refine ⟨(slk (f i) (g i)).unit_normal, (slk (f i) (g i)).width_pos,
        lt_of_not_ge hthin, ?_⟩
      have hU := (hval i hi).1.2.2.2.1 i hmem
      rw [(hval i hi).2, slabSpec_carrier_eq] at hU
      exact (subset_tubeU δ (x i) (v i)).trans hU
    · intro i hi i' hi' hff hne
      obtain ⟨h, hthin, hmem⟩ := hg i hi
      obtain ⟨h', hthin', hmem'⟩ := hg i' hi'
      obtain ⟨p, hp, hp'⟩ := hne
      rw [hZ''i i hi] at hp
      rw [hZ''i i' hi'] at hp'
      rw [← hff] at h' hmem' hp'
      have hgg : g i = g i' := by
        by_contra hne'
        have hd : Disjoint (C (f i) ⟨g i, h⟩).support (C (f i) ⟨g i', h'⟩).support :=
          hCd (f i) (fun heq => hne' (by simpa using congrArg Fin.val heq))
        rw [← hCk_eq _ _ h, ← hCk_eq _ _ h'] at hd
        exact Set.disjoint_left.mp hd (shading_subset_support hmem hp)
          (shading_subset_support hmem' hp')
      rw [← hgg] at hmem'
      have hU := (hval i hi).1.2.2.2.1 i' hmem'
      rw [(hval i hi).2, slabSpec_carrier_eq] at hU
      exact (subset_tubeU δ (x i') (v i')).trans hU

end WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy
