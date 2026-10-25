-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Assemble.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.CellFit
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.LocalGridLinearity

/-!
# All cells: the local grid linearity mass bound for one refined family

The good cells of height `√ρ` (inside `[-1, 1]` with a margin, away from height `0`) carry all
but a quarter of the mass (the rest lies in three short intervals and in the partial rows at the
ends of the cells, bounded by the vertical height density `D`). Light cells carry at most
`3/20` of the mass, so heavy cells carry half of it, and on them the fits retain the share
`s ^ εl √s / (12 √ρ)`.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal

section

variable {σ δ s θ K N : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
  {Eo : Set Space} {f : ℝ → ℝ} {P : Space → Space}

lemma heightMass_union_le {n : ℕ} (Y : Fin n → Set Space) (A B : Set ℝ) :
    heightMass Y (A ∪ B) ≤ heightMass Y A + heightMass Y B := by
  unfold heightMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [preimage_union, inter_union_distrib_left]
  exact measure_union_le _ _

lemma heightMass_biUnion_le {n : ℕ} (Y : Fin n → Set Space) {ι : Type*} (T : Finset ι)
    (A : ι → Set ℝ) : heightMass Y (⋃ j ∈ T, A j) ≤ ∑ j ∈ T, heightMass Y (A j) := by
  unfold heightMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [preimage_iUnion₂, inter_iUnion₂]
  exact measure_biUnion_finset_le _ _

/-- The good cells. -/
noncomputable def goodCells (rt : ℝ) : Finset ℤ := by
  classical
  exact (Finset.Icc ⌈-1 / rt⌉ ⌊1 / rt⌋).filter
    (fun j => -1 ≤ (j : ℝ) * rt ∧ ((j : ℝ) + 2) * rt ≤ 1 ∧ (3 ≤ j ∨ j ≤ -4))

lemma mem_goodCells {rt : ℝ} {j : ℤ} (hj : j ∈ goodCells rt) :
    -1 ≤ (j : ℝ) * rt ∧ ((j : ℝ) + 2) * rt ≤ 1 ∧ (3 ≤ j ∨ j ≤ -4) := by
  classical
  unfold goodCells at hj
  exact (Finset.mem_filter.mp hj).2

lemma card_goodCells_le {rt : ℝ} (hrt : 0 < rt) (hrt1 : rt ≤ 1) :
    ((goodCells rt).card : ℝ) ≤ 3 / rt := by
  classical
  have h1 : (goodCells rt).card ≤ (Finset.Icc ⌈-1 / rt⌉ ⌊1 / rt⌋).card := by
    unfold goodCells; exact Finset.card_filter_le _ _
  rw [Int.card_Icc] at h1
  have h2 : ((⌊1 / rt⌋ + 1 - ⌈-1 / rt⌉).toNat : ℝ) ≤ 2 / rt + 1 := by
    have a1 := Int.floor_le (1 / rt)
    have a2 := Int.le_ceil (-1 / rt)
    by_cases h : 0 ≤ ⌊1 / rt⌋ + 1 - ⌈-1 / rt⌉
    · rw [show (((⌊1 / rt⌋ + 1 - ⌈-1 / rt⌉).toNat : ℕ) : ℝ) =
          ((⌊1 / rt⌋ + 1 - ⌈-1 / rt⌉ : ℤ) : ℝ) by exact_mod_cast Int.toNat_of_nonneg h]
      push_cast
      have e1 : -1 / rt = -(1 / rt) := by ring
      have e2 : 2 / rt = 2 * (1 / rt) := by ring
      have a2' : -(1 / rt) ≤ (⌈-1 / rt⌉ : ℝ) := by rw [← e1]; exact a2
      rw [e2]
      linarith
    · push Not at h
      rw [Int.toNat_of_nonpos h.le]
      simp only [Nat.cast_zero]; positivity
  have h3 : 2 / rt + 1 ≤ 3 / rt := by
    have : 1 ≤ 1 / rt := by rw [le_div_iff₀ hrt]; linarith
    have e : 3 / rt = 2 / rt + 1 / rt := by ring
    linarith
  calc ((goodCells rt).card : ℝ) ≤ ((⌊1 / rt⌋ + 1 - ⌈-1 / rt⌉).toNat : ℝ) := by
        exact_mod_cast h1
    _ ≤ 3 / rt := h2.trans h3

/-- Every height of `[-1, 1]` outside three short intervals lies in a good cell. -/
lemma mem_goodCell_of {rt z : ℝ} (hrt : 0 < rt) (hz : z ∈ Icc (-1 : ℝ) 1)
    (h1 : -1 + 2 * rt < z) (h2 : z < 1 - 3 * rt) (h3 : 4 * rt < |z|) :
    ⌊z / rt⌋ ∈ goodCells rt := by
  classical
  set j := ⌊z / rt⌋
  have hj1 : (j : ℝ) ≤ z / rt := Int.floor_le _
  have hj2 : z / rt < j + 1 := Int.lt_floor_add_one _
  have hj1' : (j : ℝ) * rt ≤ z := by rwa [le_div_iff₀ hrt] at hj1
  have hj2' : z < (j + 1) * rt := by rwa [div_lt_iff₀ hrt] at hj2
  unfold goodCells
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- `⌈-1/rt⌉ ≤ j`
    rw [Int.ceil_le]
    have : -1 / rt + 1 ≤ z / rt := by
      rw [div_add_one hrt.ne', div_le_div_iff_of_pos_right hrt]; linarith
    linarith
  · exact Int.floor_mono (div_le_div_of_nonneg_right hz.2 hrt.le)
  · nlinarith
  · nlinarith
  · rcases le_or_gt 0 z with hz0 | hz0
    · rw [abs_of_nonneg hz0] at h3
      left
      have : (3 : ℝ) < j + 1 := by
        rw [← div_lt_iff₀ hrt] at hj2'
        have : 4 < z / rt := by rw [lt_div_iff₀ hrt]; linarith
        linarith
      have : (2 : ℤ) < j := by exact_mod_cast (show (2 : ℝ) < j by linarith)
      omega
    · rw [abs_of_neg hz0] at h3
      right
      have : (j : ℝ) < -4 := by
        have : z / rt < -4 := by rw [div_lt_iff₀ hrt]; linarith
        linarith
      have : j < -4 := by exact_mod_cast this
      omega

/-- The heights of a good cell are covered by its full rows and two short intervals. -/
lemma cell_cover {s rt : ℝ} (hs : 0 < s) {j : ℤ} {z : ℝ}
    (hz1 : (j : ℝ) * rt ≤ z) (hz2 : z < (j + 1) * rt) :
    z ∈ rowUnion s (Finset.Ico (cellLo s rt j) (cellHi s rt j)) ∪
      (Icc ((j : ℝ) * rt) (s * cellLo s rt j) ∪ Icc (s * cellHi s rt j) ((j + 1) * rt)) := by
  by_cases ha : z < s * cellLo s rt j
  · exact Or.inr (Or.inl ⟨hz1, ha.le⟩)
  by_cases hb : s * cellHi s rt j ≤ z
  · exact Or.inr (Or.inr ⟨hb, hz2.le⟩)
  push Not at ha hb
  left
  refine mem_iUnion₂.mpr ⟨⌊z / s⌋, Finset.mem_Ico.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [Int.le_floor, le_div_iff₀ hs]; linarith
  · rw [Int.floor_lt, div_lt_iff₀ hs]; linarith
  · have h1 := Int.floor_le (z / s)
    have h2 := Int.lt_floor_add_one (z / s)
    rw [le_div_iff₀ hs] at h1
    rw [div_lt_iff₀ hs] at h2
    exact ⟨by linarith, by linarith⟩

lemma cellHi_le_cellLo {s rt : ℝ} (hs : 0 < s) (hrt : 0 < rt) {j j' : ℤ} (hjj : j < j') :
    cellHi s rt j ≤ cellLo s rt j' := by
  obtain ⟨-, -, h1, -⟩ := cell_rows (rt := rt) hs j
  obtain ⟨h2, -, -, -⟩ := cell_rows (rt := rt) hs j'
  have h3 : ((j : ℝ) + 1) * rt ≤ j' * rt := by
    have : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hjj
    exact mul_le_mul_of_nonneg_right this hrt.le
  have : s * (cellHi s rt j : ℝ) ≤ s * cellLo s rt j' := by linarith
  have := le_of_mul_le_mul_left this hs
  exact_mod_cast this

lemma heightMass_eq_shading {n : ℕ} (Y : Fin n → Set Space) {H : Set ℝ} (hH : MeasurableSet H) :
    heightMass Y H = Reg.shadingHeightMeasure Y H := by
  rw [Reg.shadingHeightMeasure_apply Y hH]
  rfl

/-- The local grid linearity mass bound for one refined family and one scale `ρ`. -/
theorem cells_assemble (hS : FineSetup σ δ s θ K N x v Y Eo f P)
    {εl ηl ρ₀ : ℝ} (hspec : SlabSpec σ εl ηl ρ₀) (hsρ : s ≤ ρ₀)
    (hs8 : 8 * s ≤ s ^ ((1 : ℝ) / 2 + εl))
    (hK : 162 * K ≤ s ^ (-ηl)) (hθη : s ^ ηl ≤ (θ - δ) / 2 - 8 * s)
    (hN : 0 < N) (hn : 0 < n) {ρ : ℝ} (hρ1 : ρ ≤ 1) (hsρ4 : 4 * s ≤ ρ)
    (hheavy : ∀ Mw : ℝ, Real.sqrt s * (heightMass Y (Icc (-1) 1)).toReal / 60 ≤ Mw →
      s ^ (1 + σ / 2 + ηl) ≤ 9 * s * θ ^ 4 * Mw ^ 2 / (16 * 2304 * N * δ ^ 4 *
        pieceBound σ δ s θ K ((winLen s : ℝ) * s) * winLen s * n))
    {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ l u : ℝ, l ≤ u → heightMass Y (Icc l u) ≤ ENNReal.ofReal (D * (u - l)))
    (hDsmall : 20 * D * Real.sqrt ρ ≤ (heightMass Y (Icc (-1) 1)).toReal / 4) :
    ∃ (J : Finset ℤ) (a b : ℤ → ℝ),
      ENNReal.ofReal (s ^ εl * Real.sqrt s / (24 * Real.sqrt ρ) *
          (heightMass Y (Icc (-1) 1)).toReal) ≤
        Reg.shadingHeightMeasure Y
          (⋃ j ∈ J, Reg.affineFitHeights f (Real.sqrt ρ) ρ j (a j) (b j)) := by
  classical
  have hs := s_pos hS
  have hYb : ∀ i, Y i ⊆ ball (0 : Space) 1 := fun i => (hS.sub_Eo i).trans hS.Eo_ball
  set M := (heightMass Y (Icc (-1) 1)).toReal with hMdef
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  set rt := Real.sqrt ρ with hrtdef
  have hρpos : 0 < ρ := by linarith
  have hrtpos : 0 < rt := Real.sqrt_pos.mpr hρpos
  have hrt1 : rt ≤ 1 := by rw [hrtdef]; exact Real.sqrt_le_one.mpr hρ1
  have hrt : 2 * Real.sqrt s ≤ rt := by
    have : Real.sqrt (4 * s) ≤ rt := Real.sqrt_le_sqrt hsρ4
    rwa [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have hrtsq : rt * rt = ρ := Real.mul_self_sqrt hρpos.le
  -- per cell
  have hcell : ∀ j : ℤ, ∃ (a b : ℝ) (G : Finset ℤ), j ∈ goodCells rt →
      G ⊆ Finset.Ico (cellLo s rt j) (cellHi s rt j) ∧
      (∀ m ∈ G, ∀ z ∈ row s m, |f z - (a + b * z)| ≤ 4 * s) ∧
      (ENNReal.ofReal (s ^ εl * Real.sqrt s / (12 * rt)) *
          heightMass Y (rowUnion s (Finset.Ico (cellLo s rt j) (cellHi s rt j))) ≤
            heightMass Y (rowUnion s G) ∨
        heightMass Y (rowUnion s (Finset.Ico (cellLo s rt j) (cellHi s rt j))) ≤
          ENNReal.ofReal (rt * M / 20)) := by
    intro j
    by_cases hj : j ∈ goodCells rt
    · obtain ⟨h1, h2, h3⟩ := mem_goodCells hj
      obtain ⟨a, b, G, hG, hfit, hor⟩ := cell_fit hS hspec hsρ hs8 hK hθη hN hn hM0 hrt hrt1
        hheavy j h1 h2 h3
      exact ⟨a, b, G, fun _ => ⟨hG, hfit, hor⟩⟩
    · exact ⟨0, 0, ∅, fun h => absurd h hj⟩
  choose a b G hG using hcell
  refine ⟨goodCells rt, a, b, ?_⟩
  set J := goodCells rt with hJ
  set c := s ^ εl * Real.sqrt s / (12 * rt) with hc
  have hc0 : 0 ≤ c := by rw [hc]; have := Real.rpow_nonneg hs.le εl; positivity
  set FR := fun j => rowUnion s (Finset.Ico (cellLo s rt j) (cellHi s rt j))
  set F := fun j => (heightMass Y (FR j)).toReal
  set Gm := fun j => (heightMass Y (rowUnion s (G j))).toReal
  -- each cell
  have hF : ∀ j ∈ J, c * F j ≤ Gm j + c * (rt * M / 20) := by
    intro j hj
    obtain ⟨-, -, hor⟩ := hG j hj
    rcases hor with h | h
    · have := ENNReal.toReal_mono (heightMass_ne_top hYb _) h
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at this
      have : 0 ≤ c * (rt * M / 20) := by positivity
      simp only [F, Gm]; linarith
    · have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      rw [ENNReal.toReal_ofReal (by positivity)] at this
      have h1 : c * F j ≤ c * (rt * M / 20) := mul_le_mul_of_nonneg_left this hc0
      have h2 : 0 ≤ Gm j := ENNReal.toReal_nonneg
      linarith
  -- the decomposition of the total mass
  set Excl := Icc (-1 : ℝ) (-1 + 2 * rt) ∪ (Icc (-4 * rt) (4 * rt) ∪ Icc (1 - 3 * rt) 1)
  set I1 := fun j : ℤ => Icc ((j : ℝ) * rt) (s * cellLo s rt j)
  set I2 := fun j : ℤ => Icc (s * cellHi s rt j) (((j : ℝ) + 1) * rt)
  have hcov : Icc (-1 : ℝ) 1 ⊆ Excl ∪ ⋃ j ∈ J, (FR j ∪ (I1 j ∪ I2 j)) := by
    intro z hz
    by_cases h1 : z ≤ -1 + 2 * rt
    · exact Or.inl (Or.inl ⟨hz.1, h1⟩)
    by_cases h2 : 1 - 3 * rt ≤ z
    · exact Or.inl (Or.inr (Or.inr ⟨h2, hz.2⟩))
    by_cases h3 : |z| ≤ 4 * rt
    · exact Or.inl (Or.inr (Or.inl (abs_le.mp h3 |>.elim fun a b => ⟨by linarith, b⟩)))
    push Not at h1 h2 h3
    refine Or.inr (mem_iUnion₂.mpr ⟨⌊z / rt⌋, mem_goodCell_of hrtpos hz h1 h2 h3, ?_⟩)
    have hj1 : (⌊z / rt⌋ : ℝ) * rt ≤ z := by
      have := Int.floor_le (z / rt); rwa [le_div_iff₀ hrtpos] at this
    have hj2 : z < ((⌊z / rt⌋ : ℝ) + 1) * rt := by
      have := Int.lt_floor_add_one (z / rt); rwa [div_lt_iff₀ hrtpos] at this
    exact cell_cover hs hj1 hj2
  have hExcl : heightMass Y Excl ≤ ENNReal.ofReal (D * (13 * rt)) := by
    calc heightMass Y Excl ≤ heightMass Y (Icc (-1 : ℝ) (-1 + 2 * rt)) +
          (heightMass Y (Icc (-4 * rt) (4 * rt)) + heightMass Y (Icc (1 - 3 * rt) 1)) :=
          (heightMass_union_le Y _ _).trans (add_le_add le_rfl (heightMass_union_le Y _ _))
      _ ≤ ENNReal.ofReal (D * (2 * rt)) + (ENNReal.ofReal (D * (8 * rt)) +
          ENNReal.ofReal (D * (3 * rt))) := by
          gcongr
          · exact (hD _ _ (by linarith)).trans (le_of_eq (by congr 1; ring))
          · exact (hD _ _ (by linarith)).trans (le_of_eq (by congr 1; ring))
          · exact (hD _ _ (by linarith)).trans (le_of_eq (by congr 1; ring))
      _ = ENNReal.ofReal (D * (13 * rt)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  have hI : ∀ j, heightMass Y (I1 j) ≤ ENNReal.ofReal (D * s) ∧
      heightMass Y (I2 j) ≤ ENNReal.ofReal (D * s) := by
    intro j
    obtain ⟨a1, a2, b1, b2⟩ := cell_rows (rt := rt) hs j
    constructor
    · refine (hD _ _ a1).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (by linarith) hD0
    · refine (hD _ _ b1).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (by linarith) hD0
  have hMle : M ≤ D * (13 * rt) + ∑ j ∈ J, (F j + 2 * (D * s)) := by
    have h := (heightMass_mono Y hcov).trans ((heightMass_union_le Y _ _).trans
      (add_le_add hExcl ((heightMass_biUnion_le Y J _).trans (Finset.sum_le_sum fun j _ =>
        (heightMass_union_le Y _ _).trans (add_le_add le_rfl
          ((heightMass_union_le Y _ _).trans (add_le_add (hI j).1 (hI j).2)))))))
    have hfin : ∀ j, heightMass Y (FR j) ≠ ∞ := fun j => heightMass_ne_top hYb _
    have := ENNReal.toReal_mono (by
      apply ENNReal.add_ne_top.mpr
      refine ⟨ENNReal.ofReal_ne_top, ?_⟩
      apply ne_of_lt; apply ENNReal.sum_lt_top.mpr; intro j _
      exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr (hfin j),
        ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩⟩) h
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (by
      apply ne_of_lt; apply ENNReal.sum_lt_top.mpr; intro j _
      exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr (hfin j),
        ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩⟩),
      ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_sum (fun j _ => ENNReal.add_ne_top.mpr ⟨hfin j,
        ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩⟩)] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.toReal_add (hfin j) (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩), ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)]
    ring
  -- counting
  have hJc := card_goodCells_le hrtpos hrt1
  have hsrt : s ≤ rt * rt / 4 := by rw [hrtsq]; linarith
  have hsum2 : ∑ j ∈ J, 2 * (D * s) ≤ 3 / 2 * D * rt := by
    rw [Finset.sum_const, nsmul_eq_mul]
    calc (J.card : ℝ) * (2 * (D * s)) ≤ 3 / rt * (2 * (D * (rt * rt / 4))) := by
          gcongr
      _ = 3 / 2 * D * rt := by field_simp; ring
  have hFsum : 3 * M / 4 ≤ ∑ j ∈ J, F j := by
    have : ∑ j ∈ J, (F j + 2 * (D * s)) = ∑ j ∈ J, F j + ∑ j ∈ J, 2 * (D * s) :=
      Finset.sum_add_distrib
    nlinarith
  have hcM : c * (3 * M / 4) - c * (3 * M / 20) ≤ ∑ j ∈ J, Gm j := by
    have h1 : c * ∑ j ∈ J, F j ≤ ∑ j ∈ J, (Gm j + c * (rt * M / 20)) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum hF
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
    have h2 : (J.card : ℝ) * (c * (rt * M / 20)) ≤ 3 / rt * (c * (rt * M / 20)) :=
      mul_le_mul_of_nonneg_right hJc (by positivity)
    have h3 : 3 / rt * (c * (rt * M / 20)) = c * (3 * M / 20) := by field_simp
    have h4 : c * (3 * M / 4) ≤ c * ∑ j ∈ J, F j := mul_le_mul_of_nonneg_left hFsum hc0
    linarith
  -- the retained rows
  have hdisj : (J : Set ℤ).PairwiseDisjoint G := by
    intro j hj j' hj' hjj
    rw [Function.onFun, Finset.disjoint_left]
    intro m hm hm'
    have h1 := Finset.mem_Ico.mp ((hG j hj).1 hm)
    have h2 := Finset.mem_Ico.mp ((hG j' hj').1 hm')
    rcases lt_or_gt_of_ne hjj with h | h
    · have := cellHi_le_cellLo hs hrtpos h; omega
    · have := cellHi_le_cellLo hs hrtpos h; omega
  have hsub : rowUnion s (J.biUnion G) ⊆
      ⋃ j ∈ J, Reg.affineFitHeights f rt ρ j (a j) (b j) := by
    intro z hz
    obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp hz
    obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨hGs, hfit, -⟩ := hG j hj
    refine mem_iUnion₂.mpr ⟨j, hj, ⟨?_, ?_⟩, ?_⟩
    · obtain ⟨a1, -, -, -⟩ := cell_rows (rt := rt) hs j
      have h1 := (Finset.mem_Ico.mp (hGs hmj)).1
      have : (cellLo s rt j : ℝ) ≤ m := by exact_mod_cast h1
      have : s * (cellLo s rt j : ℝ) ≤ s * m := mul_le_mul_of_nonneg_left this hs.le
      linarith [hzm.1]
    · obtain ⟨-, -, b1, -⟩ := cell_rows (rt := rt) hs j
      have h2 := (Finset.mem_Ico.mp (hGs hmj)).2
      have : (m : ℝ) + 1 ≤ cellHi s rt j := by
        have : m + 1 ≤ cellHi s rt j := by omega
        exact_mod_cast this
      have : s * ((m : ℝ) + 1) ≤ s * cellHi s rt j := mul_le_mul_of_nonneg_left this hs.le
      linarith [hzm.2]
    · exact (hfit m hmj z hzm).trans (by linarith)
  have hmeas : MeasurableSet (rowUnion s (J.biUnion G)) :=
    Finset.measurableSet_biUnion _ fun m _ => measurableSet_row s m
  have hsplit : heightMass Y (rowUnion s (J.biUnion G)) = ∑ j ∈ J, heightMass Y (rowUnion s (G j)) := by
    rw [heightMass_rowUnion hS.meas hs, Finset.sum_biUnion hdisj]
    apply Finset.sum_congr rfl
    intro j _
    rw [heightMass_rowUnion hS.meas hs]
  calc ENNReal.ofReal (s ^ εl * Real.sqrt s / (24 * rt) * M)
      ≤ ENNReal.ofReal (∑ j ∈ J, Gm j) := by
        apply ENNReal.ofReal_le_ofReal
        have : s ^ εl * Real.sqrt s / (24 * rt) * M = c * (3 * M / 4) - c * (3 * M / 20) -
            c * (M / 10) := by rw [hc]; field_simp; ring
        have h0 : 0 ≤ c * (M / 10) := by positivity
        linarith
    _ = ∑ j ∈ J, heightMass Y (rowUnion s (G j)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
        apply Finset.sum_congr rfl
        intro j _
        exact ENNReal.ofReal_toReal (heightMass_ne_top hYb _)
    _ = heightMass Y (rowUnion s (J.biUnion G)) := hsplit.symm
    _ = Reg.shadingHeightMeasure Y (rowUnion s (J.biUnion G)) := heightMass_eq_shading Y hmeas
    _ ≤ _ := measure_mono hsub

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
