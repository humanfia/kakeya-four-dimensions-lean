import Submission.Obl.k4_wide_three_layer_scalar_inputs.KeyMenus
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.ShortBound
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass
import Submission.Obl.k4_critical_conditional_row_preparation.NativeJointCap

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MeasureTheory Finset
open Inherited.Native Inherited.Core
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

/-- The original full-assignment references, in real measure units. -/
theorem full_assignment_references_real {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] {n T : ℕ}
    (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set α)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i')) :
    ∑ i, ((2 : ℝ) ^ T)⁻¹ * (ν (A i)).toReal ≤ 1 := by
  have hh := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget
    (fun _ : Unit => ν) (fun _ : Unit => (1 : ENNReal)) (fun _ : Fin n => ()) j A
    (fun _ => measure_univ) (by simp) hA (fun i i' hne _ heq => hdisj i i' hne heq)
  simp only [one_mul, Fintype.card_fin] at hh
  have hr := ENNReal.toReal_mono (by simp) hh
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top ν (A i)), ENNReal.toReal_natCast] at hr
  rw [← Finset.mul_sum]
  calc ((2 : ℝ) ^ T)⁻¹ * ∑ i, (ν (A i)).toReal
      ≤ ((2 : ℝ) ^ T)⁻¹ * ((2 ^ T : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ = 1 := by norm_cast; simp

variable {α : Type} [MeasurableSpace α]

theorem keyRef_eq_palette_interval (cfg : Inherited.Data α) (k : ℕ)
    {χ m q a : ℝ} (hχ : 0 < χ) (key : Fin 3 → ℤ) :
    keyRef cfg k χ m q a key = (q * χ * m * a ^ cfg.d) *
      (cfg.π k (Ico ((key 0 : ℝ) * χ) (((key 0 : ℝ) + 1) * χ))).toReal := by
  unfold keyRef
  rw [Submission.Obl.k4_critical_conditional_row_preparation.floor_bin_eq_Ico χ (key 0) hχ]

/-- The lower preparation bound is charged to the full original prior,
with no surviving label intersection in its denominator. -/
theorem block_reference_lower (cfg : Inherited.Data α) (k : ℕ) (s : ℝ) {R' : ℝ}
    (hB : BlocksAt cfg k s R') [IsFiniteMeasure (cfg.ν k)]
    (hN : 0 < cfg.N k) (hK : 0 < cfg.K k) (i : Fin (cfg.n k s)) :
    (cfg.N k ^ (-s)) ^ cfg.d * (slotLen cfg k s) ^ 3 * cfg.N k ^ (-cfg.κ * s) ≤
      cfg.K k * (slotLen cfg k s * (cfg.ν k (cfg.A k s i)).toReal) := by
  have hlo := ENNReal.toReal_mono (measure_ne_top (cfg.ν k) (cfg.A k s i)) (hB.nu_lo i)
  rw [ENNReal.toReal_ofReal (by positivity)] at hlo
  have hq : 0 < slotLen cfg k s := slotLen_pos cfg k s
  have hprior : (cfg.N k ^ (-s)) ^ cfg.d * (slotLen cfg k s) ^ 2 *
      cfg.N k ^ (-cfg.κ * s) ≤ cfg.K k * (cfg.ν k (cfg.A k s i)).toReal := by
    simpa only [slotLen, mul_comm] using (div_le_iff₀ hK).mp hlo
  have hh := mul_le_mul_of_nonneg_left hprior hq.le
  nlinarith only [hh]

/-- The positive entries of the actual true table have a polynomial
reference budget, independently of the universal key box's cardinality. -/
theorem blockSum_le (cfg : Inherited.Data α) (k : ℕ) (s : ℝ)
    {ε R χ D R' m : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (hB : BlocksAt cfg k s R')
    [IsProbabilityMeasure (cfg.ν k)] [IsProbabilityMeasure (cfg.π k)]
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hχ : 0 < χ) (hm : 0 < m)
    (hχq : χ ≤ slotLen cfg k s)
    (hχg : χ ≤ slotLen cfg k s * cfg.N k ^ (-cfg.κ * s))
    (hmg : m ≤ slotLen cfg k s * cfg.N k ^ (-cfg.κ * s))
    (KB : Finset (Fin 3 → ℤ)) :
    blockSum cfg k s L m KB ≤ 140 * (cfg.K k) ^ 3 := by
  classical
  let H := cfg.N k ^ ε
  have hH : 0 ≤ H := (Real.rpow_pos_of_pos hN _).le
  let q := slotLen cfg k s
  let g := cfg.N k ^ (-cfg.κ * s)
  let a := cfg.N k ^ (-s)
  have hq : 0 < q := slotLen_pos cfg k s
  have hg : 0 < g := Real.rpow_pos_of_pos hN _
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  have hK0 : 0 ≤ cfg.K k := by linarith
  obtain ⟨V, -, hV⟩ := interval_mesh_cover hχ hH 0
  choose F₁ F₂ hF₁ hF₂ hcover using fun i : Fin (cfg.n k s) =>
    true_key_menus hK0 hq hg hχ hm
      (show slotStart cfg k s (cfg.j k s i) ∈ Icc (0 : ℝ) 1 from
        ⟨(slot_unit cfg k s _).1, by linarith [(slot_unit cfg k s (cfg.j k s i)).2]⟩)
      (cfg.c k s i) (hB.c_bd i 4) V
  let w : ℤ → ℝ := fun v =>
    (cfg.π k (Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ))).toReal
  have hw : ∀ v, 0 ≤ w v := fun _ => ENNReal.toReal_nonneg
  have hwsum : ∑ v ∈ V, w v ≤ 1 := by
    have hh := ENNReal.toReal_mono ENNReal.one_ne_top (sum_bins_le_one hχ V (π := cfg.π k))
    rw [ENNReal.toReal_sum (fun v _ => measure_ne_top _ _)] at hh
    simpa [w] using hh
  have hsub : ∀ i, KB.filter (fun key => 0 < L.ρs (blockLab cfg k s L m i key ×ˢ
      cfg.I (cfg.T k s) (cfg.j k s i))) ⊆ keyBox V (F₁ i) (F₂ i) := by
    intro i key hk
    obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero (Finset.mem_filter.mp hk).2.ne'
    obtain ⟨⟨⟨hlB, hlGood⟩, hkey⟩, -⟩ := hp
    obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp hlGood
    have hparams := (L.mem_bins hi₀).2.2.2
    have ht₀ : slotStart cfg k s (cfg.j k s i) ∈ cfg.I (cfg.T k s) (cfg.j k s i) := by
      rw [I_eq_slot]
      exact ⟨le_rfl, le_add_of_nonneg_right hq.le⟩
    obtain ⟨hZ, hY, -⟩ := hB.geom i p.1 ((hB.sets i).2.2 hlB) _ ht₀
    have hv : ⌊cfg.b k p.1 3 / χ⌋ ∈ V := hV _ (by simpa [H] using hparams 3)
    have hh := hcover i (cfg.b k p.1) hv hZ hY
    change slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) p.1 ∈
      keyBox V (F₁ i) (F₂ i) at hh
    rwa [hkey] at hh
  have hbudget := sum_true_key_references hK hq hg hχ hm ha hχq hχg hmg
    V F₁ F₂ hF₁ hF₂ w hw hwsum
    (fun i => q * (cfg.ν k (cfg.A k s i)).toReal)
    (full_assignment_references_real (cfg.ν k) (cfg.j k s) (cfg.A k s)
      (fun i => (hB.sets i).1) hB.disj)
    (fun i => block_reference_lower cfg k s hB hN (by linarith) i)
  apply le_trans _ hbudget
  unfold blockSum
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_congr rfl (fun key _ => keyRef_eq_palette_interval cfg k hχ key)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (hsub i) (fun key _ _ => by positivity)

/-- Summability of the actual projected full-strip references, converted
from the datum's unchanged ENNReal budget. -/
theorem layer_reference_budget_real (cfg : Inherited.Data α) (k : ℕ)
    {ε R χ D : ℝ} {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth)
    [IsFiniteMeasure (cfg.π k)] (hN : 0 < cfg.N k) (hχ : 0 ≤ χ) (hD : 0 ≤ D) (h : Fin 3) :
    (∑ i, χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d *
      (cfg.π k (Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ))).toReal) ≤
        cfg.N k ^ ε := by
  have hc : 0 ≤ χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d := by positivity
  have hfin : ∀ i, ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d) *
      cfg.π k (Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ)) ≠ ⊤ :=
    fun _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have heq : (∑ i, χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d *
      (cfg.π k (Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ))).toReal) =
      (∑ i, ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d) *
        cfg.π k (Ico ((L.qp h i 0 : ℝ) * χ) (((L.qp h i 0 : ℝ) + 1) * χ))).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => hfin i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  rw [heq]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (L.sum h)).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

/-- Every color's actual positive short entries cost only a subpower
multiple of its original full-strip reference sum. Summing the time slots
cancels their common length exactly. -/
theorem pieceSum_le (cfg : Inherited.Data α) (k : ℕ) (s : ℝ)
    {ε R χ D m : ℝ} {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth)
    [IsProbabilityMeasure (cfg.π k)] (hN : 0 < cfg.N k)
    (hH : 1 ≤ cfg.N k ^ ε) (hχ : 0 < χ) (hD : 0 < D) (hm : 0 < m) (hmD : m ≤ D)
    (KB : Finset (Fin 3 → ℤ)) (h : Fin 3) :
    pieceSum cfg k s L m KB h ≤ 6 * (cfg.N k ^ ε) ^ 2 := by
  classical
  let H := cfg.N k ^ ε
  let q := slotLen cfg k s
  let a := cfg.N k ^ (-depth h)
  have hq : 0 < q := slotLen_pos cfg k s
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  have hHD : 0 ≤ H * D := by dsimp [H]; positivity
  choose J hJ hcover using fun (jj : Fin (2 ^ cfg.T k s)) (i : Fin (L.np h)) =>
    interval_mesh_cover hm hHD
      ((L.qp h i 2 : ℝ) * D - slotStart cfg k s jj * ((L.qp h i 1 : ℝ) * χ))
  let w : ℤ → ℝ := fun v =>
    (cfg.π k (Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ))).toReal
  have hw : ∀ v, 0 ≤ w v := fun _ => ENNReal.toReal_nonneg
  have hsub : ∀ i jj, KB.filter (fun key => 0 < L.ρs
      (pieceLab cfg k s L m h i jj key ×ˢ cfg.I (cfg.T k s) jj)) ⊆
      keyBox {L.qp h i 0} (fun _ => {L.qp h i 1}) (fun _ _ => J jj i) := by
    intro i jj key hk
    obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero (Finset.mem_filter.mp hk).2.ne'
    obtain ⟨⟨hlC, hkey⟩, -⟩ := hp
    have ht₀ : slotStart cfg k s jj ∈ Icc (0 : ℝ) 1 :=
      ⟨(slot_unit cfg k s jj).1, by linarith [(slot_unit cfg k s jj).2, slotLen_pos cfg k s]⟩
    have hstrip := ((L.piece h i).2.2.2.2.2.1 p.1 hlC _ ht₀).1
    simp only [Inherited.Data.x, Matrix.cons_val] at hstrip
    have hY : ⌊(cfg.b k p.1 1 + slotStart cfg k s jj * cfg.b k p.1 4) / m⌋ ∈ J jj i := by
      apply hcover jj i
      convert hstrip using 1 <;> congr 1 <;> ring
    have h0 : ⌊cfg.b k p.1 3 / χ⌋ = key 0 := by
      have hh := congrFun hkey 0
      simpa [slotKey] using hh
    have h1 : ⌊cfg.b k p.1 0 / χ⌋ = key 1 := by
      have hh := congrFun hkey 1
      simpa [slotKey] using hh
    have h2 : ⌊(cfg.b k p.1 1 + slotStart cfg k s jj * cfg.b k p.1 4) / m⌋ = key 2 := by
      have hh := congrFun hkey 2
      simpa [slotKey] using hh
    apply mem_keyBox
    · exact Finset.mem_singleton.mpr (h0.symm.trans (L.mem_bins hlC).1)
    · exact Finset.mem_singleton.mpr (h1.symm.trans (L.mem_bins hlC).2.1)
    · rwa [h2] at hY
  have hsum := sum_projected_key_references (d := cfg.d) hH hD hχ hm ha hmD (cfg.T k s) (q := q) rfl
    (fun i => L.qp h i 0) (fun i => L.qp h i 1) J hJ w hw
  have hfull : (∑ i, (χ * D * a ^ cfg.d) * w (L.qp h i 0)) ≤ H :=
    layer_reference_budget_real cfg k L hN hχ.le hD.le h
  calc pieceSum cfg k s L m KB h
      = ∑ jj : Fin (2 ^ cfg.T k s), ∑ i, ∑ key ∈ KB.filter (fun key => 0 < L.ρs
          (pieceLab cfg k s L m h i jj key ×ˢ cfg.I (cfg.T k s) jj)),
          keyRef cfg k χ m q a key := by unfold pieceSum; exact Finset.sum_comm
    _ ≤ ∑ jj : Fin (2 ^ cfg.T k s), ∑ i,
        ∑ key ∈ keyBox {L.qp h i 0} (fun _ => {L.qp h i 1}) (fun _ _ => J jj i),
          (q * χ * m * a ^ cfg.d) * w (key 0) := by
      apply Finset.sum_le_sum
      intro jj _
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.sum_congr rfl (fun key _ => keyRef_eq_palette_interval cfg k hχ key)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (hsub i jj) (fun key _ _ => mul_nonneg (by positivity) (hw (key 0)))
    _ ≤ 6 * H * ∑ i, (χ * D * a ^ cfg.d) * w (L.qp h i 0) := hsum
    _ ≤ 6 * H * H := mul_le_mul_of_nonneg_left hfull (by dsimp [H]; positivity)
    _ = 6 * (cfg.N k ^ ε) ^ 2 := by dsimp [H]; ring

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
