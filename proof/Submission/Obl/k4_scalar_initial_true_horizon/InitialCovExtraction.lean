import Submission.Obl.k4_scalar_initial_true_horizon.InitialFiniteSelection
import Submission.Obl.k4_scalar_initial_true_horizon.InitialWorld

/-! Extract finite maximal good cells from the covered original incidences. -/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open scoped ENNReal BigOperators
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction (Coeff)

structure InitialCellIndex (W T : ℕ) where
  world : Fin W
  block : Fin (2 ^ T)
  bin : ℤ
  level : ℕ
  coords : ℤ × ℤ

noncomputable def initialMaximalCell (p : Data) (k T kmax : ℕ) (Φf : ℝ)
    (d : InitialCellIndex (worlds p k) T) : Prop :=
  let q := 1 / (2 : ℝ) ^ T
  let s := ((d.block : ℕ) : ℝ) / (2 : ℝ) ^ T
  MaxGood (fun l => bddTraj (N p k ^ (M p : ℝ)) (K p k) l ∧
      xBin (N p k ^ (-L p)) s l = d.bin)
    (cellIdx q s)
    (goodCell (mu p k d.world) (N p k ^ (M p : ℝ)) (K p k)
      (N p k ^ (-L p)) q s Φf d.bin) kmax d.level d.coords

theorem initialMaximalCell_disjoint {p : Data} {k T kmax : ℕ} {Φf : ℝ}
    (d e : InitialCellIndex (worlds p k) T)
    (hd : initialMaximalCell p k T kmax Φf d) (he : initialMaximalCell p k T kmax Φf e)
    (hne : d ≠ e) (hw : d.world = e.world) (hj : d.block = e.block) :
    Disjoint (initialAssignment p k T d.block d.bin d.level d.coords)
      (initialAssignment p k T e.block e.bin e.level e.coords) := by
  apply Set.disjoint_left.mpr
  intro l hld hle
  rcases d with ⟨dw, dj, dm, dl, dc⟩
  rcases e with ⟨ew, ej, em, el, ec⟩
  cases hw
  cases hj
  have hm : dm = em := hld.2.1.symm.trans hle.2.1
  subst em
  have hpair : (dl, dc) ≠ (el, ec) := by
    intro hpairs
    obtain ⟨hlev, hcoords⟩ := Prod.mk.inj hpairs
    cases hlev
    cases hcoords
    exact hne rfl
  exact maxGood_disjoint
    (idx := cellIdx (1 / (2 : ℝ) ^ T) ((dj : ℕ) / (2 : ℝ) ^ T))
    (fun _ _ _ _ hkk heq => cellIdx_nested hkk heq) hd he hpair
    ⟨hld.1, hld.2.1⟩ hld.2.2 hle.2.2

theorem initialMaximalCell_floor {p : Data} {k T kmax : ℕ} {Φf : ℝ}
    (hΦf : 0 ≤ Φf) (d : InitialCellIndex (worlds p k) T)
    (hd : initialMaximalCell p k T kmax Φf d) :
    ENNReal.ofReal (Φf * cellJ (1 / (2 : ℝ) ^ T) kmax) ≤
      mu p k d.world (initialAssignment p k T d.block d.bin d.level d.coords ×ˢ I T d.block) := by
  let q := 1 / (2 : ℝ) ^ T
  let s := ((d.block : ℕ) : ℝ) / (2 : ℝ) ^ T
  have hq : 0 < q := by dsimp [q]; positivity
  have hmin : cellJ q kmax ≤ cellJ q d.level := by
    unfold cellJ
    exact div_le_div_of_nonneg_left hq.le (by positivity)
      (pow_le_pow_right₀ (by norm_num) hd.1)
  have hgood : ENNReal.ofReal (Φf * cellJ q d.level) ≤ mu p k d.world
      (initialAssignment p k T d.block d.bin d.level d.coords ×ˢ Icc s (s + q)) := hd.2.1
  have hI : I T d.block = Icc s (s + q) := by
    dsimp [I, s, q]
    congr 1
    ring
  rw [hI]
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmin hΦf)).trans hgood

/-- The good-cell floor at its own selected level. -/
theorem initialMaximalCell_good_floor {p : Data} {k T kmax : ℕ} {Φf : ℝ}
    (d : InitialCellIndex (worlds p k) T)
    (hd : initialMaximalCell p k T kmax Φf d) :
    ENNReal.ofReal (Φf * cellJ (1 / (2 : ℝ) ^ T) d.level) ≤
      mu p k d.world (initialAssignment p k T d.block d.bin d.level d.coords ×ˢ I T d.block) := by
  have hI : I T d.block = Icc (((d.block : ℕ) : ℝ) / (2 : ℝ) ^ T)
      (((d.block : ℕ) : ℝ) / (2 : ℝ) ^ T + 1 / (2 : ℝ) ^ T) := by
    dsimp [I]
    congr 1
    ring
  rw [hI]
  exact hd.2.1

/-- Every covered incidence belongs to one of the maximal good cells. -/
theorem covInc_maximal_cover {p : Data} {k T kmax : ℕ} {Φf : ℝ}
    {a : Fin (worlds p k)} {z : Incidence}
    (hz : z ∈ covInc (mu p k a) (N p k ^ (M p : ℝ)) (K p k)
      (N p k ^ (-L p)) (1 / (2 : ℝ) ^ T) Φf T kmax) :
    ∃ d : InitialCellIndex (worlds p k) T,
      initialMaximalCell p k T kmax Φf d ∧ d.world = a ∧
      z.1 ∈ initialAssignment p k T d.block d.bin d.level d.coords ∧ z.2 ∈ I T d.block := by
  rcases hz with ⟨j, hj, ht, hbd, hcov⟩
  let jf : Fin (2 ^ T) := ⟨j, hj⟩
  let q := 1 / (2 : ℝ) ^ T
  let s := ((jf : ℕ) : ℝ) / (2 : ℝ) ^ T
  have hstart : (j : ℝ) * q = s := by dsimp [q, s, jf]; ring
  change z.2 ∈ Ico ((j : ℝ) * q) ((j : ℝ) * q + q) at ht
  rw [hstart] at ht
  change ∃ lev ≤ kmax, goodCell (mu p k a) (N p k ^ (M p : ℝ)) (K p k)
    (N p k ^ (-L p)) q ((j : ℝ) * q) Φf
    (xBin (N p k ^ (-L p)) ((j : ℝ) * q) z.1) lev
    (cellIdx q ((j : ℝ) * q) lev z.1) at hcov
  rw [hstart] at hcov
  obtain ⟨lev, c, hmax, hidx⟩ := exists_maxGood_of_covered
    (idx := cellIdx q s)
    (P := fun l => bddTraj (N p k ^ (M p : ℝ)) (K p k) l ∧
      xBin (N p k ^ (-L p)) s l = xBin (N p k ^ (-L p)) s z.1)
    (fun _ _ _ _ hkk heq => cellIdx_nested hkk heq) ⟨hbd, rfl⟩ hcov
  refine ⟨⟨a, jf, xBin (N p k ^ (-L p)) s z.1, lev, c⟩, hmax, rfl,
    ⟨hbd, rfl, hidx⟩, ?_⟩
  have hI : I T jf = Icc s (s + q) := by
    dsimp [I, s, q]
    congr 1
    ring
  rw [hI]
  exact ⟨ht.1, ht.2.le⟩

/-- The selected index set is finite before any enumeration is chosen. -/
theorem initialMaximalCells_finite {p : Data} (hp : Exact p) (k T kmax : ℕ) {Φf : ℝ}
    (hΦf : 0 < Φf) : {d | initialMaximalCell p k T kmax Φf d}.Finite := by
  apply finite_initial_assignment_family hp (η := Φf * cellJ (1 / (2 : ℝ) ^ T) kmax)
    {d | initialMaximalCell p k T kmax Φf d}
    (fun d => d.world) (fun d => d.block)
    (fun d => initialAssignment p k T d.block d.bin d.level d.coords)
  · intro d _
    exact cellSet_measurable _ _ _ _ _ _ _ _
  · intro d hd e he hne hw hj
    exact initialMaximalCell_disjoint (kmax := kmax) (Φf := Φf) d e hd he hne hw hj
  · exact mul_pos hΦf (cellJ_pos (by positivity) kmax)
  · intro d hd
    exact initialMaximalCell_floor hΦf.le d hd

/-- The maximal covered original cells give a raw true chart once the
scale, common-floor count and original covered mass have been bounded. -/
theorem rawChart_of_covInc {p : Data} (hp : Exact p) {k T kmax B : ℕ} {h ε Φf : ℝ}
    (hB : 1 ≤ B) (hMB : M p ≤ B) (hDB : D p ≤ B)
    (hT : (2 : ℝ) ^ T ≤ N p k ^ h)
    (hqL : 1 / (2 : ℝ) ^ T ≤ N p k ^ (-L p))
    (hformat : N p k ^ (M p : ℝ) + 18 ≤ N p k ^ (B : ℝ))
    (hslack : 4 * K p k + 3 ≤ N p k ^ ε)
    (hparam : 4 * K p k + 3 ≤ N p k ^ (B : ℝ))
    (hΦf : Φf = N p k ^ (-profile p (L p)) * (1 / (2 : ℝ) ^ T) / N p k ^ ε)
    (hinv : (2 : ℝ) ^ kmax * (2 : ℝ) ^ T ≤ N p k ^ (B : ℝ))
    (hcount : (worlds p k : ℝ) / (Φf * cellJ (1 / (2 : ℝ) ^ T) kmax) ≤
      N p k ^ (B : ℝ))
    (hmass : ENNReal.ofReal (N p k ^ (-ε)) ≤ ∑ a, ENNReal.ofReal (weight p k a) *
      mu p k a (covInc (mu p k a) (N p k ^ (M p : ℝ)) (K p k)
        (N p k ^ (-L p)) (1 / (2 : ℝ) ^ T) Φf T kmax)) :
    RawChart p B (L p) (L p) h ε true k := by
  classical
  have hN : 0 < N p k := by linarith [hp.resolution_ge k]
  have hΦ : 0 < Φf := by
    rw [hΦf]
    exact div_pos (mul_pos (Real.rpow_pos_of_pos hN _) (by positivity))
      (Real.rpow_pos_of_pos hN _)
  let S := {d | initialMaximalCell p k T kmax Φf d}
  have hS : S.Finite := initialMaximalCells_finite hp k T kmax hΦ
  letI : Fintype S := hS.fintype
  let n := Fintype.card S
  let e : S ≃ Fin n := Fintype.equivFin S
  let d : Fin n → InitialCellIndex (worlds p k) T := fun i => (e.symm i).val
  let γ : Fin n → Fin (worlds p k) := fun i => (d i).world
  let j : Fin n → Fin (2 ^ T) := fun i => (d i).block
  let m : Fin n → ℤ := fun i => (d i).bin
  let lev : Fin n → ℕ := fun i => (d i).level
  let c : Fin n → ℤ × ℤ := fun i => (d i).coords
  have hd : ∀ i, initialMaximalCell p k T kmax Φf (d i) := fun i => (e.symm i).property
  have hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' →
      Disjoint (initialAssignment p k T (j i) (m i) (lev i) (c i))
        (initialAssignment p k T (j i') (m i') (lev i') (c i')) := by
    intro i i' hne hw hj
    apply initialMaximalCell_disjoint (d i) (d i') (hd i) (hd i') _ hw hj
    intro heq
    exact hne (e.symm.injective (Subtype.ext heq))
  have hη : 0 < Φf * cellJ (1 / (2 : ℝ) ^ T) kmax :=
    mul_pos hΦ (cellJ_pos (by positivity) kmax)
  have hn : (n : ℝ) ≤ N p k ^ (B : ℝ) := by
    apply le_trans _ hcount
    exact initial_cell_count_le hp γ j
      (fun i => initialAssignment p k T (j i) (m i) (lev i) (c i))
      (fun _ => cellSet_measurable _ _ _ _ _ _ _ _) hdisj hη
      (fun i => initialMaximalCell_floor hΦ.le (d i) (hd i))
  apply rawChart_of_cells hp hB hMB hDB γ j m lev c hT hn hqL hformat hslack hparam
  · intro i
    calc
      (cellJ (1 / (2 : ℝ) ^ T) (lev i))⁻¹ = (2 : ℝ) ^ (lev i) * (2 : ℝ) ^ T := by
        simp [cellJ, div_eq_mul_inv]
      _ ≤ (2 : ℝ) ^ kmax * (2 : ℝ) ^ T := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (hd i).1)
          (by positivity)
      _ ≤ _ := hinv
  · exact hdisj
  · intro i
    rw [initialIncidences_mu_eq hp]
    have heq : N p k ^ (-profile p (L p)) * cellJ (1 / (2 : ℝ) ^ T) (lev i) /
        (N p k ^ ε * (2 : ℝ) ^ T) = Φf * cellJ (1 / (2 : ℝ) ^ T) (lev i) := by
      rw [hΦf]
      ring
    rw [heq]
    exact initialMaximalCell_good_floor (d i) (hd i)
  · apply hmass.trans
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_right
    change (((prior p k a).prod volume).restrict (event p k a)) _ ≤
      (((prior p k a).prod volume).restrict (event p k a)) _
    rw [Measure.restrict_apply' (hp.event_measurable k a),
      Measure.restrict_apply' (hp.event_measurable k a)]
    apply measure_mono
    intro z hz
    obtain ⟨d₀, hd₀, hw, hA, ht⟩ := covInc_maximal_cover hz.1
    let i : Fin n := e ⟨d₀, hd₀⟩
    have hdi : d i = d₀ := by simp [d, i]
    have hγ : γ i = a := by change (d i).world = a; rw [hdi]; exact hw
    refine ⟨⟨i, hγ, ?_⟩, hz.2⟩
    change z ∈ event p k (γ i) ∩ (initialAssignment p k T (d i).block (d i).bin
      (d i).level (d i).coords ×ˢ I T (d i).block)
    rw [hγ, hdi]
    exact ⟨hz.2, hA, ht⟩

end Submission.Obl.k4_scalar_initial_true_horizon
