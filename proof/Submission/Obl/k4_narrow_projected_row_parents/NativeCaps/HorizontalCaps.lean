import Submission.Obl.k4_narrow_projected_row_parents.NativeCaps.ParentUniformCaps
import Submission.Obl.k4_narrow_projected_row_parents.NativeCaps.ParentStablePartition
import Submission.Obl.k4_narrow_projected_row_parents.NativeCaps.ParentChart
import Submission.Obl.k4_narrow_projected_row_parents.NativeCaps.HorizontalProjection
import Submission.Obl.k4_critical_conditional_row_preparation.NativeJointCap

namespace Submission.Obl.k4_narrow_projected_row_parents.NativeCaps

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Obl.k4_narrow_projected_row_parents.PreparedModel

noncomputable section

def horizontalParentConstant (K : ℝ) : ℝ := 6 * K * recoveredParentBaseConstant K 1

theorem horizontalParentConstant_polynomial {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ horizontalParentConstant K ∧ horizontalParentConstant K ≤ 30000000 * K ^ 20 := by
  have heq : horizontalParentConstant K = 21233664 * K ^ 17 + 1296 * K ^ 3 := by
    unfold horizontalParentConstant recoveredParentBaseConstant
    ring
  rw [heq]
  constructor
  · have h17 : 1 ≤ K ^ 17 := one_le_pow₀ hK
    have h3 : 0 ≤ K ^ 3 := pow_nonneg (zero_le_one.trans hK) _
    linarith
  · calc 21233664 * K ^ 17 + 1296 * K ^ 3
        ≤ 21233664 * K ^ 20 + 1296 * K ^ 20 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK (by decide : 17 ≤ 20)) (by norm_num))
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK (by decide : 3 ≤ 20)) (by norm_num))
      _ ≤ 30000000 * K ^ 20 := by nlinarith [pow_nonneg (zero_le_one.trans hK) 20]

theorem horizontalParentConstant_subpow (p : Parameters) (hp : p.Valid) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, horizontalParentConstant (p.K k) ≤ p.N k ^ ε := by
  intro ε hε
  have h := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [hp.1 k]) hp.2.1 hp.2.2.1.1 hp.2.2.1.2 20
    (a := 0) (b := ε) hε (A := 30000000) (by norm_num)
  filter_upwards [h] with k hk
  exact (horizontalParentConstant_polynomial (hp.2.2.1.1 k)).2.trans
    (by simpa only [Real.rpow_zero, mul_one] using hk.le)

variable {α : Type} [MeasurableSpace α]

/-- The original horizontal joint cap in a true parent, after a negligible
full-parent deletion. Both the original palette weight and the full original
assignment weight remain explicit. -/
theorem eventually_parent_horizontal_caps
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (ha : a.Valid p)
    {r t : ℝ} (hr : 0 < r) (hrU : r ≤ p.U) (ht : 0 < t) :
    ∀ᶠ k in atTop, ∀ i : Fin (a.n k r), ∃ G : Set (α × ℝ),
      MeasurableSet G ∧ G ⊆ a.B k r i ×ˢ a.block k r i ∧
      a.mu k ((a.B k r i ×ˢ a.block k r i) \ G) ≤
        ENNReal.ofReal (p.K k * (parentFilling (p.K k) (width p k r))⁻¹) *
          (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r i)) ∧
      ∀ (c : Fin 2 → ℤ) (j : ℤ),
        a.rho k {z | z ∈ G ∧ hcell (parentZoom p a k r i) (p.N k ^ (-t))
            (a.b k z.1) z.2 = c ∧ ⌊a.b k z.1 3 / p.N k ^ (-t)⌋ = j} ≤
          ENNReal.ofReal (horizontalParentConstant (p.K k) * (p.N k ^ (-t)) ^ 2) *
            a.pi k (Ico ((j : ℝ) * p.N k ^ (-t)) (((j : ℝ) + 1) * p.N k ^ (-t))) *
            (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r i)) := by
  obtain ⟨B, hB, hgroups⟩ := eventually_parent_signal_groups p hp a ha.1 ha.2.1 ha.2.2.1 hr hrU
  obtain ⟨C, hC, hmatrix⟩ := eventually_parentChart_matrix_bound p hp a hr
  have hcaps := eventually_parent_uniform_caps p hp a ha.1 ha.2.1 ha.2.2.1
    hr hrU hB.le hC (fun _ => 1) t t ht ht
  let R : ℝ := 2 + r + r⁻¹
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hR : 1 < R := by dsimp [R]; linarith
  have hRr : R⁻¹ ≤ r := by
    have h : r⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [inv_inv] using inv_anti₀ hri h
  filter_upwards [hgroups, hmatrix, hcaps, ha.2.2.1 R hR] with k hgroup hmat hcap hAt
  intro i
  have hA : a.AtlasAt p R k r := hAt r hRr hrU
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hK : 1 ≤ p.K k := hp.2.2.1.1 k
  have hK0 : 0 ≤ p.K k := zero_le_one.trans hK
  have hKp : 0 < p.K k := zero_lt_one.trans_le hK
  have hq := q_pos a k r
  have hg := narrow_pos p hp k r
  have hξ : 0 < p.N k ^ (-t) := Real.rpow_pos_of_pos hN _
  have hξ1 : p.N k ^ (-t) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hp.1 k]) (by linarith)
  letI : IsProbabilityMeasure (a.nu k) := (ha.1 k).2.1
  letI : IsProbabilityMeasure (a.pi k) := (ha.1 k).2.2.1
  obtain ⟨E, hEm, hEsub, hEd, hEloss, hEosc⟩ := hgroup i
  let G : Set (α × ℝ) := ⋃ e, E e
  have hGm : MeasurableSet G := MeasurableSet.iUnion hEm
  have hGsub : G ⊆ a.B k r i ×ˢ a.block k r i := by
    intro z hz
    obtain ⟨e, he⟩ := mem_iUnion.mp hz
    exact hEsub e he
  let ν : Measure (α × ℝ) := (a.rho k).restrict G
  have hν : ν ≤ a.mu k := Measure.restrict_le_self.trans (ha.1 k).2.2.2.2.1
  have hνE : ∀ᵐ z ∂ν, ∃ e, z ∈ E e :=
    (ae_restrict_mem hGm).mono fun z hz => mem_iUnion.mp hz
  let Z := parentZoom p a k r i
  have hdet := parentChart_det p hp a k r i
  have hrecover := hcap i E hEosc ν hν hνE Z.baseMatrix Z.baseShift 1
    (hmat R hA i) hdet.1 (by simpa only [abs_one, one_mul] using hdet.2) (by norm_num)
  let m : ℝ := a.q k r * (a.nu k (a.A k r i)).toReal
  let ζ : Measure (α × ℝ) := (ENNReal.ofReal m)⁻¹ • ν
  have hRef : ENNReal.ofReal m = ENNReal.ofReal (a.q k r) * a.nu k (a.A k r i) := by
    change ENNReal.ofReal (a.q k r * (a.nu k (a.A k r i)).toReal) = _
    rw [ENNReal.ofReal_mul hq.le, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hprior : a.nu k (a.A k r i) ≠ 0 := by
    apply (lt_of_lt_of_le _ (hA.2.2.2.2.1 i).1).ne'
    exact ENNReal.ofReal_pos.mpr (by unfold width narrow; positivity)
  have hm : 0 < m := mul_pos hq (ENNReal.toReal_pos hprior (measure_ne_top _ _))
  have hRef0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.mpr hm).ne'
  refine ⟨G, hGm, hGsub, ?_, ?_⟩
  · calc a.mu k ((a.B k r i ×ˢ a.block k r i) \ G)
        ≤ a.mu k (a.parentSet k r i) *
            ENNReal.ofReal ((parentFilling (p.K k) (width p k r))⁻¹) := hEloss
      _ ≤ (ENNReal.ofReal (p.K k * a.q k r) * a.nu k (a.A k r i)) *
            ENNReal.ofReal ((parentFilling (p.K k) (width p k r))⁻¹) :=
        mul_le_mul_left (a.original_parent_mass_upper p hp ha.1 hA i) _
      _ = _ := by
        rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_mul hK0]
        ring
  · intro c j
    have hYν : ∀ᵐ z ∂ν, |rowBase Z (a.b k z.1) z.2 2| ≤ p.K k := by
      filter_upwards [ae_restrict_mem hGm] with z hz
      exact parentChart_transverse_bound p hp a hA i (hGsub hz).1 (hGsub hz).2
    have hY : ∀ᵐ z ∂ζ, |rowBase Z (a.b k z.1) z.2 2| ≤ p.K k :=
      Measure.ae_smul_measure hYν ((ENNReal.ofReal m)⁻¹)
    have hxy := horizontal_cap_of_base_cap ζ (fun z => rowBase Z (a.b k z.1) z.2)
      (fun z => ⌊a.b k z.1 3 / p.N k ^ (-t)⌋) hξ hξ1 hK
      (show 0 ≤ recoveredParentBaseConstant (p.K k) 1 by
        unfold recoveredParentBaseConstant; positivity) hY
      (a.pi k {w | ⌊w / p.N k ^ (-t)⌋ = j}) j (fun q => hrecover.2.1 q j) c
    let S : Set (α × ℝ) := {z | horizontalMesh (p.N k ^ (-t)) (rowBase Z (a.b k z.1) z.2) = c ∧
      ⌊a.b k z.1 3 / p.N k ^ (-t)⌋ = j}
    change ζ S ≤ _ at hxy
    rw [show ζ = (ENNReal.ofReal m)⁻¹ • ν from rfl, Measure.smul_apply, smul_eq_mul] at hxy
    have hdenorm : ν S ≤ ENNReal.ofReal
        (horizontalParentConstant (p.K k) * (p.N k ^ (-t)) ^ 2) *
          a.pi k {w | ⌊w / p.N k ^ (-t)⌋ = j} *
          (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r i)) := by
      rw [← hRef]
      calc ν S = ((ENNReal.ofReal m)⁻¹ * ν S) * ENNReal.ofReal m := by
            rw [mul_comm _ (ENNReal.ofReal m), ← mul_assoc,
              ENNReal.mul_inv_cancel hRef0 ENNReal.ofReal_ne_top, one_mul]
        _ ≤ _ := mul_le_mul_left hxy _
    have hle : a.rho k {z | z ∈ G ∧ hcell Z (p.N k ^ (-t)) (a.b k z.1) z.2 = c ∧
        ⌊a.b k z.1 3 / p.N k ^ (-t)⌋ = j} ≤ ν S := by
      rw [show ν = (a.rho k).restrict G from rfl, Measure.restrict_apply' hGm]
      apply measure_mono
      intro z hz
      refine ⟨⟨?_, hz.2.2⟩, hz.1⟩
      change (fun e : Fin 2 => Submission.Lib.K4AffineMeshCaps.baseMesh (p.N k ^ (-t))
        (rowBase Z (a.b k z.1) z.2) (Fin.castLE (by decide : 2 ≤ 3) e)) = c
      rw [← hcell_eq_rowBase Z hq.ne']
      exact hz.2.1
    have hresult := hle.trans hdenorm
    rw [Submission.Obl.k4_critical_conditional_row_preparation.floor_bin_eq_Ico
      (p.N k ^ (-t)) j hξ] at hresult
    exact hresult

end

end Submission.Obl.k4_narrow_projected_row_parents.NativeCaps
