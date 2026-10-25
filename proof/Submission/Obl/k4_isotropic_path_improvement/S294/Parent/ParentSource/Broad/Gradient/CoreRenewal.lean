-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.CoreRenewal, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/CoreRenewal.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/CoreRenewal.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.RowPruning
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FixedParentBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DeepPhysicalMenus

/-!
# Breadth renewal on the renewal cells of one fine core

The generic same-state renewal `PaletteFamily.exists_broad_physical_state_source` is applied to
the ORIGINAL law `(ν ⊗ dt)` restricted to a set `U` of incidences of one fine packet `b`, with
the state "renewal cell of the local core point". Velocities are measured in `b`'s own cube
frame, as in the row tests. The deep family consists of the good deep packets inside `b`;
every whole deep packet meets at most `27` renewal cells (its local diameter is below the
mesh), and their full references sum to at most `κ² ref_b`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric Native Analytic
open k4_stable_native_signal_oscillation
open scoped ENNReal

noncomputable section

/-- The fine cube velocity is the frozen normalized velocity of the same packet. -/
theorem packetCubeVelocity_eq_normalizedVelocity {W : ℕ} (p : PathData W) (b : Fin p.C)
    (x : Event) :
    (6 * p.κ)⁻¹ • p.normalizedVelocity b x = packetCubeVelocity p b x.1 := by
  ext t
  fin_cases t <;>
    simp [packetCubeVelocity, PathData.normalizedVelocity, normalizedPacketLine,
      nativeOldBaseFrame, Submission.Lib.K4ChartLifting.Frame.normTraj,
      Submission.Lib.K4ChartLifting.Frame.normCoeff, v, Native.v, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_two]

/-- Neighbouring integer codes: an anchor code plus a shift in `{-1, 0, 1}³`. -/
def codeNeighbours (c : Fin 3 → ℤ) : Finset (Fin 3 → ℤ) :=
  (Finset.univ : Finset (Fin 3 → Fin 3)).image (fun e => fun t => c t + ((e t : ℕ) : ℤ) - 1)

theorem card_codeNeighbours (c : Fin 3 → ℤ) : (codeNeighbours c).card ≤ 27 := by
  unfold codeNeighbours
  exact Finset.card_image_le.trans (by simp)

theorem mem_codeNeighbours {c d : Fin 3 → ℤ} (h : ∀ t, |d t - c t| ≤ 1) :
    d ∈ codeNeighbours c := by
  unfold codeNeighbours
  rw [Finset.mem_image]
  refine ⟨fun t => ⟨(d t - c t + 1).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
  · have h1 := abs_le.mp (h t)
    omega
  · funext t
    have h1 := abs_le.mp (h t)
    simp only
    rw [Int.toNat_of_nonneg (by omega)]
    ring

/-- Two points within the mesh in every coordinate have neighbouring renewal codes. -/
theorem renewalCellCode_near {Kc : ℝ} (hKc : 0 < Kc) (J qc : ℕ)
    {x y : EuclideanSpace ℝ (Fin 3)} (hxy : ‖x - y‖ ≤ renewalCellMesh Kc J qc) :
    renewalCellCode Kc J qc x ∈ codeNeighbours (renewalCellCode Kc J qc y) := by
  apply mem_codeNeighbours
  intro t
  have hm : 0 < renewalCellMesh Kc J qc := by unfold renewalCellMesh; positivity
  have hcoord : |x t - y t| ≤ renewalCellMesh Kc J qc := by
    have hh := PiLp.norm_apply_le (x - y) t
    simp only [PiLp.sub_apply, Real.norm_eq_abs] at hh
    exact hh.trans hxy
  obtain ⟨hlo, hhi⟩ := abs_le.mp hcoord
  have hf1 := Int.floor_le (x t / renewalCellMesh Kc J qc)
  have hf2 := Int.lt_floor_add_one (x t / renewalCellMesh Kc J qc)
  have hg1 := Int.floor_le (y t / renewalCellMesh Kc J qc)
  have hg2 := Int.lt_floor_add_one (y t / renewalCellMesh Kc J qc)
  have hdiv : |x t / renewalCellMesh Kc J qc - y t / renewalCellMesh Kc J qc| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hm, div_le_one hm]
    exact hcoord
  obtain ⟨hd1, hd2⟩ := abs_le.mp hdiv
  unfold renewalCellCode
  rw [abs_le]
  constructor
  · have : (⌊x t / renewalCellMesh Kc J qc⌋ : ℝ) - ⌊y t / renewalCellMesh Kc J qc⌋ > -2 := by
      linarith
    have h' : ⌊x t / renewalCellMesh Kc J qc⌋ - ⌊y t / renewalCellMesh Kc J qc⌋ > -2 := by
      exact_mod_cast this
    omega
  · have : (⌊x t / renewalCellMesh Kc J qc⌋ : ℝ) - ⌊y t / renewalCellMesh Kc J qc⌋ < 2 := by
      linarith
    have h' : ⌊x t / renewalCellMesh Kc J qc⌋ - ⌊y t / renewalCellMesh Kc J qc⌋ < 2 := by
      exact_mod_cast this
    omega

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {m : ℕ}
    {u : T → ℝ} {τ : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- **Renewal on the cells of one fine core.** -/
theorem exists_core_cell_renewal
    (hHbase : ∀ w, H w ⊆ Q.base w)
    (hHterminal : ∀ w, H₀ w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (hHbroad : ∀ w, H w ⊆ broad.residual w)
    (old : Fin p.C) (hold : p.lev old = i) (hactive : F.active old)
    (b : Fin p.C) {mid : ℕ} (hbmid : p.lev b = mid) (hmid : p.lev old ≤ mid)
    (hstop : mid ≤ stop) (hγ : p.γ b = p.γ old) (hbold : p.F b ⊆ p.F old)
    {K : ℝ} (hK0 : 0 ≤ K) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3))
    {Kc : ℝ} (hKc : 0 < Kc) (J qc : ℕ)
    (hdeep : ∀ deep : Fin p.C, p.lev deep = stop →
      6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ b deep ≤ renewalCellMesh Kc J qc)
    {width : ℝ} (hfraction : 0 ≤ fraction) (hwidth0 : 0 ≤ width)
    (hstrip : width * (6 * p.κ ^ 3 * d.N k ^ (2 * δ₀ * d.L)) ≤ r)
    (U : Set Event) (hUm : MeasurableSet U) (hUH : U ⊆ H (p.γ b) ∩ p.F b)
    (δref : ENNReal) (hδ0 : δref ≠ 0) (hδtop : δref ≠ ∞) :
    ∃ keep : Set Event, MeasurableSet keep ∧
      (((d.ν k (p.γ old)).prod volume).restrict U) univ ≤
        ((((d.ν k (p.γ old)).prod volume).restrict U).restrict keep) univ +
          δref * (27 * (ENNReal.ofReal (p.κ ^ 2) *
            (d.ν k (p.γ old) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)))) ∧
      ∀ (label : Fin 3 → ℤ) (n center : EuclideanSpace ℝ (Fin 2)), ‖n‖ = 1 →
        ((((d.ν k (p.γ old)).prod volume).restrict U).restrict keep)
          {x | renewalCellCode Kc J qc (packetLocalCorePoint (d.N k) (d.B k) p b K R c x) = label ∧
            |inner ℝ n (packetCubeVelocity p b x.1 - center)| ≤ width} ≤
          (δref⁻¹ * ENNReal.ofReal (8 * fraction)) *
            ((((d.ν k (p.γ old)).prod volume).restrict U).restrict keep)
              {x | renewalCellCode Kc J qc
                (packetLocalCorePoint (d.N k) (d.B k) p b K R c x) = label} := by
  classical
  let ρ := ((d.ν k (p.γ old)).prod volume).restrict U
  let Z := packetLocalCorePoint (d.N k) (d.B k) p b K R c
  have hZ : Measurable Z :=
    (((measurable_nativeBase.comp (measurable_packetNativeCubePoint (d.N k) (d.B k) p b)).sub_const
      c).const_smul (K ^ R))
  let state : Event → (Fin 3 → ℤ) := fun x => renewalCellCode Kc J qc (Z x)
  have hstate : Measurable state := (measurable_renewalCellCode Kc J qc).comp hZ
  let nodes := originalFinePackets p old stop
  let good := nodes.filter (fun deep =>
    F.coding.code deep ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction old ∧
    F.coding.code deep ∉ fineRetentionFailures (Q.coarseLaw (p.lev old) (F.code old))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U old) (ENNReal.ofReal (1 / 8 : ℝ)) ∧
    p.F deep ⊆ p.F b)
  let I := ↥good
  have hn (j : I) : p.lev j.1 = stop ∧ p.γ j.1 = p.γ old ∧ p.F j.1 ⊆ p.F old :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp j.2).1).2
  have he (j : I) := (Finset.mem_filter.mp j.2).2.1
  have hret (j : I) := (Finset.mem_filter.mp j.2).2.2.1
  have hinb (j : I) : p.F j.1 ⊆ p.F b := (Finset.mem_filter.mp j.2).2.2.2
  have hpacket (deep : Fin p.C) (hdlev : p.lev deep = stop) (hdγ : p.γ deep = p.γ old)
      {z : Event} (hz : z ∈ F.fineOriginalEvent old deep univ) : z ∈ p.F deep := by
    have hh := hz.1
    have htag : p.lev deep = stop ∧ p.γ deep = p.γ old := ⟨hdlev, hdγ⟩
    simp only [PathData.packetWitness, ite_eq_left htag] at hh
    exact hh.1.1
  have hUbase (z : Event) (hz : z ∈ U) : z ∈ Q.base (p.γ old) := by
    have hh := hHbase _ (hUH hz).1
    rwa [hγ] at hh
  have hcover : ∀ᵐ z ∂ρ, ∃ j : I, z ∈ F.fineOriginalEvent old j.1 univ := by
    filter_upwards [ae_restrict_mem hUm] with z hz
    have hzres : z ∈ broad.residual (p.γ old) ∩ p.F old := by
      refine ⟨?_, hbold (hUH hz).2⟩
      have hh := hHbroad _ (hUH hz).1
      rwa [hγ] at hh
    obtain ⟨deep, hdlev, hdγ, hdnon, hdret, hzevent⟩ :=
      broad.original_parent_fine_cover old hold z hzres
    have hzdeep := hpacket deep hdlev hdγ hzevent
    have hnode := Q.mem_original_fine_packets hp old deep stop (hmid.trans hstop) hdlev hdγ
      z (hUbase z hz) hzres.2 hzdeep
    have hdb : p.F deep ⊆ p.F b := Q.original_ancestor_of_common_incidence hp b deep
      (by omega) (hdγ.trans hγ.symm) z (by rw [hγ]; exact hUbase z hz) (hUH hz).2 hzdeep
    exact ⟨⟨deep, Finset.mem_filter.mpr ⟨hnode, hdnon, hdret, hdb⟩⟩, hzevent⟩
  let menus (j : I) : Finset (Fin 3 → ℤ) :=
    if h : (U ∩ p.F j.1).Nonempty then codeNeighbours (state h.some) else ∅
  have hcard (j : I) : (menus j).card ≤ 27 := by
    dsimp only [menus]
    split_ifs
    · exact card_codeNeighbours _
    · simp
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hmenu : ∀ᵐ z ∂ρ, ∀ j : I, z ∈ F.fineOriginalEvent old j.1 univ → state z ∈ menus j := by
    filter_upwards [ae_restrict_mem hUm] with z hz j hzevent
    have hzdeep := hpacket j.1 (hn j).1 (hn j).2.1 hzevent
    have hne : (U ∩ p.F j.1).Nonempty := ⟨z, hz, hzdeep⟩
    have hmenu_eq : menus j = codeNeighbours (state hne.some) := by
      dsimp only [menus]
      rw [dif_pos hne]
    rw [hmenu_eq]
    obtain ⟨hyU, hydeep⟩ := hne.some_mem
    have hA : p.A j.1 ⊆ p.A b := Q.original_assignment_ancestor_of_common_incidence hp b j.1
      (by rw [hbmid, (hn j).1]; exact hstop) ((hn j).2.1.trans hγ.symm) z
      (by rw [hγ]; exact hUbase z hz) (hUH hz).2 hzdeep
    have hdiam := hp.deep_original_core_diameter hN b j.1 hA hK0 R c z hzdeep hne.some hydeep
    exact renewalCellCode_near hKc J qc (hdiam.trans (hdeep j.1 (hn j).1))
  have hρ : ρ ≤ (d.ν k (p.γ old)).prod volume := Measure.restrict_le_self
  obtain ⟨keep, hkeep, hbudget, hcap⟩ := F.exists_broad_physical_state_source hd hp
    (hp.residual_subset_event H₀ hHterminal) hHterminal old b hactive (fun j : I => j.1)
    (fun j => (hn j).1) (fun j => (hn j).2.1) hfraction hwidth0 hstrip he hret ρ hρ
    state hstate menus 27 hcard hcover hmenu δref hδ0 hδtop
  have hNpos : 0 < d.N k := (by norm_num : (0 : ℝ) < 2).trans_le (hd.1 k)
  have hsum : (∑ j : I, ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
      d.ν k (p.γ j.1) (p.A j.1)) ≤ ENNReal.ofReal (p.κ ^ 2) *
        (d.ν k (p.γ old) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹)) := by
    have hh := hp.local_reference_sum_le hNpos b stop good
      (fun deep hdeep => ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hdeep).1).2.1,
        ((Finset.mem_filter.mp (Finset.mem_filter.mp hdeep).1).2.2.1).trans hγ.symm,
        (Finset.mem_filter.mp hdeep).2.2.2⟩)
    rw [← hγ]
    calc
      _ = ∑ j : I, ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
          d.ν k (p.γ b) (p.A j.1) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [(hn j).2.1, hγ]
      _ = ∑ deep ∈ good, ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) * d.ν k (p.γ b) (p.A deep) :=
        Finset.sum_coe_sort good (fun deep => ENNReal.ofReal (((2 : ℝ) ^ p.T stop)⁻¹) *
          d.ν k (p.γ b) (p.A deep))
      _ ≤ _ := hh
  refine ⟨keep, hkeep, hbudget.trans (add_le_add le_rfl ?_), ?_⟩
  · have hh := mul_le_mul' (le_refl (δref * ((27 : ℕ) : ENNReal))) hsum
    simpa only [mul_assoc, Nat.cast_ofNat] using hh
  · intro label n center hn1
    have hh := hcap label n center hn1
    have hset : {x : Event | state x = label ∧
        |inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity b x - center)| ≤ width} =
        {x | renewalCellCode Kc J qc (packetLocalCorePoint (d.N k) (d.B k) p b K R c x) = label ∧
          |inner ℝ n (packetCubeVelocity p b x.1 - center)| ≤ width} := by
      ext x
      simp only [mem_setOf_eq, packetCubeVelocity_eq_normalizedVelocity, state, Z]
    rw [hset] at hh
    exact hh

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
